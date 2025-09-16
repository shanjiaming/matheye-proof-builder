import * as path from 'path';
import * as vscode from 'vscode';
import * as fs from 'fs';
import { strict as assert } from 'assert';
// runner is provided by index.ts; no direct Mocha usage here
import { exec } from 'child_process';
import { LeanClientService } from '../../services/leanClient';

suite('MathEye Integration', () => {
  // repo root from out/test/suite is four levels up
  const repoRoot = path.resolve(__dirname, '../../../..');
  // Put all test files under repoRoot to ensure Lean picks the right Lake project/LEAN_PATH
  // 使用稳定的测试目录，避免 .it_scratch 在部分环境下的缓存/监控边角
  const scratchDir = path.join(repoRoot, 'extension', '.vscode-test', 'tmp_cases');
  try { fs.mkdirSync(scratchDir, { recursive: true }); } catch {}
  const tmpFile = path.join(scratchDir, 'sample.lean');
  const sample = [
    'import Mathlib.Data.Nat.Basic',
    '',
    'theorem t (n : Nat) : n = n := by',
    '  rfl',
    ''
  ].join('\n');

  suiteSetup(async () => {
    // 开启 Lean 端 AST 调试日志
    try { (process as any).env.MATHEYE_DEBUG_AST = '1'; } catch {}
    fs.writeFileSync(tmpFile, sample, 'utf8');
    try {
      await vscode.workspace.getConfiguration('matheye').update('logLevel', 'debug', vscode.ConfigurationTarget.Global);
      await vscode.workspace.getConfiguration('lean4').update('lakeEnabled', true, vscode.ConfigurationTarget.Global);
      await vscode.workspace.getConfiguration('lean4').update('toolchainPath', '', vscode.ConfigurationTarget.Global);
      const wrapper = path.resolve(repoRoot, 'extension', 'scripts', 'lean_server_wrapper.sh');
      await vscode.workspace.getConfiguration('lean4').update('executablePath', wrapper, vscode.ConfigurationTarget.Global);
      // 移除可能残留的“破坏性设置”，避免 lean --server + 清空 LEAN_PATH
      await vscode.workspace.getConfiguration().update('lean4.serverArgs', undefined, vscode.ConfigurationTarget.Global);
      await vscode.workspace.getConfiguration().update('lean4.serverEnv', undefined, vscode.ConfigurationTarget.Global);
      await vscode.workspace.getConfiguration().update('lean4.serverArgs', undefined, vscode.ConfigurationTarget.Workspace);
      await vscode.workspace.getConfiguration().update('lean4.serverEnv', undefined, vscode.ConfigurationTarget.Workspace);
      try { await vscode.commands.executeCommand('lean4.restartServer'); } catch {}
      await new Promise(r => setTimeout(r, 1200));
    } catch {}
  });

  test('User bug case: complex by_cases/obtain/grind — probe multiple cursors (real)', async () => {
    const file = uniqueFile('user_bug_case');
    const content = [
      'import Mathlib',
      'def IsPrime (n : Nat) := 1 < n ∧ ∀ k, 1 < k → k < n → ¬ k ∣ n',
      'theorem exists_prime_factor :∀ n, 1 < n → ∃ k, IsPrime k ∧ k ∣ n := by',
      '  intro n h1',
      '  -- Either `n` is prime...',
      '  by_cases hprime : IsPrime n',
      '  · grind [Nat.dvd_refl]',
      '  -- ... or it has a non-trivial divisor with a prime factor',
      '  · obtain ⟨k, _⟩ : ∃ k, 1 < k ∧ k < n ∧ k ∣ n := by',
      '      simp_all [IsPrime]',
      '    obtain ⟨p, _, _⟩ := exists_prime_factor k (by grind)',
      '    grind [Nat.dvd_trans]',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    const positions: Array<{ name: string; pos: vscode.Position }> = [];
    // Collect several interesting positions
    const lines = content.split(/\r?\n/);
    const find = (substr: string) => {
      const i = lines.findIndex(l => l.includes(substr));
      return { line: i, col: Math.max(0, lines[i]?.indexOf(substr) ?? 0) };
    };
    const pts = [
      find('by_cases hprime'),
      find('grind [Nat.dvd_refl]'),
      find('simp_all [IsPrime]'),
      find('exists_prime_factor k'),
      find('grind [Nat.dvd_trans]'),
    ];
    for (const p of pts) {
      if (p.line >= 0) positions.push({ name: lines[p.line].trim(), pos: new vscode.Position(p.line, p.col) });
    }
    const outDir = path.join(path.dirname(file), 'user_bug_outputs');
    try { fs.mkdirSync(outDir, { recursive: true }); } catch {}
    let idx = 0;
    for (const it of positions) {
      editor.selection = new vscode.Selection(it.pos, it.pos);
      await snapshotWithMarker(doc, editor, it.pos, path.join(outDir, `case_${idx}.pre.out.lean`));
      try { await vscode.commands.executeCommand('matheye.insertHaveAdmit'); } catch {}
      await new Promise(r => setTimeout(r, 1500));
      const txt = doc.getText();
      fs.writeFileSync(path.join(outDir, `case_${idx}.post.out.lean`), txt, 'utf8');
      // Minimal assertions: ensure we did not duplicate or keep stale trailing tactic token on same line
      // 不强制编译，只做结构性观测
      idx++;
    }
  });

  test('Real: admit after intro keeps intro and inserts have/exact', async () => {
    const file = uniqueFile('intro_keep_then_admit');
    const content = [
      'import Mathlib',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      'def IsPrime (n : Nat) := 1 < n ∧ ∀ k, 1 < k → k < n → ¬ k ∣ n',
      'theorem exists_prime_factor :∀ n, 1 < n → ∃ k, IsPrime k ∧ k ∣ n := by',
      '  intro n h1',
      '  by_cases hprime : IsPrime n',
      '  · trivial',
      '  · admit',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    await ensureRpcReady(doc, new vscode.Position(5, 2));
    const introLine = 5; // 0-based
    const introCol = doc.lineAt(introLine).text.length; // 放在该行末尾，模拟“光标在 intro 后面”
    const pos = new vscode.Position(introLine, introCol);
    editor.selection = new vscode.Selection(pos, pos);
    await snapshotWithMarker(doc, editor, pos, file.replace(/\.lean$/, '.pre.out.lean'));
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1400));
    const text = doc.getText();
    fs.writeFileSync(file.replace(/\.lean$/, '.post.out.lean'), text, 'utf8');
    // 应保留 intro 行
    const hasIntro = /\bintro\s+n\s+h1\b/.test(text);
    if (!hasIntro) throw new Error('intro n h1 应被保留');
    // 应插入 have / exact
    const hasHave = /\bhave\b/.test(text);
    const hasExact = /\bexact\b/.test(text);
    if (!hasHave || !hasExact) throw new Error('应插入 have/exact');
  });

  test('Inline by rfl: admit at rfl position becomes block and compiles (real)', async () => {
    const file = uniqueFile('inline_by_rfl_admit');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem have_exact_simple (n : Nat) : n = n := by rfl',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    await checkDiagnostics(doc, 'import MathEye');
    // 先重启，再等 elaboration，清理 out-of-date，并做 BUILD_TAG 自检
    try { await vscode.commands.executeCommand('lean4.restartServer'); } catch {}
    await new Promise(r => setTimeout(r, 2000));
    try { await vscode.commands.executeCommand('lean4.restartFile'); } catch {}
    await waitImportsUpToDate(doc, 10000);
    // 主动触发一次 goal 请求
    try { const svc = new LeanClientService(); await svc.getProofGoals(new vscode.Position(4, 2), doc); } catch {}
    await ensureRpcReady(doc, new vscode.Position(0, 0));
    const line = 4;
    const col = doc.lineAt(line).text.indexOf('rfl');
    const pos = new vscode.Position(line, Math.max(col - 1, 0));
    editor.selection = new vscode.Selection(pos, pos);
    await snapshotWithMarker(doc, editor, pos, file.replace(/\.lean$/, '.pre.out.lean'));
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1200));
    const postPath = file.replace(/\.lean$/, '.post.out.lean');
    fs.writeFileSync(postPath, doc.getText(), 'utf8');
    const txt = doc.getText();
    // DEBUG: Log actual output for analysis
    console.log('DEBUG: Actual output after insertHaveAdmit:');
    console.log('=' + '='.repeat(50));
    console.log(txt);
    console.log('=' + '='.repeat(50));
    console.log('Contains \":= by\":', /:=\s*by\b/.test(txt));
    console.log('Contains \"rfl\":', /\brfl\b/.test(txt));
    // Expect `:= by` and no rfl
    if (!/\:=\s*by\b/.test(txt)) throw new Error('header should contain ":= by"');
    if (/\brfl\b/.test(txt)) throw new Error('rfl should be trimmed');
    await runLakeCompile(postPath);
  });

  test('Inline by rfl: deny at rfl position becomes block and compiles (real)', async () => {
    const file = uniqueFile('inline_by_rfl_deny');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem have_exact_simple2 (n : Nat) : n = n := by rfl',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    await checkDiagnostics(doc, 'import MathEye');
    await ensureRpcReady(doc, new vscode.Position(0, 0));
    try { await vscode.commands.executeCommand('lean4.restartServer'); } catch {}
    await new Promise(r => setTimeout(r, 2000));
    const line = 4;
    const col = doc.lineAt(line).text.indexOf('rfl');
    const pos = new vscode.Position(line, Math.max(col - 1, 0));
    editor.selection = new vscode.Selection(pos, pos);
    await snapshotWithMarker(doc, editor, pos, file.replace(/\.lean$/, '.pre.out.lean'));
    await vscode.commands.executeCommand('matheye.insertHaveDeny');
    await new Promise(r => setTimeout(r, 1200));
    const postPath = file.replace(/\.lean$/, '.post.out.lean');
    fs.writeFileSync(postPath, doc.getText(), 'utf8');
    const txt = doc.getText();
    if (!/\:=\s*by\b/.test(txt)) throw new Error('header should contain ":= by"');
    if (/\brfl\b/.test(txt)) throw new Error('rfl should be trimmed');
    // deny 不要求 exact
    await runLakeCompile(postPath);
  });

  suiteTeardown(async () => {
    try { fs.unlinkSync(tmpFile); } catch {}
  });

  test('Insert Have command exists', async () => {
    const doc = await vscode.workspace.openTextDocument(tmpFile);
    const editor = await vscode.window.showTextDocument(doc);
    editor.selection = new vscode.Selection(new vscode.Position(3, 2), new vscode.Position(3, 2));
    // Just verify command is registered
    const cmds = await vscode.commands.getCommands(true);
    assert.ok(cmds.includes('matheye.insertHaveAdmit'));
  });

  async function snapshotWithMarker(doc: vscode.TextDocument, editor: vscode.TextEditor, pos: vscode.Position, outPath: string) {
    const marker = '⟦CURSOR⟧';
    const text = doc.getText();
    const lines = text.split('\n');
    const lineText = lines[pos.line] || '';
    const before = lineText.slice(0, pos.character);
    const after = lineText.slice(pos.character);
    lines[pos.line] = before + marker + after;
    const markedText = lines.join('\n');
    try { fs.writeFileSync(outPath, markedText, 'utf8'); } catch {}
  }

  function uniqueFile(name: string): string {
    const ts = Date.now();
    try { fs.mkdirSync(scratchDir, { recursive: true }); } catch {}
    return path.join(scratchDir, `${name}_${ts}.lean`);
  }

  async function ensureRpcReady(doc: vscode.TextDocument, pos: vscode.Position) {
    const svc = new LeanClientService();
    // 单次构建，避免反复循环：先把依赖构建好
    try { await runLake(['update']); } catch {}
    try { await runLake(['build']); } catch {}
    // 预热文件（仅一次）：import MathEye + by 块
    try {
      const prewarmPath = path.join(scratchDir, `__prewarm_${Date.now()}.lean`);
      const prewarmContent = [
        'import MathEye',
        '',
        'theorem _warm : True := by',
        '  rfl',
        ''
      ].join('\n');
      fs.writeFileSync(prewarmPath, prewarmContent, 'utf8');
      const warmDoc = await vscode.workspace.openTextDocument(prewarmPath);
      await vscode.window.showTextDocument(warmDoc, { preview: true });
      try { await vscode.commands.executeCommand('lean4.restartFile'); } catch {}
      await new Promise(r => setTimeout(r, 1500));
      // 直接在 by 内探测一次 BUILD_TAG
      try {
        const res0: any = await svc.getByBlockRange(new vscode.Position(3, 2), warmDoc);
        if (res0 && res0.buildTag === 'NO_PROBE_VER_1') {
          await vscode.window.showTextDocument(doc, { preview: false });
        }
      } catch {}
      await vscode.window.showTextDocument(doc, { preview: false });
    } catch {}
    // 对目标文件：一次 Restart File，然后立即探测 BUILD_TAG
    try { await vscode.commands.executeCommand('lean4.restartFile'); } catch {}
    await new Promise(r => setTimeout(r, 1200));
    try {
      const res: any = await svc.getByBlockRange(pos, doc);
      if (res && res.buildTag === 'NO_PROBE_VER_1') return;
    } catch {}
    // 显式失败并输出诊断，避免无限重启
    const diags = vscode.languages.getDiagnostics(doc.uri).map(d => d.message).join('\n');
    throw new Error('Lean RPC not ready (single-attempt): buildTag not observed. Diagnostics: ' + diags);
  }

  async function checkDiagnostics(doc: vscode.TextDocument, expectImport: string) {
    // wait briefly for initial diagnostics
    await new Promise(r => setTimeout(r, 500));
    const diags = vscode.languages.getDiagnostics(doc.uri);
    const msg = diags.map(d => d.message).join('\n');
    const bad = /unknown import|unknown module|not found/i.test(msg);
    if (bad) {
      throw new Error('Import/diagnostics error before RPC: ' + msg);
    }
  }

  function runLake(args: string[]): Promise<void> {
    return new Promise((resolve, reject) => {
      exec(`lake ${args.join(' ')}`, { cwd: repoRoot, timeout: 120000 }, (err, so, se) => {
        if (err) return reject(err);
        resolve();
      });
    });
  }

  async function waitImportsUpToDate(doc: vscode.TextDocument, timeoutMs = 8000) {
    const start = Date.now();
    while (Date.now() - start < timeoutMs) {
      const diags = vscode.languages.getDiagnostics(doc.uri);
      const msg = diags.map(d => d.message).join('\n');
      if (!/Imports are out of date/i.test(msg)) return;
      try { await vscode.commands.executeCommand('lean4.restartFile'); } catch {}
      await new Promise(r => setTimeout(r, 800));
    }
  }

  test.skip('Admit inserts have/exact inside branch (cursor before |)', async () => {
    const file = uniqueFile('branch_before_pipe');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem add_zero (n : Nat) : n + 0 = n := by',
      '  induction n with',
      '  | zero => rfl',
      '  | succ k ih => rw [Nat.add_succ, ih]',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    // Place cursor before the leading '|'
    const lineIdx = 6; // 0-based, line: '  | zero => rfl'
    const col = 2; // before '|'
    editor.selection = new vscode.Selection(new vscode.Position(lineIdx, col), new vscode.Position(lineIdx, col));
    // snapshot pre with marker
    await snapshotWithMarker(doc, editor, editor.selection.active, file.replace(/\.lean$/, '.pre.out.lean'));
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    try { fs.writeFileSync(file.replace(/\.lean$/, '.post.out.lean'), doc.getText(), 'utf8'); } catch {}
    const text = doc.getText();
    const zeroIdx = text.indexOf('| zero');
    const succIdx = text.indexOf('| succ');
    const segment = text.slice(zeroIdx, succIdx > 0 ? succIdx : undefined);
    try { fs.writeFileSync(file.replace(/\.lean$/, '.debug.txt'), segment, 'utf8'); } catch {}
    // Must turn into a block with by on header
    const haveCount0 = (segment.match(/\bhave\b/g) || []).length;
    const exactCount0 = (segment.match(/\bexact\b/g) || []).length;
    assert.ok(haveCount0 >= 1, 'should insert have in branch');
    assert.ok(exactCount0 >= 1, 'should insert exact in branch');
    // Must contain exactly one have+exact pair
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.equal(haveCount, 1, 'should insert exactly one have');
    assert.ok(exactCount >= 1, 'should insert at least one exact');
    // Must not contain rfl anymore
    assert.ok(!/\brfl\b/.test(segment), 'rfl should be trimmed');
  });

  test.skip('Admit inserts have/exact inside branch (cursor after => )', async () => {
    const file = uniqueFile('branch_after_arrow');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem add_zero2 (n : Nat) : n + 0 = n := by',
      '  induction n with',
      '  | zero => rfl',
      '  | succ k ih => rw [Nat.add_succ, ih]',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    // Place cursor after the '=> '
    const lineIdx = 6; // '  | zero => rfl'
    const arrowCol = doc.lineAt(lineIdx).text.indexOf('=>') + 3; // after space
    editor.selection = new vscode.Selection(new vscode.Position(lineIdx, arrowCol), new vscode.Position(lineIdx, arrowCol));
    await snapshotWithMarker(doc, editor, editor.selection.active, file.replace(/\.lean$/, '.pre.out.lean'));
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    try { fs.writeFileSync(file.replace(/\.lean$/, '.post.out.lean'), doc.getText(), 'utf8'); } catch {}
    const text = doc.getText();
    const zeroIdx = text.indexOf('| zero');
    const succIdx = text.indexOf('| succ');
    const segment = text.slice(zeroIdx, succIdx > 0 ? succIdx : undefined);
    try { fs.writeFileSync(file.replace(/\.lean$/, '.debug.txt'), segment, 'utf8'); } catch {}
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.ok(haveCount >= 1, 'should insert have in branch');
    assert.ok(exactCount >= 1, 'should insert exact in branch');
    assert.ok(!/\brfl\b/.test(segment), 'rfl should be trimmed');
  });

  test.skip('Admit at => without space (cursor exactly after =>) compiles and trims rfl', async () => {
    const file = uniqueFile('branch_after_arrow_nospace');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem add_zero3 (n : Nat) : n + 0 = n := by',
      '  induction n with',
      '  | zero =>rfl',
      '  | succ k ih => rw [Nat.add_succ, ih]',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    // Place cursor exactly after '=>'
    const lineIdx = 6;
    const arrowCol = doc.lineAt(lineIdx).text.indexOf('=>') + 2; // no space
    const pos = new vscode.Position(lineIdx, arrowCol);
    editor.selection = new vscode.Selection(pos, pos);
    await snapshotWithMarker(doc, editor, pos, file.replace(/\.lean$/, '.pre.out.lean'));
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    fs.writeFileSync(file.replace(/\.lean$/, '.post.out.lean'), doc.getText(), 'utf8');
    const text = doc.getText();
    const zeroIdx = text.indexOf('| zero');
    const succIdx = text.indexOf('| succ');
    const segment = text.slice(zeroIdx, succIdx > 0 ? succIdx : undefined);
    // Header becomes => by; rfl trimmed
    const haveCount2 = (segment.match(/\bhave\b/g) || []).length;
    const exactCount2 = (segment.match(/\bexact\b/g) || []).length;
    assert.ok(haveCount2 >= 1, 'should insert have in branch');
    assert.ok(exactCount2 >= 1, 'should insert exact in branch');
    await runLakeCompile(file.replace(/\.lean$/, '.post.out.lean'));
  });

  test.skip('Admit at => with space trims rfl and compiles', async () => {
    const file = uniqueFile('branch_after_arrow_space');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem add_zero4 (n : Nat) : n + 0 = n := by',
      '  induction n with',
      '  | zero => rfl',
      '  | succ k ih => rw [Nat.add_succ, ih]',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    const lineIdx = 6;
    const arrowCol = doc.lineAt(lineIdx).text.indexOf('=>') + 3; // after space
    const pos = new vscode.Position(lineIdx, arrowCol);
    editor.selection = new vscode.Selection(pos, pos);
    await snapshotWithMarker(doc, editor, pos, file.replace(/\.lean$/, '.pre.out.lean'));
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    fs.writeFileSync(file.replace(/\.lean$/, '.post.out.lean'), doc.getText(), 'utf8');
    const text = doc.getText();
    const zeroIdx = text.indexOf('| zero');
    const succIdx = text.indexOf('| succ');
    const segment = text.slice(zeroIdx, succIdx > 0 ? succIdx : undefined);
    const haveCount3 = (segment.match(/\bhave\b/g) || []).length;
    const exactCount3 = (segment.match(/\bexact\b/g) || []).length;
    assert.ok(haveCount3 >= 1, 'should insert have in branch');
    assert.ok(exactCount3 >= 1, 'should insert exact in branch');
    await runLakeCompile(file.replace(/\.lean$/, '.post.out.lean'));
  });

  test.skip('Admit with cursor at rfl trims inline and compiles', async () => {
    const file = uniqueFile('branch_cursor_at_rfl');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem add_zero5 (n : Nat) : n + 0 = n := by',
      '  induction n with',
      '  | zero => rfl',
      '  | succ k ih => rw [Nat.add_succ, ih]',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    const lineIdx = 6;
    const rflCol = doc.lineAt(lineIdx).text.indexOf('rfl');
    const pos = new vscode.Position(lineIdx, rflCol);
    editor.selection = new vscode.Selection(pos, pos);
    await snapshotWithMarker(doc, editor, pos, file.replace(/\.lean$/, '.pre.out.lean'));
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    fs.writeFileSync(file.replace(/\.lean$/, '.post.out.lean'), doc.getText(), 'utf8');
    const text = doc.getText();
    const zeroIdx = text.indexOf('| zero');
    const succIdx = text.indexOf('| succ');
    const segment = text.slice(zeroIdx, succIdx > 0 ? succIdx : undefined);
    const haveCount4a = (segment.match(/\bhave\b/g) || []).length;
    const exactCount4a = (segment.match(/\bexact\b/g) || []).length;
    assert.ok(haveCount4a >= 1, 'should insert have in branch');
    assert.ok(exactCount4a >= 1, 'should insert exact in branch');
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.equal(haveCount, 1, 'should insert exactly one have');
    assert.ok(exactCount >= 1, 'should insert at least one exact');
    await runLakeCompile(file.replace(/\.lean$/, '.post.out.lean'));
  });

  test.skip('E2E basic_theorem: cursor at rfl trims inline and compiles', async () => {
    const file = uniqueFile('basic_theorem_inline_rfl');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem t0 (n : Nat) : n = n := by',
      '  induction n with',
      '  | zero => rfl',
      '  | succ k ih => exact rfl',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    const targetLine = doc.getText().split(/\r?\n/).findIndex(l => /\|\s*zero\s*=>\s*rfl\b/.test(l));
    if (targetLine < 0) throw new Error('zero-branch not found');
    const rflCol = doc.lineAt(targetLine).text.indexOf('rfl');
    const pos = new vscode.Position(targetLine, rflCol);
    editor.selection = new vscode.Selection(pos, pos);
    await snapshotWithMarker(doc, editor, pos, file.replace(/\.lean$/, '.pre.out.lean'));
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    try { fs.writeFileSync(file.replace(/\.lean$/, '.post.out.lean'), doc.getText(), 'utf8'); } catch {}
    const text = doc.getText();
    const zeroIdx = text.indexOf('| zero');
    const succIdx = text.indexOf('| succ');
    const segment = text.slice(zeroIdx, succIdx > 0 ? succIdx : undefined);
    const haveCount4 = (segment.match(/\bhave\b/g) || []).length;
    const exactCount4 = (segment.match(/\bexact\b/g) || []).length;
    if (haveCount4 < 1) throw new Error(`have not inserted`);
    if (exactCount4 < 1) throw new Error('exact missing');
    await runLakeCompile(file.replace(/\.lean$/, '.post.out.lean'));
  });

  // Helpers for real test_cases
  function copyCase(basename: string): string {
    const src = path.join(repoRoot, 'test_cases', basename);
    const dst = path.join(__dirname, `tmp_${basename}`);
    fs.copyFileSync(src, dst);
    return dst;
  }

  function runLakeCompile(file: string): Promise<void> {
    return new Promise((resolve, reject) => {
      exec(`lake env lean "${file}"`, { cwd: repoRoot, timeout: 60000 }, (err, stdout, stderr) => {
        const errMsg = (stderr || '').trim();
        if (!err) return resolve();
        // Treat warnings as non-fatal in CI/test host
        if (errMsg && /^warning:/m.test(errMsg) && !/error:/m.test(errMsg)) return resolve();
        return reject(new Error(errMsg || err.message));
      });
    });
  }

  test.skip('E2E test_01: cursor before | then admit stays in zero-branch and compiles', async () => {
    const file = uniqueFile('tmp_test_01_basic_theorem');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem t01 (n : Nat) : n = n := by',
      '  induction n with',
      '  | zero => rfl',
      '  | succ k ih => exact rfl',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    const lines = doc.getText().split(/\r?\n/);
    const targetLine = lines.findIndex(l => /\|\s+zero\s+=>/.test(l));
    assert.ok(targetLine >= 0, 'zero-branch not found');
    const col = doc.lineAt(targetLine).text.indexOf('|');
    const pos = new vscode.Position(targetLine, col);
    editor.selection = new vscode.Selection(pos, pos);
    await snapshotWithMarker(doc, editor, pos, file.replace(/\.lean$/, '.pre.out.lean'));
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    try { fs.writeFileSync(file.replace(/\.lean$/, '.post.out.lean'), doc.getText(), 'utf8'); } catch {}
    const text = doc.getText();
    const zeroIdx = text.indexOf('| zero');
    const succIdx = text.indexOf('| succ');
    const segment = text.slice(zeroIdx, succIdx > 0 ? succIdx : undefined);
    try { fs.writeFileSync(file.replace(/\.lean$/, '.debug.txt'), segment, 'utf8'); } catch {}
    const haveCount5 = (segment.match(/\bhave\b/g) || []).length;
    const exactCount5 = (segment.match(/\bexact\b/g) || []).length;
    assert.ok(haveCount5 >= 1, 'should insert have in branch');
    assert.ok(exactCount5 >= 1, 'should insert exact in branch');
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.equal(haveCount, 1, 'should insert exactly one have');
    assert.ok(exactCount >= 1, 'should insert at least one exact');
    assert.ok(!/\brfl\b/.test(segment), 'rfl should be trimmed');
    await runLakeCompile(file.replace(/\.lean$/, '.post.out.lean'));
  });

  test.skip('E2E test_01: cursor after => space then admit stays in zero-branch and compiles', async () => {
    const file = uniqueFile('tmp_test_01_basic_theorem');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem t01b (n : Nat) : n = n := by',
      '  induction n with',
      '  | zero => rfl',
      '  | succ k ih => exact rfl',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    const targetLine = doc.getText().split(/\r?\n/).findIndex(l => /\|\s+zero\s+=>/.test(l));
    assert.ok(targetLine >= 0, 'zero-branch not found');
    // 放到 '=>' 后一个字符（兼容换行块形态）
    const arrowCol = doc.lineAt(targetLine).text.indexOf('=>') + 2;
    const pos = new vscode.Position(targetLine, arrowCol);
    editor.selection = new vscode.Selection(pos, pos);
    await snapshotWithMarker(doc, editor, pos, file.replace(/\.lean$/, '.pre.out.lean'));
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    try { fs.writeFileSync(file.replace(/\.lean$/, '.post.out.lean'), doc.getText(), 'utf8'); } catch {}
    const text = doc.getText();
    const zeroIdx = text.indexOf('| zero');
    const succIdx = text.indexOf('| succ');
    const segment = text.slice(zeroIdx, succIdx > 0 ? succIdx : undefined);
    try { fs.writeFileSync(file.replace(/\.lean$/, '.debug.txt'), segment, 'utf8'); } catch {}
    const haveCount6 = (segment.match(/\bhave\b/g) || []).length;
    const exactCount6 = (segment.match(/\bexact\b/g) || []).length;
    assert.ok(haveCount6 >= 1, 'should insert have in branch');
    assert.ok(exactCount6 >= 1, 'should insert exact in branch');
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.equal(haveCount, 1, 'should insert exactly one have');
    assert.ok(exactCount >= 1, 'should insert at least one exact');
    assert.ok(!/\brfl\b/.test(segment), 'rfl should be trimmed');
    await runLakeCompile(file.replace(/\.lean$/, '.post.out.lean'));
  });

  test.skip('Real: double admit on same branch remains single have/exact and compiles', async () => {
    const file = uniqueFile('double_admit_same_branch');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem t1 (n : Nat) : n = n := by',
      '  induction n with',
      '  | zero => rfl',
      '  | succ k ih => exact rfl',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    const lineIdx = doc.getText().split(/\r?\n/).findIndex(l => /\|\s+zero\s+=>/.test(l));
    const pos = new vscode.Position(lineIdx, doc.lineAt(lineIdx).text.indexOf('=>') + 2);
    editor.selection = new vscode.Selection(pos, pos);
    // first admit
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    // second admit
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    const text = doc.getText();
    const zeroIdx = text.indexOf('| zero');
    const succIdx = text.indexOf('| succ');
    const segment = text.slice(zeroIdx, succIdx > 0 ? succIdx : undefined);
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.ok(haveCount >= 1, 'should insert have after double admit');
    assert.ok(exactCount >= 1, 'should keep exact after double admit');
    await runLakeCompile(file);
  });

  test.skip('Real: preexisting have/exact then admit trims old and compiles', async () => {
    const file = uniqueFile('admit_over_existing_have');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem t2 (n : Nat) : n = n := by',
      '  induction n with',
      '  | zero =>',
      '    have h0 : 0 = 0 := by human_oracle',
      '    exact h0',
      '  | succ k ih => exact rfl',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    const lineIdx = doc.getText().split(/\r?\n/).findIndex(l => /\|\s+zero\s*=>/.test(l));
    const pos = new vscode.Position(lineIdx, doc.lineAt(lineIdx).text.indexOf('=>') + 2);
    editor.selection = new vscode.Selection(pos, pos);
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    const text = doc.getText();
    const zeroIdx = text.indexOf('| zero');
    const succIdx = text.indexOf('| succ');
    const segment = text.slice(zeroIdx, succIdx > 0 ? succIdx : undefined);
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.ok(haveCount >= 1, 'should still contain have after admit');
    assert.ok(exactCount >= 1, 'should have exact present');
    await runLakeCompile(file);
  });

  test.skip('Real: cases Bool branch inline rfl -> admit trims and compiles', async () => {
    const file = uniqueFile('cases_bool_branch');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem tb (b : Bool) : b = b := by',
      '  cases b with',
      '  | false => rfl',
      '  | true => rfl',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    const lineIdx = doc.getText().split(/\r?\n/).findIndex(l => /\|\s*false\s*=>/.test(l));
    const pos = new vscode.Position(lineIdx, doc.lineAt(lineIdx).text.indexOf('=>') + 2);
    editor.selection = new vscode.Selection(pos, pos);
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    const text = doc.getText();
    const falseIdx = text.indexOf('| false');
    const trueIdx = text.indexOf('| true');
    const segment = text.slice(falseIdx, trueIdx > 0 ? trueIdx : undefined);
    const haveCount7 = (segment.match(/\bhave\b/g) || []).length;
    assert.ok(haveCount7 >= 1, 'should insert have in branch');
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.equal(haveCount, 1, 'should insert exactly one have');
    assert.ok(exactCount >= 1, 'should insert at least one exact');
    assert.ok(!/\brfl\b/.test(segment), 'rfl should be trimmed');
    await runLakeCompile(file);
  });

  test.skip('Real: admit inside nested have by-block compiles', async () => {
    const file = uniqueFile('nested_have_by');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem tn (n : Nat) : True := by',
      '  have h : True := by',
      '    exact True.intro',
      '  exact True.intro',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    const lineIdx = doc.getText().split(/\r?\n/).findIndex(l => /have\s+h\s*:\s*True\s*:=\s*by\s*$/.test(l));
    const pos = new vscode.Position(lineIdx, doc.lineAt(lineIdx).text.length);
    editor.selection = new vscode.Selection(pos, pos);
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    const fullText = doc.getText();
    try { fs.writeFileSync(file.replace(/\.lean$/, '.post.out.lean'), fullText, 'utf8'); } catch {}
    const all = fullText.split(/\r?\n/);
    const hdrIdx = all.findIndex(l => /have\s+h\s*:\s*True\s*:=\s*by\s*$/.test(l));
    const baseIndent = hdrIdx >= 0 ? all[hdrIdx].match(/^(\s*)/)![1].length : 0;
    let j = hdrIdx + 1;
    const bodyLines: string[] = [];
    while (j < all.length) {
      const line = all[j];
      const indent = (line.match(/^(\s*)/)![1] || '').length;
      if (indent <= baseIndent) break;
      bodyLines.push(line);
      j++;
    }
    const segment = bodyLines.join('\n');
    try { fs.writeFileSync(file.replace(/\.lean$/, '.debug.txt'), segment, 'utf8'); } catch {}
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.ok(haveCount >= 1, 'should insert have');
    assert.ok(exactCount >= 1, 'should contain exact inside nested by');
    await runLakeCompile(file);
  });

  test('Real: admit at exact line (seam-safe insertion) compiles', async () => {
    const file = uniqueFile('admit_at_exact_line');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      '/-- Using have and exact for simple steps -/',
      'theorem have_exact_simple (n : Nat) : n = n := by',
      '  have h : n = n := rfl',
      '  exact h',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    // place cursor at start of `exact h` line
    const lineIdx = doc.getText().split(/\r?\n/).findIndex(l => /^\s*exact\s+h\s*$/.test(l));
    const pos = new vscode.Position(lineIdx, doc.lineAt(lineIdx).firstNonWhitespaceCharacterIndex);
    editor.selection = new vscode.Selection(pos, pos);
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    const text = doc.getText();
    // Ensure have/exact present at least once in the block
    const segStart = text.indexOf('theorem have_exact_simple');
    const segment = text.slice(segStart);
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.ok(haveCount >= 1, 'should contain have');
    assert.ok(exactCount >= 1, 'should contain exact');
    await runLakeCompile(file);
  });

  test.skip('Real: admit inside nested have (eq type with rfl) compiles', async () => {
    const file = uniqueFile('nested_have_eq_rfl');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem have_exact_simple (n : Nat) : n = n := by',
      '  have h : n = n := by',
      '    rfl',
      '  exact rfl',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    // place cursor at end of the `have ... := by` header line to simulate seam
    const headerIdx = doc.getText().split(/\r?\n/).findIndex(l => /have\s+h\s*:\s*n\s*=\s*n\s*:=\s*by\s*$/.test(l));
    const pos = new vscode.Position(headerIdx, doc.lineAt(headerIdx).text.length);
    editor.selection = new vscode.Selection(pos, pos);
    await vscode.commands.executeCommand('matheye.insertHaveAdmit');
    await new Promise(r => setTimeout(r, 1000));
    const text = doc.getText();
    // Find nested by body and ensure have/exact appear
    const lines = text.split(/\r?\n/);
    const baseIndent = lines[headerIdx].match(/^(\s*)/)![1].length;
    const bodyLines: string[] = [];
    for (let i = headerIdx + 1; i < lines.length; i++) {
      const ind = (lines[i].match(/^(\s*)/)![1] || '').length;
      if (ind <= baseIndent) break;
      bodyLines.push(lines[i]);
    }
    const segment = bodyLines.join('\n');
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.ok(haveCount >= 1, 'should insert have');
    assert.ok(exactCount >= 1, 'should contain exact inside nested by');
    await runLakeCompile(file);
  });

  test.skip('Real Rollback: admit with history then rollback restores by-block', async () => {
    const file = uniqueFile('rollback_restore');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem tr (n : Nat) : n = n := by',
      '  rfl',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    // Find by line
    const byLine = doc.getText().split(/\r?\n/).findIndex(l => /:\s*n\s*=\s*n\s*:=\s*by$/.test(l));
    // Insert with history
    editor.selection = new vscode.Selection(new vscode.Position(byLine + 1, 2), new vscode.Position(byLine + 1, 2));
    await vscode.commands.executeCommand('matheye.insertHaveAdmitWithHistory');
    await new Promise(r => setTimeout(r, 1000));
    // Rollback
    await vscode.commands.executeCommand('matheye.rollbackCurrentBlock');
    await new Promise(r => setTimeout(r, 500));
    const after = doc.getText().split(/\r?\n/).slice(byLine, byLine + 3).join('\n');
    assert.ok(/\brfl\b/.test(after), 'should restore original rfl');
  });

  test.skip('Real Rollback: user edits inserted snippet, rollback still restores by-block', async () => {
    const file = uniqueFile('rollback_fallback');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem tr2 (n : Nat) : n = n := by',
      '  rfl',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    const byLine = doc.getText().split(/\r?\n/).findIndex(l => /:\s*n\s*=\s*n\s*:=\s*by$/.test(l));
    editor.selection = new vscode.Selection(new vscode.Position(byLine + 1, 2), new vscode.Position(byLine + 1, 2));
    await vscode.commands.executeCommand('matheye.insertHaveAdmitWithHistory');
    await new Promise(r => setTimeout(r, 1000));
    // user edits inserted snippet
    await editor.edit(eb => eb.insert(new vscode.Position(byLine + 1, 2), '-- user edit\n  '));
    await new Promise(r => setTimeout(r, 200));
    // rollback should fallback to by-block restore
    await vscode.commands.executeCommand('matheye.rollbackCurrentBlock');
    await new Promise(r => setTimeout(r, 500));
    const afterAll = doc.getText().split(/\r?\n/).slice(byLine, byLine + 3).join('\n');
    assert.ok(/\brfl\b/.test(afterAll), 'should restore original by-block even after edits');
  });
});

// No run() here; index.ts loads this file
