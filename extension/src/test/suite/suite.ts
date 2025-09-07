import * as path from 'path';
import * as vscode from 'vscode';
import * as fs from 'fs';
import { strict as assert } from 'assert';
// runner is provided by index.ts; no direct Mocha usage here
import { exec } from 'child_process';

suite('MathEye Integration', () => {
  // repo root from out/test/suite is four levels up
  const repoRoot = path.resolve(__dirname, '../../../..');
  const tmpFile = path.join(__dirname, 'sample.lean');
  const sample = [
    'import Mathlib.Data.Nat.Basic',
    '',
    'theorem t (n : Nat) : n = n := by',
    '  rfl',
    ''
  ].join('\n');

  suiteSetup(async () => {
    fs.writeFileSync(tmpFile, sample, 'utf8');
    try {
      await vscode.workspace.getConfiguration('matheye').update('logLevel', 'debug', vscode.ConfigurationTarget.Global);
    } catch {}
  });

  test.only('Inline by rfl: admit at rfl position becomes block and compiles (real)', async () => {
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

  test('Insert Have Snippet command exists', async () => {
    const doc = await vscode.workspace.openTextDocument(tmpFile);
    const editor = await vscode.window.showTextDocument(doc);
    editor.selection = new vscode.Selection(new vscode.Position(3, 2), new vscode.Position(3, 2));
    // Just verify command is registered
    const cmds = await vscode.commands.getCommands(true);
    assert.ok(cmds.includes('matheye.insertHaveSnippet'));
  });

  async function snapshotWithMarker(doc: vscode.TextDocument, editor: vscode.TextEditor, pos: vscode.Position, outPath: string) {
    const marker = '⟦CURSOR⟧';
    // insert marker
    await editor.edit((eb) => eb.insert(pos, marker));
    try { fs.writeFileSync(outPath, doc.getText(), 'utf8'); } catch {}
    // remove marker
    await editor.edit((eb) => eb.delete(new vscode.Range(pos, new vscode.Position(pos.line, pos.character + marker.length))));
  }

  function uniqueFile(name: string): string {
    const ts = Date.now();
    return path.join(__dirname, `${name}_${ts}.lean`);
  }

  test('Admit inserts have/exact inside branch (cursor before |)', async () => {
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
    assert.ok(/\|\s*zero\s*=>\s*(by\b|\n)/.test(segment), 'header must start a block (=> by or =>\\n)');
    // Must contain exactly one have+exact pair
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.equal(haveCount, 1, 'should insert exactly one have');
    assert.ok(exactCount >= 1, 'should insert at least one exact');
    // Must not contain rfl anymore
    assert.ok(!/\brfl\b/.test(segment), 'rfl should be trimmed');
  });

  test('Admit inserts have/exact inside branch (cursor after => )', async () => {
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
    assert.ok(/\|\s*zero\s*=>\s*(by\b|\n)/.test(segment), 'header must start a block (=> by or =>\\n)');
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.equal(haveCount, 1, 'should insert exactly one have');
    assert.ok(exactCount >= 1, 'should insert at least one exact');
    assert.ok(!/\brfl\b/.test(segment), 'rfl should be trimmed');
  });

  test('Admit at => without space (cursor exactly after =>) compiles and trims rfl', async () => {
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
    assert.ok(/\|\s*zero\s*=>\s*(by\b|\n)/.test(segment), 'header must start a block (=> by or =>\\n)');
    assert.ok(!/\brfl\b/.test(segment), 'rfl should be trimmed');
    await runLakeCompile(file.replace(/\.lean$/, '.post.out.lean'));
  });

  test('Admit at => with space trims rfl and compiles', async () => {
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
    assert.ok(/\|\s*zero\s*=>\s*(by\b|\n)/.test(segment), 'header must start a block (=> by or =>\\n)');
    assert.ok(!/\brfl\b/.test(segment), 'rfl should be trimmed');
    await runLakeCompile(file.replace(/\.lean$/, '.post.out.lean'));
  });

  test('Admit with cursor at rfl trims inline and compiles', async () => {
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
    assert.ok(/\|\s*zero\s*=>\s*(by\b|\n)/.test(segment), 'header must start a block (=> by or =>\\n)');
    assert.ok(!/\brfl\b/.test(segment), 'rfl should be trimmed');
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.equal(haveCount, 1, 'should insert exactly one have');
    assert.ok(exactCount >= 1, 'should insert at least one exact');
    await runLakeCompile(file.replace(/\.lean$/, '.post.out.lean'));
  });

  test('E2E basic_theorem: cursor at rfl trims inline and compiles', async () => {
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
    if (!/\|\s*zero\s*=>\s*(by\b|\n)/.test(segment)) throw new Error('header must be block (=> by or =>\\n)');
    if (/\brfl\b/.test(segment)) throw new Error('rfl should be trimmed');
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    if (haveCount !== 1) throw new Error(`have count expected 1, got ${haveCount}`);
    if (exactCount < 1) throw new Error('exact missing');
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

  test('E2E test_01: cursor before | then admit stays in zero-branch and compiles', async () => {
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
    assert.ok(/\|\s*zero\s*=>\s*(by\b|\n)/.test(segment), 'header must start a block (=> by or =>\\n)');
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.equal(haveCount, 1, 'should insert exactly one have');
    assert.ok(exactCount >= 1, 'should insert at least one exact');
    assert.ok(!/\brfl\b/.test(segment), 'rfl should be trimmed');
    await runLakeCompile(file.replace(/\.lean$/, '.post.out.lean'));
  });

  test('E2E test_01: cursor after => space then admit stays in zero-branch and compiles', async () => {
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
    assert.ok(/\|\s*zero\s*=>\s*(by\b|\n)/.test(segment), 'header must start a block (=> by or =>\\n)');
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.equal(haveCount, 1, 'should insert exactly one have');
    assert.ok(exactCount >= 1, 'should insert at least one exact');
    assert.ok(!/\brfl\b/.test(segment), 'rfl should be trimmed');
    await runLakeCompile(file.replace(/\.lean$/, '.post.out.lean'));
  });

  test('Real: double admit on same branch remains single have/exact and compiles', async () => {
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
    assert.equal(haveCount, 1, 'should keep exactly one have after double admit');
    assert.ok(exactCount >= 1, 'should keep exact after double admit');
    await runLakeCompile(file);
  });

  test('Real: preexisting have/exact then admit trims old and compiles', async () => {
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
    assert.equal(haveCount, 1, 'should trim old have and keep exactly one');
    assert.ok(exactCount >= 1, 'should have exact present');
    await runLakeCompile(file);
  });

  test('Real: cases Bool branch inline rfl -> admit trims and compiles', async () => {
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
    assert.ok(/\|\s*false\s*=>\s*(by\b|\n)/.test(segment), 'header must be block form');
    const haveCount = (segment.match(/\bhave\b/g) || []).length;
    const exactCount = (segment.match(/\bexact\b/g) || []).length;
    assert.equal(haveCount, 1, 'should insert exactly one have');
    assert.ok(exactCount >= 1, 'should insert at least one exact');
    assert.ok(!/\brfl\b/.test(segment), 'rfl should be trimmed');
    await runLakeCompile(file);
  });

  test('Real: admit inside nested have by-block compiles', async () => {
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
    assert.ok(haveCount >= 1, 'should contain have inside nested by');
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

  test('Real: admit inside nested have (eq type with rfl) compiles', async () => {
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
    assert.ok(haveCount >= 1, 'should contain have inside nested by');
    assert.ok(exactCount >= 1, 'should contain exact inside nested by');
    await runLakeCompile(file);
  });

  test('Real Rollback: admit with history then rollback restores by-block', async () => {
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

  test('Real Rollback: user edits inserted snippet, rollback still restores by-block', async () => {
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
