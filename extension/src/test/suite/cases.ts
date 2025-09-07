import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { strict as assert } from 'assert';
import { exec } from 'child_process';

suite('MathEye Complex Containers (Real)', () => {
  const repoRoot = path.resolve(__dirname, '../../../..');
  function unique(name: string): string { return path.join(__dirname, `${name}_${Date.now()}.lean`); }
  function runLakeCompile(file: string): Promise<void> {
    return new Promise((resolve, reject) => {
      exec(`lake env lean "${file}"`, { cwd: repoRoot, timeout: 60000 }, (err, _so, se) => {
        const errMsg = (se || '').trim();
        if (!err) return resolve();
        if (errMsg && /^warning:/m.test(errMsg) && !/error:/m.test(errMsg)) return resolve();
        return reject(new Error(errMsg || err?.message));
      });
    });
  }

  async function waitLeanClientReady(timeoutMs = 4000): Promise<void> {
    const ext = vscode.extensions.getExtension('leanprover.lean4');
    await ext?.activate();
    const start = Date.now();
    while (Date.now() - start < timeoutMs) {
      try {
        const features = await (ext as any).exports.allFeatures();
        const client = features?.clientProvider?.getActiveClient?.();
        if (client) return;
      } catch {}
      await new Promise(r => setTimeout(r, 200));
    }
  }

  test('Real Complex: cases branch with nested by, admit then rollback', async () => {
    await waitLeanClientReady();
    const file = unique('match_nested_by');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem tm (b : Bool) : True := by',
      '  cases b with',
      '  | true =>',
      '    exact True.intro',
      '  | false =>',
      '    exact True.intro',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    const line = doc.getText().split(/\r?\n/).findIndex(l => /\|\s*true\s*=>/.test(l));
    const pos = new vscode.Position(line, doc.lineAt(line).text.length);
    editor.selection = new vscode.Selection(pos, pos);
    // give Lean client time to initialize
    await new Promise(r => setTimeout(r, 1500));
    await vscode.commands.executeCommand('matheye.insertHaveAdmitWithHistory');
    await new Promise(r => setTimeout(r, 800));
    try { await doc.save(); } catch {}
    await vscode.commands.executeCommand('matheye.rollbackCurrentBlock');
    await new Promise(r => setTimeout(r, 400));
    try { await doc.save(); } catch {}
    const full = doc.getText();
    assert.ok(/\bexact\s+True\.intro\b/.test(full), `rollback should restore original inner by, got: ${full.slice(0,300)}`);
    await runLakeCompile(file);
  });

  test.skip('Real Complex: calc inner by, admit then rollback', async () => {
    await waitLeanClientReady();
    const file = unique('calc_inner_by');
    const content = [
      'import Mathlib.Data.Nat.Basic',
      'import MathEye',
      'macro "human_oracle" : tactic => `(tactic| sorry)',
      '',
      'theorem tc (n : Nat) : n = n := by',
      '  calc',
      '    n = n := by rfl',
    ].join('\n');
    fs.writeFileSync(file, content, 'utf8');
    const doc = await vscode.workspace.openTextDocument(file);
    const editor = await vscode.window.showTextDocument(doc);
    const line = doc.getText().split(/\r?\n/).findIndex(l => /:=\s*by\s*rfl\s*$/.test(l));
    const pos = new vscode.Position(line, doc.lineAt(line).text.indexOf('by') + 2);
    editor.selection = new vscode.Selection(pos, pos);
    await new Promise(r => setTimeout(r, 1500));
    await vscode.commands.executeCommand('matheye.insertHaveAdmitWithHistory');
    await new Promise(r => setTimeout(r, 800));
    try { await doc.save(); } catch {}
    await vscode.commands.executeCommand('matheye.rollbackCurrentBlock');
    await new Promise(r => setTimeout(r, 400));
    try { await doc.save(); } catch {}
    const l0 = doc.lineAt(line).text;
    const l1 = (doc.lineCount > line + 1) ? doc.lineAt(line + 1).text : '';
    const l2 = (doc.lineCount > line + 2) ? doc.lineAt(line + 2).text : '';
    assert.ok(/by\s*rfl\b/.test(l0) || (/by\s*$/.test(l0) && (/(^|\s)rfl(\s|$)/.test(l1) || /(^|\s)rfl(\s|$)/.test(l2))), `rollback should restore calc inner by rfl, got: ${l0} / ${l1} / ${l2}`);
    await runLakeCompile(file);
  });
});
