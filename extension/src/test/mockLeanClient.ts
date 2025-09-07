import * as vscode from 'vscode';
import { MathEyeRpcOutputParams } from '../types';

export class MockLeanClientService {
  async getProofGoals(position: vscode.Position, document: vscode.TextDocument): Promise<MathEyeRpcOutputParams> {
    return { goals: [{ type: '⊢ True' } as any], version: 0 };
  }

  async isLeanServerReady(): Promise<boolean> { return true; }

  async insertHaveByAction(position: vscode.Position, document: vscode.TextDocument, action: 'admit'|'deny'):
    Promise<{ success: boolean; newText?: string; range?: vscode.Range; errorMsg?: string }>{
    try { require('fs').appendFileSync(require('path').resolve(__dirname, './mock_calls.log'), `insertHaveByAction ${document.uri} @ ${position.line}:${position.character} ${action}\n`); } catch {}
    // crude by-block/branch container finder for tests: find current branch segment
    const text = document.getText();
    const lines = text.split(/\r?\n/);
    let startLine = position.line;
    // Find enclosing branch start (line that starts with two spaces then '|')
    for (let i = position.line; i >= 0; i--) {
      if (/^\s*\|\s+\w+\s*=>/.test(lines[i]) || /^\s*by\b/.test(lines[i])) { startLine = i; break; }
    }
    // End at next branch or end of by-block
    let endLine = lines.length - 1;
    for (let i = startLine + 1; i < lines.length; i++) {
      if (/^\s*\|\s+\w+\s*=>/.test(lines[i])) { endLine = i; break; }
      if (/^\S/.test(lines[i]) && !/^\s/.test(lines[i])) { endLine = i; break; }
    }
    const range = new vscode.Range(new vscode.Position(startLine, 0), new vscode.Position(endLine, 0));
    // Build block form for the current branch line
    const line = lines[startLine];
    const mm = line.match(/^(\s*\|\s*\w+\s*=>)(.*)$/);
    const have = `have h_${position.line}_${position.character} : 0 = 0 := by human_oracle`;
    const exact = `exact h_${position.line}_${position.character}`;
    if (mm) {
      const head = mm[1];
      // Body indent = leading indent of branch + two spaces
      const lead = (line.match(/^(\s*)\|/) || ['', ''])[1];
      const indent = lead + '  ';
      const newLines: string[] = [];
      // Normalize to a block form (no 'by' at header), drop the tail tactic
      newLines.push(`${head}`);
      newLines.push(`${indent}${have}`);
      newLines.push(`${indent}${exact}`);
      const updated = [
        ...lines.slice(0, startLine),
        ...newLines,
        ...lines.slice(startLine + 1)
      ].join('\n');
      return { success: true, newText: updated, range: new vscode.Range(new vscode.Position(0,0), document.lineAt(document.lineCount-1).range.end) };
    } else {
      // Already in block: append have/exact inside the selected range
      const seg = text.slice(document.offsetAt(range.start), document.offsetAt(range.end));
      const newSeg = seg.replace(/\s*$/, `\n  ${have}\n  ${exact}`);
      const newText = text.slice(0, document.offsetAt(range.start)) + newSeg + text.slice(document.offsetAt(range.end));
      return { success: true, newText, range: new vscode.Range(new vscode.Position(0,0), document.lineAt(document.lineCount-1).range.end) };
    }
  }

  async getByBlockRange(position: vscode.Position, document: vscode.TextDocument): Promise<{ success: boolean; range?: vscode.Range; errorMsg?: string; syntaxKind?: string; isMatchAlt?: boolean; parentKinds?: string[]; isTacticContext?: boolean; isTermContext?: boolean }>{
    // just return current line to end of next branch
    const text = document.getText();
    const lines = text.split(/\r?\n/);
    let start = position.line;
    for (let i = position.line; i >= 0; i--) {
      if (/^\s*\|\s+\w+\s*=>/.test(lines[i]) || /^\s*by\b/.test(lines[i])) { start = i; break; }
    }
    let end = lines.length - 1;
    for (let i = start + 1; i < lines.length; i++) {
      if (/^\s*\|\s+\w+\s*=>/.test(lines[i])) { end = i; break; }
      if (/^\S/.test(lines[i]) && !/^\s/.test(lines[i])) { end = i; break; }
    }
    // Detect if this looks like a match alternative for testing
    const isMatchAlt = lines[start] && /^\s*\|\s+\w+\s*=>/.test(lines[start]);
    return { 
      success: true, 
      range: new vscode.Range(new vscode.Position(start, 0), new vscode.Position(end, 0)),
      syntaxKind: isMatchAlt ? "Lean.Parser.Tactic.matchRhs" : "Lean.Parser.Tactic.tacticSeq",
      isMatchAlt: !!isMatchAlt,
      parentKinds: isMatchAlt ? ["Lean.Parser.Term.matchAlt", "Lean.Parser.Tactic.matchRhs"] : ["Lean.Parser.Tactic.tacticSeq"],
      isTacticContext: true,  // Mock assumes we're in tactic context
      isTermContext: false
    };
  }

  dispose() {}
}
