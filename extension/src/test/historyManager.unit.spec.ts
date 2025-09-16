import * as assert from 'assert';
const mock = require('mock-require');
import type * as vscode from 'vscode';

// Mock vscode API before importing the service under test
class MockPosition { 
  constructor(public line: number, public character: number) {}
  isBefore(other: vscode.Position): boolean { return this.line < other.line || (this.line === other.line && this.character < other.character); }
  isBeforeOrEqual(other: vscode.Position): boolean { return this.isBefore(other) || this.isEqual(other); }
  isAfter(other: vscode.Position): boolean { return !this.isBeforeOrEqual(other); }
  isAfterOrEqual(other: vscode.Position): boolean { return !this.isBefore(other); }
  isEqual(other: vscode.Position): boolean { return this.line === other.line && this.character === other.character; }
  translate(): any { return this; }
  with(): any { return this; }
}

class MockRange { 
  constructor(public start: vscode.Position, public end: vscode.Position) {}
  get isEmpty() { return this.start.line === this.end.line && this.start.character === this.end.character; }
  get isSingleLine() { return this.start.line === this.end.line; }
  contains(_positionOrRange: any): boolean { return true; }
  isEqual(other: vscode.Range): boolean { return this.start.isEqual(other.start) && this.end.isEqual(other.end); }
  intersection(_range: vscode.Range): vscode.Range | undefined { return this; }
  union(_other: vscode.Range): vscode.Range { return this; }
  with(): vscode.Range { return this; }
}

mock('vscode', {
  window: { createOutputChannel: () => ({ appendLine: (_: string) => {}, dispose: () => {} }) },
  Position: MockPosition,
  Range: MockRange,
  TextEditorRevealType: { InCenterIfOutsideViewport: 0 },
  workspace: { getConfiguration: () => ({ get: () => undefined }) },
});

import { HistoryManager, HistoryOperation } from '../services/historyManager';



describe('HistoryManager', () => {
  it('records and validates operations', async () => {
    const hm = new HistoryManager();
    const docUri = 'file:///test.lean';
    const byRange = new MockRange(new MockPosition(10, 0) as unknown as vscode.Position, new MockPosition(20, 0) as unknown as vscode.Position);
    const inserted = 'have h : P := by human_oracle\nexact h\n';
    const op: HistoryOperation = {
      type: 'admit',
      goalIndex: 0,
      byBlockRange: byRange as unknown as vscode.Range,
      originalByBlockContent: 'by\n  exact rfl\n',
      insertedText: inserted,
      byBlockStartLine: byRange.start.line,
      absStartLine: 18,
      absStartChar: 0,
      absEndLine: 19,
      absEndChar: 0,
      timestamp: Date.now(),
      documentUri: docUri
    };
    hm.recordOperation(op);
    const fakeDoc: any = {
      uri: { toString: () => docUri },
      getText: (range: any) => {
        // By-block content contains the inserted snippet, so validation should pass
        if (range.start.line === byRange.start.line && range.end.line === byRange.end.line) {
          return op.originalByBlockContent + inserted;
        }
        return '';
      }
    };
    assert.strictEqual(hm.canRollbackForDocument(fakeDoc), true);
    const ok = await hm.validateOperationInBlock(fakeDoc, byRange as unknown as vscode.Range);
    assert.strictEqual(ok, true);
    hm.clearLastOperationForDocument(fakeDoc);
    assert.strictEqual(hm.canRollbackForDocument(fakeDoc), false);
  });
});