import { expect } from 'chai';
const mock = require('mock-require');
import type * as vscode from 'vscode';

// Provide minimal runtime for vscode API. TypeScript types come from @types/vscode above.
class MockPosition { constructor(public line: number, public character: number) {}
  isBefore(other: vscode.Position): boolean { return this.line < other.line || (this.line === other.line && this.character < other.character); }
  isBeforeOrEqual(other: vscode.Position): boolean { return this.isBefore(other) || this.isEqual(other); }
  isAfter(other: vscode.Position): boolean { return !this.isBeforeOrEqual(other); }
  isAfterOrEqual(other: vscode.Position): boolean { return !this.isBefore(other); }
  isEqual(other: vscode.Position): boolean { return this.line === other.line && this.character === other.character; }
  translate(): any { return this; }
  with(): any { return this; }
}
class MockRange { constructor(public start: vscode.Position, public end: vscode.Position) {}
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

import { CursorMode } from '../types/cursorModes';
import { CursorModeManager } from '../services/cursorModeManager';
import { LeanClientService } from '../services/leanClient';

// Mock ExtensionContext
const fakeContext: any = {
  globalState: {
    get: (_k: string, def: any) => def,
    update: async (_k: string, _v: any) => {}
  },
  subscriptions: []
};

describe('CursorModeManager.calculateDeleteRange', () => {
  it('returns range from logical cursor to by-block end when server provides range', async () => {
    const mockOutputChannel = { appendLine: () => {}, dispose: () => {} } as any;
    const lean = new LeanClientService(mockOutputChannel);
    // monkey-patch getByBlockRange to return a known range
    (lean as any).getByBlockRange = async (_pos: any) => ({ success: true, range: new MockRange(new MockPosition(10, 2) as unknown as vscode.Position, new MockPosition(20, 5) as unknown as vscode.Position) });
    const m = new CursorModeManager(fakeContext, lean);
    const doc: any = { };
    const actual = new MockPosition(12, 0) as unknown as vscode.Position;
    const del = await m.calculateDeleteRange(actual, doc, CursorMode.CURRENT);
    expect(del).to.be.instanceOf(MockRange);
    expect(del!.start.line).to.equal(12);
    expect(del!.end.line).to.equal(20);
  });
});