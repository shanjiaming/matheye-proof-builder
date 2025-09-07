import { expect } from 'chai';
const mock = require('mock-require');
import type * as vscode from 'vscode';

// Provide basic vscode API with Position/Range to allow constructing results
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

const sendRequestStub = async (method: string, payload: any) => {
  if (method === "$/lean/rpc/connect") {
    return { sessionId: 's1' };
  }
  if (method === "$/lean/rpc/call") {
    if (payload.method === 'MathEye.getByBlockRange') {
      return { success: true, range: { start: { line: 3, character: 1 }, stop: { line: 7, character: 2 } } };
    }
    if (payload.method === 'MathEye.insertHaveByAction') {
      return { success: true, newText: 'by\n  exact h\n', range: { start: { line: 3, character: 1 }, stop: { line: 7, character: 2 } } };
    }
  }
  if (method === "$/lean/plainGoal") {
    return { goals: [ { hyps: [], goal: '⊢ P' } ] };
  }
  throw new Error('unexpected method: ' + method);
};

// Shared extension object so tests can mutate exports between cases
const extensionObj: any = {
  isActive: true,
  exports: {
    allFeatures: async () => ({ clientProvider: { getActiveClient: () => ({ sendRequest: sendRequestStub }) } })
  },
  activate: async () => {}
};

mock('vscode', {
  window: { createOutputChannel: () => ({ appendLine: (_: string) => {}, dispose: () => {} }) },
  Position: MockPosition,
  Range: MockRange,
  workspace: { getConfiguration: () => ({ get: () => false }) },
  extensions: {
    getExtension: (_: string) => extensionObj
  }
});

import { LeanClientService } from '../services/leanClient';
import { CursorMode } from '../types/cursorModes';
import { CursorModeManager } from '../services/cursorModeManager';

describe('LeanClientService RPC wrappers', () => {
  const mockOutputChannel = { appendLine: () => {}, dispose: () => {} } as any;

  it('getByBlockRange maps RangeDto correctly', async () => {
    const svc = new LeanClientService(mockOutputChannel);
    const fakeDoc: any = { uri: { toString: () => 'file:///tmp.lean' } };
    const res = await svc.getByBlockRange(new MockPosition(0, 0) as unknown as vscode.Position, fakeDoc);
    expect(res.success).to.equal(true);
    expect(res.range!.start.line).to.equal(3);
    expect(res.range!.end.character).to.equal(2);
  });

  it('insertHaveByAction returns newText and Range on success', async () => {
    const svc = new LeanClientService(mockOutputChannel);
    const fakeDoc: any = { uri: { toString: () => 'file:///tmp.lean' } };
    const res = await svc.insertHaveByAction(new MockPosition(0, 0) as unknown as vscode.Position, fakeDoc, 'admit');
    expect(res.success).to.equal(true);
    expect(res.newText).to.contain('exact');
    expect(res.range!.start.line).to.equal(3);
  });

  it('insertHaveByAction surfaces failure', async () => {
    // Temporarily override the client stub to return a failure for this case
    const failStub = async (method: string, payload: any) => {
      if (method === "$/lean/rpc/connect") return { sessionId: 's1' };
      if (method === "$/lean/rpc/call" && payload.method === 'MathEye.insertHaveByAction') {
        return { success: false, errorMsg: 'no tactic at pos' };
      }
      if (method === "$/lean/rpc/call" && payload.method === 'MathEye.getByBlockRange') {
        return { success: true, range: { start: { line: 0, character: 0 }, stop: { line: 1, character: 0 } } };
      }
      if (method === "$/lean/plainGoal") return { goals: [] };
      return (sendRequestStub as any)(method, payload);
    };
    // Rebuild LeanClientService with failure stub
    const svc = new LeanClientService(mockOutputChannel);
    const ext = (require('vscode').extensions.getExtension('leanprover.lean4'));
    ext.exports = { allFeatures: async () => ({ clientProvider: { getActiveClient: () => ({ sendRequest: failStub }) } }) };
    const fakeDoc: any = { uri: { toString: () => 'file:///tmp.lean' } };
    const res = await svc.insertHaveByAction(new MockPosition(0, 0) as unknown as vscode.Position, fakeDoc, 'admit');
    expect(res.success).to.equal(false);
    expect(String(res.errorMsg || '')).to.contain('no tactic');
  });

  it('CursorModeManager.calculateDeleteRange uses server by-block range', async () => {
    const svc = new LeanClientService(mockOutputChannel);
    const ext = (require('vscode').extensions.getExtension('leanprover.lean4'));
    // Force a deterministic range
    const localStub = async (method: string, payload: any) => {
      if (method === "$/lean/rpc/connect") return { sessionId: 's1' };
      if (method === "$/lean/rpc/call" && payload.method === 'MathEye.getByBlockRange')
        return { success: true, range: { start: { line: 10, character: 2 }, stop: { line: 20, character: 5 } } };
      // pass-through otherwise
      return (sendRequestStub as any)(method, payload);
    };
    ext.exports = { allFeatures: async () => ({ clientProvider: { getActiveClient: () => ({ sendRequest: localStub }) } }) };
    const ctx: any = { globalState: { get: (_: string, d: any) => d, update: async () => {} }, subscriptions: [] };
    const mgr = new CursorModeManager(ctx, svc);
    const doc: any = { uri: { toString: () => 'file:///tmp.lean' } };
    const del = await mgr.calculateDeleteRange(new MockPosition(12, 0) as unknown as vscode.Position, doc, CursorMode.CURRENT);
    expect(del!.start.line).to.equal(12);
    expect(del!.end.line).to.equal(20);
  });
});