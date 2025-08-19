import { expect } from 'chai';
import mock from 'mock-require';

// Mock minimal vscode API
class WorkspaceEditMock {
  public inserts: Array<{ uri: any; position: any; text: string }> = [];
  insert(uri: any, position: any, text: string) { this.inserts.push({ uri, position, text }); return true; }
}

const vscodeMock: any = {
  WorkspaceEdit: WorkspaceEditMock,
  Position: class {
    line: number; character: number;
    constructor(line: number, character: number) { this.line = line; this.character = character; }
  },
  Range: class { constructor(public sl: number, public sc: number, public el: number, public ec: number) {} },
  EndOfLine: { LF: 1 },
  window: { createOutputChannel: (_name: string) => ({ appendLine() {}, show() {}, dispose() {} }) },
  workspace: {
    applyEdit: async (_we: any) => true,
    getConfiguration: (_section?: string, _scope?: any) => ({
      get: (_key: string, def: any) => def, // defaults: insertSpaces=true, tabSize=2
    })
  }
};

mock('vscode', vscodeMock);

// Now import the service (after mocking)
import { CodeModifierService } from '../services/codeModifier';

// Minimal TextDocument mock
class TextDocMock {
  uri = { toString: () => 'untitled:mock.lean' };
  fileName = 'mock.lean';
  isUntitled = false;
  languageId = 'lean4';
  version = 1;
  isDirty = false;
  isClosed = false;
  eol = vscodeMock.EndOfLine.LF;
  lines: string[];
  lineCount: number;
  constructor(text: string) {
    this.lines = text.split(/\r?\n/);
    this.lineCount = this.lines.length;
  }
  lineAt(pos: any) {
    const ln = typeof pos === 'number' ? pos : pos.line;
    const text = this.lines[ln] ?? '';
    const firstNonWhitespaceCharacterIndex = text.length - text.trimStart().length;
    return {
      lineNumber: ln,
      text,
      range: new vscodeMock.Range(ln, 0, ln, text.length),
      rangeIncludingLineBreak: new vscodeMock.Range(ln, 0, ln, text.length + 1),
      firstNonWhitespaceCharacterIndex,
      isEmptyOrWhitespace: text.trim().length === 0,
    };
  }
  getText() { return this.lines.join('\n'); }
}

describe('Indentation around by-block', () => {
  it('admit: inserts with two-space indent after theorem ... := by', async () => {
    const source = [
      'import Mathlib',
      'import MathEye',
      '-- Test with mathlib functionality',
      'theorem test_theorem (a b : ℕ) : a + b = b + a := by'
    ].join('\n');

    const doc = new TextDocMock(source);
    const goals = [{ type: '⊢ a + b = b + a' }];
    const service = new CodeModifierService();

    // Position at end of the by-line
    const byLine = 3;
    const pos = new vscodeMock.Position(byLine, doc.lineAt(byLine).text.length);

    // Capture inserts
    const edit = new WorkspaceEditMock();
    const originalApply = vscodeMock.workspace.applyEdit;
    vscodeMock.workspace.applyEdit = async (we: any) => { edit.inserts = we.inserts; return true; };

    try {
      await service.applyFeedback(doc as any, goals as any, { goalIndex: 0, action: 'admit' } as any, pos as any, { useExactPosition: true });
      expect(edit.inserts).to.have.length(1);
      const inserted = edit.inserts[0].text;

      // If not at column 0, service will add a leading newline
      // We want to assert two spaces before have/exact on their lines
      expect(inserted).to.match(/\n  have /);
      expect(inserted).to.match(/\n  exact /);
    } finally {
      vscodeMock.workspace.applyEdit = originalApply;
    }
  });

  it('deny: inserts with two-space indent and ¬', async () => {
    const source = [
      'import Mathlib',
      'import MathEye',
      '-- Test with mathlib functionality',
      'theorem test_theorem (a b : ℕ) : a + b = b + a := by'
    ].join('\n');

    const doc = new TextDocMock(source);
    const goals = [{ type: '⊢ a + b = b + a' }];
    const service = new CodeModifierService();

    const pos = new vscodeMock.Position(3, doc.lineAt(3).text.length);

    const edit = new WorkspaceEditMock();
    const originalApply = vscodeMock.workspace.applyEdit;
    vscodeMock.workspace.applyEdit = async (we: any) => { edit.inserts = we.inserts; return true; };

    try {
      await service.applyFeedback(doc as any, goals as any, { goalIndex: 0, action: 'deny' } as any, pos as any, { useExactPosition: true });
      expect(edit.inserts).to.have.length(1);
      const inserted = edit.inserts[0].text;
      expect(inserted).to.match(/\n  have /);
      expect(inserted).to.contain('¬');
    } finally {
      vscodeMock.workspace.applyEdit = originalApply;
    }
  });

  it('respects editor.tabSize=4 when configured (produces 4 spaces)', async () => {
    const source = [
      'theorem test_theorem (a b : ℕ) : a + b = b + a := by'
    ].join('\n');

    const doc = new TextDocMock(source);
    const goals = [{ type: '⊢ a + b = b + a' }];
    const service = new CodeModifierService();

    // Override configuration to simulate tabSize=4
    const originalGetCfg = vscodeMock.workspace.getConfiguration;
    vscodeMock.workspace.getConfiguration = (_section?: string, _scope?: any) => ({
      get: (key: string, def: any) => key === 'tabSize' ? 4 : (key === 'insertSpaces' ? true : def)
    });

    const pos = new vscodeMock.Position(0, doc.lineAt(0).text.length);
    const edit = new WorkspaceEditMock();
    const originalApply = vscodeMock.workspace.applyEdit;
    vscodeMock.workspace.applyEdit = async (we: any) => { edit.inserts = we.inserts; return true; };

    try {
      await service.applyFeedback(doc as any, goals as any, { goalIndex: 0, action: 'admit' } as any, pos as any, { useExactPosition: true });
      const inserted = edit.inserts[0].text;
      // Expect four spaces when tabSize=4
      expect(inserted).to.match(/\n    have /);
      expect(inserted).to.match(/\n    exact /);
    } finally {
      vscodeMock.workspace.applyEdit = originalApply;
      vscodeMock.workspace.getConfiguration = originalGetCfg;
    }
  });
});
