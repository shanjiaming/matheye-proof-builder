import { expect } from 'chai';
import { LeanClientService } from '../services/leanClient';

// Mock the 'vscode' module before importing code under test so mocha can run outside VSCode
// Only minimal surface is mocked as these tests only touch string helpers
const mock = require('mock-require');
mock('vscode', {
  window: {
    createOutputChannel: () => ({ appendLine: (_: string) => {}, dispose: () => {} }),
    showInformationMessage: (_msg: string) => {},
    visibleTextEditors: []
  },
  workspace: {
    getConfiguration: () => ({ get: () => undefined }),
    applyEdit: async () => true
  },
});

import { CodeModifierService } from '../services/codeModifier';

// Integration-like test is omitted here because VSCode/mocha host is required.

describe('CodeModifierService (unit)', () => {
  const mockOutputChannel = { appendLine: () => {}, dispose: () => {} } as any;
  const MockLeanClient = require('./mockLeanClient').MockLeanClientService;
  const mockLeanClient = new MockLeanClient() as LeanClientService;

  it('extracts proposition from goal text with ⊢', () => {
    const svc = new CodeModifierService(mockOutputChannel, mockLeanClient);
    const txt = 'h₁ : P\n⊢ Q ∧ R';
    // @ts-expect-error accessing private for unit test convenience
    const prop = svc.extractGoalProposition(txt);
    expect(prop).to.equal('Q ∧ R');
  });

  it('generates admit have+exact snippet', () => {
    const svc = new CodeModifierService(mockOutputChannel, mockLeanClient);
    const goal = { type: '⊢ P → Q' } as any;
    // @ts-expect-error
    const snippet = svc.generateInsertText(goal, 'admit', 'h1');
    expect(snippet).to.contain('have h1 :');
    expect(snippet).to.contain('exact h1');
  });

  it('generates deny have not snippet', () => {
    const svc = new CodeModifierService(mockOutputChannel, mockLeanClient);
    const goal = { type: '⊢ P' } as any;
    // @ts-expect-error
    const snippet = svc.generateInsertText(goal, 'deny', 'h2');
    expect(snippet).to.contain('have h2 : ¬ (');
  });
});