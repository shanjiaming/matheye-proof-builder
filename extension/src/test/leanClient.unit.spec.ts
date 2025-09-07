import { expect } from 'chai';
const mock = require('mock-require');

// Minimal vscode API surface for constructing the service
mock('vscode', {
  window: {
    createOutputChannel: () => ({ appendLine: (_: string) => {}, dispose: () => {} }),
  },
  extensions: { getExtension: (_: string) => ({ isActive: true, exports: {}, activate: async () => {} }) },
});

import { LeanClientService } from '../services/leanClient';

describe('LeanClientService.convertPlainGoalToProofGoals', () => {
  const mockOutputChannel = { appendLine: () => {}, dispose: () => {} } as any;

  it('handles array-of-objects shape { hyps, goal }', () => {
    const svc = new LeanClientService(mockOutputChannel) as any;
    const input = { goals: [ { hyps: ["h : P"], goal: "Q" }, { hyps: [], goal: "R ∧ S" } ] };
    const res = svc["convertPlainGoalToProofGoals"](input);
    expect(res).to.have.length(2);
    expect(res[0].type).to.contain('⊢ Q');
    expect(res[1].type).to.contain('R ∧ S');
  });

  it('handles array-of-strings shape', () => {
    const svc = new LeanClientService(mockOutputChannel) as any;
    const input = { goals: ["⊢ P → Q", "⊢ R"] };
    const res = svc["convertPlainGoalToProofGoals"](input);
    expect(res).to.have.length(2);
    expect(res[0].type).to.equal('⊢ P → Q');
  });

  it('returns [] for unknown shapes', () => {
    const svc = new LeanClientService(mockOutputChannel) as any;
    const input = { somethingElse: true };
    const res = svc["convertPlainGoalToProofGoals"](input);
    expect(res).to.be.an('array').that.has.length(0);
  });
});