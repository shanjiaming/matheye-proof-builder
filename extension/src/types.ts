// TypeScript type definitions for MathEye extension

export interface ProofGoal {
  type: string;
  name?: string;
  translation?: string;
  translationError?: string;
}

export interface MathEyeRpcInputParams {
  pos: { line: number; character: number };
}

export interface MathEyeRpcOutputParams {
  goals: ProofGoal[];
  version: number;
}

export interface UserFeedback {
  goalIndex: number;
  action: 'admit' | 'deny' | 'toggleLock' | 'toggleTranslation' | 'cycleCursorMode';
}