import * as vscode from 'vscode';
import { MathEyeRpcInputParams, MathEyeRpcOutputParams } from '../types';

/**
 * Service for interacting with Lean language server via vscode-lean4 extension
 * Implements Paperproof-style RPC calls
 */
export class LeanClientService {
    private outputChannel: vscode.OutputChannel;

    constructor() {
        this.outputChannel = vscode.window.createOutputChannel("MathEye");
    }

    /**
     * Get the active Lean language client from vscode-lean4 extension
     */
    private async getLeanClient(): Promise<any> {
        const leanExtension = vscode.extensions.getExtension('leanprover.lean4');
        if (!leanExtension) {
            throw new Error('vscode-lean4 extension not found');
        }

        if (!leanExtension.isActive) {
            await leanExtension.activate();
        }

        const exports = leanExtension.exports;
        if (!exports) {
            throw new Error('vscode-lean4 extension has no exports');
        }

        // Get the client provider from exports
        const features = await exports.allFeatures();
        const clientProvider = features.clientProvider;
        
        if (!clientProvider) {
            throw new Error('LeanClientProvider not available');
        }

        const client = clientProvider.getActiveClient();
        if (!client) {
            throw new Error('No active Lean client');
        }

        return client;
    }

    /**
     * Get current goals like vscode-lean's "Plain Goal" view.
     * Uses the built-in $/lean/plainGoal request so it updates with cursor reliably.
     */
    async getProofGoals(
        position: vscode.Position,
        document: vscode.TextDocument
    ): Promise<MathEyeRpcOutputParams> {
        const client = await this.getLeanClient();
        const uri = document.uri.toString();
        const params = {
            textDocument: { uri },
            position: { line: position.line, character: position.character }
        };
        this.outputChannel.appendLine(`Calling $/lean/plainGoal for ${uri} at ${position.line}:${position.character}`);
        try {
            const plain: any = await client.sendRequest("$/lean/plainGoal", params);
            this.outputChannel.appendLine(`plainGoal response: ${JSON.stringify(plain).slice(0, 1000)}`);
            const goals = this.convertPlainGoalToProofGoals(plain);
            return { goals, version: 0 };
        } catch (e) {
            const errorMsg = `plainGoal failed: ${e}`;
            this.outputChannel.appendLine(errorMsg);
            throw e;
        }
    }

    /**
     * Ask Lean server for the canonical insertion point inside the current proof block.
     */
    async getInsertionPoint(position: vscode.Position, document: vscode.TextDocument): Promise<vscode.Position> {
        const client = await this.getLeanClient();
        const uri = document.uri.toString();
        const rpcParams = {
            sessionId: (await client.sendRequest("$/lean/rpc/connect", { uri })).sessionId,
            method: "MathEye.getInsertionPoint",
            textDocument: { uri },
            position: { line: position.line, character: position.character },
            params: { pos: { line: position.line, character: position.character } }
        };
        try {
            const resp: any = await client.sendRequest("$/lean/rpc/call", rpcParams);
            const p = resp.pos ?? resp;
            return new vscode.Position(p.line, p.character);
        } catch (e) {
            // Fallback to current position on failure
            return position;
        }
    }

    /**
     * Convert $/lean/plainGoal response into our ProofGoal[]
     */
    private convertPlainGoalToProofGoals(plain: any): { type: string; name?: string }[] {
        if (!plain) return [];
        // Common shapes observed in Lean: { goals: [ { hyps: string[], goal: string } ] }
        const mk = (goalStr: string) => ({ type: goalStr });
        if (Array.isArray(plain.goals)) {
            const arr = plain.goals as any[];
            // If it's array of strings
            if (arr.length > 0 && typeof arr[0] === 'string') {
                return arr.map((s) => mk(String(s)));
            }
            // If it's array of { hyps, goal } objects
            if (arr.length > 0 && typeof arr[0] === 'object') {
                return arr.map((g: any) => {
                    const hyps = Array.isArray(g.hyps) ? g.hyps.join('\n') : '';
                    const goal = typeof g.goal === 'string' ? g.goal : '';
                    const text = hyps ? `${hyps}\n⊢ ${goal}` : goal;
                    return mk(text || JSON.stringify(g));
                });
            }
        }
        // Fallback: try plain as string
        if (typeof plain === 'string') return [mk(plain)];
        // Unknown shape
        return [];
    }

    /**
     * Check if Lean server is running and ready
     */
    async isLeanServerReady(): Promise<boolean> {
        try {
            const client = await this.getLeanClient();
            return client.running || false;
        } catch (error) {
            this.outputChannel.appendLine(`Lean server check failed: ${error}`);
            return false;
        }
    }

    /**
     * Show output channel for debugging
     */
    showOutput(): void {
        this.outputChannel.show();
    }

    dispose(): void {
        this.outputChannel.dispose();
    }
}