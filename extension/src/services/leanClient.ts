import * as vscode from 'vscode';
import { MathEyeRpcInputParams, MathEyeRpcOutputParams } from '../types';

/**
 * Service for interacting with Lean language server via vscode-lean4 extension
 * Implements Paperproof-style RPC calls
 */
export class LeanClientService {
    private outputChannel: vscode.OutputChannel;

    constructor(outputChannel?: vscode.OutputChannel) {
        this.outputChannel = outputChannel || vscode.window.createOutputChannel("MathEye");
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

    /**
     * Insert have statement by calling MathEye.insertHaveByAction
     */
    async insertHaveByAction(
        position: vscode.Position,
        document: vscode.TextDocument,
        action: 'admit' | 'deny',
        byRange?: vscode.Range,
        includeByOnSeq?: boolean,
        returnWholeFile?: boolean
    ): Promise<{ success: boolean; newText?: string; range?: vscode.Range; errorMsg?: string }> {
        const client = await this.getLeanClient();
        const uri = document.uri.toString();
        
        // Debug logging at entry
        try {
            if (process.env.MATHEYE_TEST_MODE === '1') {
                const p = require('path'); const fs = require('fs');
                const logPath = p.resolve(__dirname, '..', 'rpc_debug.log');
                fs.appendFileSync(logPath, `[insertHaveByAction] ENTRY @ ${position.line}:${position.character} action=${action}\n`);
            }
        } catch {}
        
        const call = async () => {
            const sessionId = (await client.sendRequest("$/lean/rpc/connect", { uri })).sessionId;
            const params: any = {
                pos: { line: position.line, character: position.character },
                action: action,
            };
            if (byRange) {
                const rangeDto = {
                    start: { line: byRange.start.line, character: byRange.start.character },
                    stop: { line: byRange.end.line, character: byRange.end.character }
                };
                (params as any)["blockRange?"] = rangeDto;
            }
            if (includeByOnSeq !== undefined) {
                (params as any)["includeByOnSeq?"] = includeByOnSeq;
            }
            if (returnWholeFile !== undefined) {
                (params as any)["returnWholeFile?"] = returnWholeFile;
            }
            const rpcParams = {
                sessionId,
                method: "MathEye.insertHaveByAction",
                // Lean RPC requires textDocument + position for context resolution
                textDocument: { uri },
                position: { line: position.line, character: position.character },
                params
            };
            const result: any = await client.sendRequest("$/lean/rpc/call", rpcParams);

            // Debug logging to a guaranteed-existing directory under out/
            try {
                if (process.env.MATHEYE_TEST_MODE === '1') {
                    const p = require('path'); const fs = require('fs');
                    const logPath = p.resolve(__dirname, '..', 'rpc_debug.log');
                    fs.appendFileSync(logPath, `[insertHaveByAction] RESULT @ ${position.line}:${position.character} -> ${JSON.stringify(result)}\n`);
                }
            } catch {}
            
            if (process.env.MATHEYE_TEST_MODE === '1') {
                try {
                    const p = require('path'); const fs = require('fs');
                    const logPath = p.resolve(__dirname, '..', 'rpc_debug.log');
                    fs.appendFileSync(logPath, `[insertHaveByAction] BUILD_TAG=${result?.buildTag || ''}\n`);
                } catch {}
            }
            if (result && result.success) {
                const rg = result.range;
                const range = new vscode.Range(
                    new vscode.Position(rg.start.line, rg.start.character), 
                    new vscode.Position(rg.stop.line, rg.stop.character)
                );
                return { success: true, newText: result.newText, range };
            }
            return { success: false, errorMsg: result?.errorMsg || 'unknown error' };
        };
        
        try {
            return await call();
        } catch (e: any) {
            // Debug logging for exceptions
            try {
                if (process.env.MATHEYE_TEST_MODE === '1') {
                    const p = require('path'); const fs = require('fs');
                    const logPath = p.resolve(__dirname, '..', 'rpc_debug.log');
                    fs.appendFileSync(logPath, `[insertHaveByAction] EXCEPTION @ ${position.line}:${position.character} -> ${String(e)}\n`);
                }
            } catch {}
            return { success: false, errorMsg: String(e) };
        }
    }

    /**
     * Get by block range using MathEye.getByBlockRange
     */
    async getByBlockRange(
        position: vscode.Position, 
        document: vscode.TextDocument
    ): Promise<{success: boolean, range?: vscode.Range, isTacticContext?: boolean, isTermContext?: boolean, isMatchAlt?: boolean, syntaxKind?: string, errorMsg?: string, buildTag?: string}> {
        const client = await this.getLeanClient();
        const uri = document.uri.toString();
        
        try {
            const sessionId = (await client.sendRequest("$/lean/rpc/connect", { uri })).sessionId;
            const rpcParams = {
                sessionId,
                method: "MathEye.getByBlockRange", 
                textDocument: { uri },
                position: { line: position.line, character: position.character },
                params: {
                    pos: { line: position.line, character: position.character }
                }
            };
            const result: any = await client.sendRequest("$/lean/rpc/call", rpcParams);
            // TEST-MODE diagnostics: append a concise record of the RPC result
            try {
                if (process.env.MATHEYE_TEST_MODE === '1') {
                    const p = require('path'); const fs = require('fs');
                    const logPath = p.resolve(__dirname, '..', 'rpc_debug.log');
                    const rg = result && result.range ? `[${result.range.start.line}:${result.range.start.character}-${result.range.stop.line}:${result.range.stop.character}]` : 'none';
                    const parentKinds = Array.isArray(result?.parentKinds) ? JSON.stringify(result.parentKinds) : '[]';
                    fs.appendFileSync(logPath,
                        `[getByBlockRange] @ ${position.line}:${position.character} -> success=${!!(result && result.success)} range=${rg} syntax=${result?.syntaxKind} isTactic=${result?.isTacticContext} isTerm=${result?.isTermContext} isMatchAlt=${result?.isMatchAlt} parentKinds=${parentKinds}\n` +
                        `[getByBlockRange] BUILD_TAG=${result?.buildTag || ''}\n`
                    );
                }
            } catch {}
            
            if (result && result.success) {
                const rg = result.range;
                const range = new vscode.Range(
                    new vscode.Position(rg.start.line, rg.start.character),
                    new vscode.Position(rg.stop.line, rg.stop.character)
                );
                return {
                    success: true,
                    range,
                    isTacticContext: result.isTacticContext,
                    isTermContext: result.isTermContext,
                    isMatchAlt: result.isMatchAlt,
                    syntaxKind: result.syntaxKind,
                    buildTag: result.buildTag
                };
            }
            return { success: false, errorMsg: result?.errorMsg || 'unknown error', buildTag: result?.buildTag };
        } catch (e: any) {
            try {
                if (process.env.MATHEYE_TEST_MODE === '1') {
                    const p = require('path'); const fs = require('fs');
                    const logPath = p.resolve(__dirname, '..', 'rpc_debug.log');
                    fs.appendFileSync(logPath, `[getByBlockRange] @ ${position.line}:${position.character} -> error=${String(e)}\n`);
                }
            } catch {}
            return { success: false, errorMsg: String(e) };
        }
    }

    /**
     * Ensure document is visible to Lean server
     */
    private async ensureDocumentVisible(document: vscode.TextDocument): Promise<void> {
        // Simple implementation: just wait a bit
        await new Promise(r => setTimeout(r, 200));
    }

    // Removed legacy anchor capture/restore APIs

    /**
     * Restore a by-block using recorded range and original content via MathEye.restoreByBlock
     */
    async restoreByBlock(
        document: vscode.TextDocument,
        params: { blockRange: vscode.Range, originalByBlockContent: string }
    ): Promise<{ success: boolean; newText?: string; range?: vscode.Range; errorMsg?: string }>{
        const client = await this.getLeanClient();
        const uri = document.uri.toString();
        try {
            const sessionId = (await client.sendRequest("$/lean/rpc/connect", { uri })).sessionId;
            const rpcParams = {
                sessionId,
                method: "MathEye.restoreByBlock",
                textDocument: { uri },
                position: { line: params.blockRange.start.line, character: params.blockRange.start.character },
                params: {
                    blockRange: {
                        start: { line: params.blockRange.start.line, character: params.blockRange.start.character },
                        stop:  { line: params.blockRange.end.line,   character: params.blockRange.end.character }
                    },
                    originalByBlockContent: params.originalByBlockContent
                }
            };
            const result: any = await client.sendRequest("$/lean/rpc/call", rpcParams);
            if (result && result.success) {
                const range = new vscode.Range(
                    new vscode.Position(result.range.start.line, result.range.start.character),
                    new vscode.Position(result.range.stop.line, result.range.stop.character)
                );
                return { success: true, newText: result.newText, range };
            }
            return { success: false, errorMsg: result?.errorMsg || 'unknown error' };
        } catch (e: any) {
            return { success: false, errorMsg: String(e) };
        }
    }

    dispose(): void {
        this.outputChannel.dispose();
    }
}
