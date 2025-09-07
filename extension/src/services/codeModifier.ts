import * as vscode from 'vscode';
import { ProofGoal, UserFeedback } from '../types';
import { LogicalCursorResult } from '../types/cursorModes';
import { HistoryManager, HistoryOperation } from './historyManager';
import { LeanClientService } from './leanClient';

/**
 * Service for modifying Lean source code based on user feedback on proof goals
 */
export class CodeModifierService {
    private outputChannel: vscode.OutputChannel;
    private nextVariableIndex: number = 1;
    private historyManager: HistoryManager;
    private leanClient: LeanClientService;

    constructor(outputChannel: vscode.OutputChannel, leanClient: LeanClientService) {
        this.outputChannel = outputChannel;
        this.leanClient = leanClient;
        this.historyManager = new HistoryManager();
    }

    async ensureImportsAndMacros(document: vscode.TextDocument): Promise<void> {
        const fullText = document.getText();
        const edits = new vscode.WorkspaceEdit();
        let changed = false;
        // Ensure `import MathEye` exists so RPC methods are registered
        if (!/^\s*import\s+MathEye\b/m.test(fullText)) {
            // Insert after leading imports/blank lines
            let insertLine = 0;
            for (let ln = 0; ln < document.lineCount; ln++) {
                const t = document.lineAt(ln).text.trim();
                if (t.length === 0) { insertLine = ln + 1; continue; }
                if (t.startsWith('import ')) { insertLine = ln + 1; continue; }
                break;
            }
            edits.insert(document.uri, new vscode.Position(insertLine, 0), 'import MathEye\n');
            changed = true;
        }
        // Ensure human_oracle macro exists once
        if (!/^\s*macro\s+"human_oracle"\s*:/m.test(fullText)) {
            // place macro after imports with a blank line
            let insertLine = 0;
            for (let ln = 0; ln < document.lineCount; ln++) {
                const t = document.lineAt(ln).text.trim();
                if (t.length === 0) { insertLine = ln + 1; continue; }
                if (t.startsWith('import ')) { insertLine = ln + 1; continue; }
                if (/^\s*open\b/.test(t)) { insertLine = ln + 1; continue; }
                break;
            }
            edits.insert(document.uri, new vscode.Position(insertLine, 0), 'macro "human_oracle" : tactic => `(tactic| sorry)\n\n');
            changed = true;
        }
        if (changed) {
            await vscode.workspace.applyEdit(edits);
            try { await document.save(); } catch {}
            // Give Lean server a moment to re-elaborate
            await new Promise(r => setTimeout(r, 150));
        }
    }

    /**
     * Apply feedback using a logical cursor position, optionally deleting a range first.
     */
    async applyFeedbackWithLogicalCursor(
        document: vscode.TextDocument,
        goals: ProofGoal[],
        feedback: UserFeedback,
        logicalCursor: LogicalCursorResult,
        deleteRange?: vscode.Range
    ): Promise<boolean> {
        // Minimal debug logging; real behavior driven by Lean AST RPC
        this.outputChannel.appendLine(`[DEBUG] applyFeedbackWithLogicalCursor action=${feedback.action}`);
        try {
            // Snapshot by-block content (for rollback) if available
            let byBlockInfo = logicalCursor.byBlock 
                ? {
                    range: new vscode.Range(
                        new vscode.Position(logicalCursor.byBlock.startPosition.line, 0),
                        logicalCursor.byBlock.endPosition
                    ),
                    content: document.getText(new vscode.Range(
                        new vscode.Position(logicalCursor.byBlock.startPosition.line, 0),
                        logicalCursor.byBlock.endPosition
                    ))
                }
                : null;
            if (!byBlockInfo) {
                try {
                    const br = await this.leanClient.getByBlockRange(logicalCursor.position, document);
                    if (br.success && br.range) byBlockInfo = { range: br.range, content: document.getText(br.range) } as any;
                } catch {}
            }
            if (byBlockInfo) this.outputChannel.appendLine(`[DEBUG] byBlock backup captured (${byBlockInfo.range.start.line}-${byBlockInfo.range.end.line})`);

            // Capture anchor (MVP): declName + path + original body, for per-block history
            let anchorPayload: any = null;
            try {
                const ca = await this.leanClient.captureAnchor(logicalCursor.position, document);
                if (ca && ca.success) {
                    this.outputChannel.appendLine(`[ANCHOR] pathLen=${(ca.path||[]).length}`);
                    anchorPayload = { declName: ca.declName || '', path: ca.path || [], originalBody: ca.originalBody || '', anchorPos: ca.anchorPos };
                }
            } catch {}

            // Pure AST path: delegate edit to Lean RPC and apply returned range/text
            const goal = goals[feedback.goalIndex];
            if (!goal) throw new Error(`Invalid goal index: ${feedback.goalIndex}`);
            const normalized = (feedback.action || 'admit').trim();
            const action: 'admit' | 'deny' = normalized === 'deny' ? 'deny' : 'admit';
            // Ensure required imports/macros before server RPC
            await this.ensureImportsAndMacros(document);
            // Prefer passing the by-block range if available for deterministic server targeting
            const byRange = logicalCursor.byBlock
                ? new vscode.Range(logicalCursor.byBlock.startPosition, logicalCursor.byBlock.endPosition)
                : undefined;
            // Decide whether we need to wrap with `by` (term context only)
            let includeByOnSeq: boolean | undefined = undefined;
            try {
                const br = await this.leanClient.getByBlockRange(logicalCursor.position, document);
                if (br) includeByOnSeq = !!(br.isTermContext && !br.isTacticContext);
            } catch {}
            // Snap insertion point to a canonical position inside the tactic block to avoid seam issues
            let insertPos = logicalCursor.position;
            try { insertPos = await this.leanClient.getInsertionPoint(insertPos, document); } catch {}
            // 统一为整文件替换：请求服务器直接返回整篇文本，避免局部替换导致快照漂移
            let resp = await this.leanClient.insertHaveByAction(insertPos, document, action, byRange, includeByOnSeq, true);
            if (!resp.success) {
                throw new Error(resp.errorMsg || 'Lean RPC insert failed');
            }
            // Capture replaced文本（用于历史记录）：若返回整文件范围，则用全文；否则用局部片段
            const wholeRangeReturned = resp.range
              && resp.range.start.line === 0 && resp.range.start.character === 0
              && resp.range.end.line >= document.lineCount - 1;
            const replacedTextBefore = wholeRangeReturned
              ? document.getText()
              : document.getText(resp.range!);
            const edit = new vscode.WorkspaceEdit();

            // TEST-MODE diagnostics: dump ranges/slices to file for post-mortem
            try {
                if (process.env.MATHEYE_TEST_MODE === '1') {
                    const p = require('path'); const fs = require('fs');
                    const outDir = p.resolve(__dirname, '../test/suite');
                    try { fs.mkdirSync(outDir, { recursive: true }); } catch {}
                    const dbg = p.resolve(outDir, `logic_debug_${Date.now()}.txt`);
                    const around = (pos: vscode.Position, n = 2) => {
                        const s = Math.max(0, pos.line - n);
                        const e = Math.min(document.lineCount - 1, pos.line + n);
                        const seg = document.getText(new vscode.Range(new vscode.Position(s, 0), new vscode.Position(e, document.lineAt(e).text.length)));
                        return `L${s}-${e}:\n${seg}`;
                    };
                    const beforeSlice = replacedTextBefore;
                    const contentHead = document.getText(new vscode.Range(new vscode.Position(0,0), new vscode.Position(Math.min(50, document.lineCount-1), 0)));
                    fs.writeFileSync(dbg,
                        [
                            `byRange=${byRange ? `[${byRange.start.line}:${byRange.start.character} - ${byRange.end.line}:${byRange.end.character}]` : 'none'}`,
                            `logicalCursor=${logicalCursor.position.line}:${logicalCursor.position.character}`,
                            `insertPos=${insertPos.line}:${insertPos.character}`,
                            `resp.range=[${resp.range!.start.line}:${resp.range!.start.character} - ${resp.range!.end.line}:${resp.range!.end.character}]`,
                            `BEFORE_RANGE_SLICE:\n${beforeSlice}`,
                            `AROUND_INSERT:\n${around(insertPos)}`,
                            `DOC_HEAD_PREVIEW:\n${contentHead}`
                        ].join('\n\n'), 'utf8');
                }
            } catch {}

            // 仅允许整篇替换：要求服务器返回整文件范围
            if (!wholeRangeReturned) {
                throw new Error('服务器未返回整篇替换范围');
            }
            const fullRange = new vscode.Range(0, 0, document.lineCount, 0);
            edit.replace(document.uri, fullRange, resp.newText || '');
            const applied = await vscode.workspace.applyEdit(edit);
            if (!applied) return false;

            // Record precise history (for rollback)
            if (byBlockInfo) {
                const usedStart = resp.range!.start;
                const usedEnd = resp.range!.end;
                const relStartLine = usedStart.line - byBlockInfo.range.start.line;
                const relEndLine = usedEnd.line - byBlockInfo.range.start.line;
                const anchor = anchorPayload || {};
                const historyOperation: HistoryOperation = {
                    type: action,
                    goalIndex: feedback.goalIndex,
                    declName: anchor.declName,
                    path: anchor.path,
                    originalBody: anchor.originalBody,
                    anchorPos: anchor.anchorPos ? { line: anchor.anchorPos.line, character: anchor.anchorPos.character } : undefined,
                    byBlockRange: byBlockInfo.range,
                    originalByBlockContent: byBlockInfo.content,
                    insertedText: resp.newText || '',
                    replacedText: replacedTextBefore,
                    documentVersion: (document as any).version ?? undefined,
                    byBlockStartLine: byBlockInfo.range.start.line,
                    insertRelStartLine: relStartLine,
                    insertRelStartChar: usedStart.character,
                    insertRelEndLine: relEndLine,
                    insertRelEndChar: usedEnd.character,
                    absStartLine: usedStart.line,
                    absStartChar: usedStart.character,
                    absEndLine: usedEnd.line,
                    absEndChar: usedEnd.character,
                    timestamp: Date.now(),
                    documentUri: document.uri.toString()
                };
                this.historyManager.recordOperation(historyOperation);
            }

            return true;
        } catch (error) {
            const errorMsg = `Error applying feedback with logical cursor: ${error}`;
            this.outputChannel.appendLine(errorMsg);
            try {
                if (process.env.MATHEYE_TEST_MODE === '1') {
                    const p = require('path'); const fs = require('fs');
                    const outDir = p.resolve(__dirname, '../test/suite');
                    try { fs.mkdirSync(outDir, { recursive: true }); } catch {}
                    fs.appendFileSync(p.resolve(outDir, 'logic_debug_errors.log'), `${new Date().toISOString()} ${errorMsg}\n`);
                }
            } catch {}
            vscode.window.showErrorMessage(errorMsg);
            return false;
        }
    }

    /**
     * Apply user feedback to proof goals by inserting code at cursor position
     */
    async applyFeedback(
        document: vscode.TextDocument,
        goals: ProofGoal[],
        feedback: UserFeedback,
        position: vscode.Position,
        options?: { useExactPosition?: boolean; replaceRange?: vscode.Range }
    ): Promise<{ success: boolean; insertedText?: string; replacedText?: string; absStart?: vscode.Position; absEnd?: vscode.Position }> {
        try {
            const goal = goals[feedback.goalIndex];
            if (!goal) {
                throw new Error(`Invalid goal index: ${feedback.goalIndex}`);
            }

            const edit = new vscode.WorkspaceEdit();
            let insertedText: string | undefined;
            let replacedText: string | undefined;
            let absStart: vscode.Position | undefined;
            let absEnd: vscode.Position | undefined;
            // Insert human_oracle macro at top if missing
            const fullText = document.getText();
            const macroRegex = /^\s*macro\s+"human_oracle"\s*:/m;
            if (!macroRegex.test(fullText)) {
                let insertLine = 0;
                const total = document.lineCount;
                for (let ln = 0; ln < total; ln++) {
                    const txt = document.lineAt(ln).text.trim();
                    if (txt.length === 0) { insertLine = ln + 1; continue; }
                    if (txt.startsWith('import ')) { insertLine = ln + 1; continue; }
                    break;
                }
                const macroDef = 'macro "human_oracle" : tactic => `(tactic| sorry)\n\n';
                edit.insert(document.uri, new vscode.Position(insertLine, 0), macroDef);
            }
            const normalized = (feedback.action || 'admit').trim();
            const action: 'admit' | 'deny' = normalized === 'deny' ? 'deny' : 'admit';
            // Use Lean RPC (Meta-based) to insert have by action; server reads goal Expr, delabs, parses, trims, appends
            await this.ensureImportsAndMacros(document);
            // 显式请求整篇返回，禁止任何客户端端的字符串拼接
            let resp = await this.leanClient.insertHaveByAction(position, document, action, undefined, undefined, true);
            if (!resp.success && /No RPC method \'MathEye\\.insertHaveByAction\'/m.test(String(resp.errorMsg || ''))) {
                // Retry once after ensuring imports/macros
                resp = await this.leanClient.insertHaveByAction(position, document, action);
            }
            if (!resp.success || !resp.newText || !resp.range) {
                throw new Error(resp.errorMsg || 'Lean RPC insert failed');
            }
            replacedText = document.getText(resp.range);
            insertedText = resp.newText;
            absStart = resp.range.start;
            absEnd = resp.range.end;

            // 仅允许整篇替换：要求服务器返回整文件范围
            const wholeRangeReturned = resp.range.start.line === 0 && resp.range.start.character === 0 && resp.range.end.line >= document.lineCount - 1;
            if (!wholeRangeReturned) {
                throw new Error('服务器未返回整篇替换范围');
            }
            const fullRange = new vscode.Range(0, 0, document.lineCount, 0);
            edit.replace(document.uri, fullRange, insertedText || '');

            const success = await vscode.workspace.applyEdit(edit);
            
            if (success) {
                this.outputChannel.appendLine(`Applied ${action} to goal: ${goal.type.substring(0, 50)}...`);
            } else {
                this.outputChannel.appendLine(
                    `Failed to apply ${feedback.action} to goal`
                );
            }

            return { success, insertedText, replacedText, absStart, absEnd };

        } catch (error) {
            const errorMsg = `Error applying feedback: ${error}`;
            this.outputChannel.appendLine(errorMsg);
            vscode.window.showErrorMessage(errorMsg);
            return { success: false };
        }
    }

    /**
     * Rollback the operation for a specific goal
     */
    async rollbackOperation(document: vscode.TextDocument): Promise<boolean> {
        try {
            this.outputChannel.appendLine(`[ROLLBACK] Attempting rollback for last insertion\'s by block`);
            const lastOp = this.historyManager.getLastOperationForDocument(document);
            if (!lastOp) {
                vscode.window.showInformationMessage('没有可回滚的操作');
                return false;
            }
            const operation = lastOp as any;
            // Anchor-based restore: no fallback to ranges
            if (!operation.path || !operation.originalBody || !operation.anchorPos) {
                vscode.window.showErrorMessage('回滚失败：历史锚缺失');
                return false;
            }
            const res = await this.leanClient.restoreByAnchor(document, {
                declName: operation.declName || '',
                path: operation.path || [],
                originalBody: operation.originalBody || '',
                anchorPos: new vscode.Position(operation.anchorPos.line, operation.anchorPos.character)
            });
            if (!res.success || !res.newText || !res.range) {
                vscode.window.showErrorMessage(`回滚失败：${res.errorMsg || '未知错误'}`);
                return false;
            }
            const edit = new vscode.WorkspaceEdit();
            // Always whole-file replace on restore
            const fullRange = new vscode.Range(0, 0, document.lineCount, 0);
            edit.replace(document.uri, fullRange, res.newText);
            const ok = await vscode.workspace.applyEdit(edit);
            if (ok) this.historyManager.clearLastOperationForDocument(document);
            return ok;

        } catch (error) {
            const errorMsg = `Error during rollback: ${error}`;
            this.outputChannel.appendLine(errorMsg);
            vscode.window.showErrorMessage(errorMsg);
            return false;
        }
    }

    /**
     * 检查指定目标是否有历史记录可以回滚
     */
    canRollbackGoal(_goalIndex: number): boolean {
        return false;
    }

    /**
     * Check if rollback is available for a specific goal
     */
    canRollback(_goalIndex: number): boolean {
        return false;
    }

    /**
     * Check if rollback is available and likely valid for a specific goal
     */
    async canRollbackInCurrentBlock(document: vscode.TextDocument, position: vscode.Position): Promise<boolean> {
        const lastOp = this.historyManager.getLastOperationForDocument(document);
        if (!lastOp) return false;
        const line = position.line, ch = position.character;
        // 1) Inside last inserted snippet?
        const inSnippet = (
            (line > lastOp.absStartLine || (line === lastOp.absStartLine && ch >= lastOp.absStartChar)) &&
            (line < lastOp.absEndLine   || (line === lastOp.absEndLine   && ch <= lastOp.absEndChar))
        );
        // 2) Or inside the same by block (use recorded byBlockRange)
        const inBlock = line >= lastOp.byBlockRange.start.line && line <= lastOp.byBlockRange.end.line;
        return inSnippet || inBlock;
    }

    /**
     * Generate code text to insert based on user action
     */
    private generateInsertText(goal: ProofGoal, action: 'admit' | 'deny', variableName: string): string {
        const prop = this.extractGoalProposition(goal.type);

        switch (action) {
            case 'admit':
                return `have ${variableName} : ${prop} := by human_oracle\nexact ${variableName}\n`;
            case 'deny':
                return `have ${variableName} : ¬ (${prop}) := by human_oracle\n`;
            default:
                throw new Error(`Unknown action: ${action}`);
        }
    }

    /**
     * Extract the proposition from a pretty-printed goal string that may include
     * hypotheses and a line starting with '⊢'. If no '⊢' is present, return the full string.
     */
    private extractGoalProposition(goalText: string): string {
        if (!goalText) return goalText;
        // Prefer the last line containing '⊢'
        const lines = goalText.split(/\r?\n/);
        for (let i = lines.length - 1; i >= 0; i--) {
            const idx = lines[i].indexOf('⊢');
            if (idx >= 0) {
                return lines[i].slice(idx + 1).trim();
            }
        }
        // Fallback: use substring after last '⊢' anywhere
        const lastIdx = goalText.lastIndexOf('⊢');
        if (lastIdx >= 0) return goalText.slice(lastIdx + 1).trim();
        return goalText.trim();
    }

    /**
     * Preview the changes without applying them
     */
    previewChanges(goal: ProofGoal, action: 'admit' | 'deny'): string {
        return this.generateInsertText(goal, action, 'h');
    }

    /**
     * Reset variable counter
     */
    resetVariableCounter(): void {
        this.nextVariableIndex = 1;
    }

    showOutput(): void {
        this.outputChannel.show();
    }

    dispose(): void {
        this.historyManager.dispose();
    }
}
