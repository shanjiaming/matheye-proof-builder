import * as vscode from 'vscode';
import { ProofGoal, UserFeedback } from '../types';
import { LogicalCursorResult } from '../types/cursorModes';
import { HistoryManager, HistoryOperation } from './historyManager';

/**
 * Service for modifying Lean source code based on user feedback on proof goals
 */
export class CodeModifierService {
    private outputChannel: vscode.OutputChannel;
    private nextVariableIndex: number = 1;
    private historyManager: HistoryManager;

    constructor() {
        this.outputChannel = vscode.window.createOutputChannel("MathEye CodeModifier");
        this.historyManager = new HistoryManager();
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
        vscode.window.showInformationMessage(`🔥 DEBUG: applyFeedbackWithLogicalCursor called with action: ${feedback.action}`);
        try {
            // Use the by block info from logical cursor - no need to search!
            const byBlockInfo = logicalCursor.byBlock 
                ? {
                    // Include the complete by block from the line containing 'by' keyword
                    range: new vscode.Range(
                        new vscode.Position(logicalCursor.byBlock.byPosition.line, 0),
                        logicalCursor.byBlock.endPosition
                    ),
                    content: document.getText(new vscode.Range(
                        new vscode.Position(logicalCursor.byBlock.byPosition.line, 0),
                        logicalCursor.byBlock.endPosition
                    ))
                }
                : null;
            if (byBlockInfo) {
                vscode.window.showInformationMessage(`🔥 DEBUG: 备份内容: "${byBlockInfo.content}"`);
            } else {
                vscode.window.showInformationMessage(`🔥 DEBUG: byBlockInfo = null - no by block`);
            }
            
            // Normalize delete start: if prefix (0..start) is whitespace-only, start from column 0
            let insertionPosition = logicalCursor.position;
            if (deleteRange && !deleteRange.start.isEqual(deleteRange.end)) {
                try {
                    const startLineText = document.lineAt(deleteRange.start.line).text;
                    const prefix = startLineText.slice(0, deleteRange.start.character);
                    if (/^\s*$/.test(prefix)) {
                        const normStart = new vscode.Position(deleteRange.start.line, 0);
                        deleteRange = new vscode.Range(normStart, deleteRange.end);
                        insertionPosition = normStart;
                    }
                } catch {}
                // Use replaceRange to avoid intermediate empty lines and to ensure atomicity
                const success = await this.applyFeedback(
                    document,
                    goals,
                    feedback,
                    insertionPosition,
                    { replaceRange: deleteRange }
                );
                
                // Record history if backup was successful and operation succeeded
                if (success && byBlockInfo) {
                    const normalized = (feedback.action || 'admit').trim();
                    const action: 'admit' | 'deny' = normalized === 'deny' ? 'deny' : 'admit';
                    const historyOperation: HistoryOperation = {
                        type: action,
                        goalIndex: feedback.goalIndex,
                        byBlockRange: byBlockInfo.range,
                        originalByBlockContent: byBlockInfo.content,
                        timestamp: Date.now(),
                        documentUri: document.uri.toString()
                    };
                    this.historyManager.recordOperation(historyOperation);
                    vscode.window.showInformationMessage(`🔥 DEBUG: 已记录 ${action} 操作历史记录`);
                } else if (success) {
                    this.outputChannel.appendLine(`[DEBUG] No byBlockInfo, history not recorded (deleteRange path)`);
                }
                
                return success;
            }

            // Determine canonical insertion anchor within by-block to avoid stray blank lines
            let finalInsertPos = insertionPosition;
            if ((logicalCursor as any)?.byBlock) {
                try {
                    const byStartLine = (logicalCursor as any).byBlock.startPosition.line;
                    let anchorLine = byStartLine;
                    // Find the last non-empty, non-comment line between by-start and insertion line - 1
                    for (let ln = Math.min(insertionPosition.line - 1, document.lineCount - 1); ln >= byStartLine; ln--) {
                        const t = document.lineAt(ln).text.trim();
                        if (t.length === 0) continue;
                        if (t.startsWith('--')) continue;
                        anchorLine = ln;
                        break;
                    }
                    finalInsertPos = new vscode.Position(Math.min(anchorLine + 1, document.lineCount - 1), 0);
                } catch {}
            }

            // byBlockInfo already declared at the beginning of the method
            
            // Insert at canonical position with exact placement
            const ok = await this.applyFeedback(
                document,
                goals,
                feedback,
                finalInsertPos,
                { useExactPosition: true, replaceRange: deleteRange }
            );
            if (!ok) return false;
            
            // Record the by block backup after successful insertion
            if (byBlockInfo) {
                const normalized = (feedback.action || 'admit').trim();
                const action: 'admit' | 'deny' = normalized === 'deny' ? 'deny' : 'admit';
                const historyOperation: HistoryOperation = {
                        type: action,
                        goalIndex: feedback.goalIndex,
                        byBlockRange: byBlockInfo.range,
                        originalByBlockContent: byBlockInfo.content,
                        timestamp: Date.now(),
                        documentUri: document.uri.toString()
                    };
                this.historyManager.recordOperation(historyOperation);
                this.outputChannel.appendLine(`[DEBUG] Recorded history for ${action} operation`);
            } else {
                this.outputChannel.appendLine(`[DEBUG] No byBlockInfo, history not recorded`);
            }

            // After insertion, trim any accidental extra blank lines at the insertion site
            try {
                const line = Math.min(logicalCursor.position.line + 1, document.lineCount - 1);
                const lineText = document.lineAt(line).text;
                const prev = document.lineAt(Math.max(0, line - 1)).text;
                // If there is a double blank (prev blank and current blank), collapse to single
                if (prev.trim().length === 0 && lineText.trim().length === 0) {
                    const rng = new vscode.Range(new vscode.Position(line - 1, 0), new vscode.Position(line, lineText.length));
                    const trimEdit = new vscode.WorkspaceEdit();
                    trimEdit.delete(document.uri, rng);
                    await vscode.workspace.applyEdit(trimEdit);
                }
            } catch {}
            return true;
        } catch (error) {
            const errorMsg = `Error applying feedback with logical cursor: ${error}`;
            this.outputChannel.appendLine(errorMsg);
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
    ): Promise<boolean> {
        try {
            const goal = goals[feedback.goalIndex];
            if (!goal) {
                throw new Error(`Invalid goal index: ${feedback.goalIndex}`);
            }

            const edit = new vscode.WorkspaceEdit();
            // Insert human_oracle macro at top if missing
            const fullText = document.getText();
            if (!fullText.includes('macro "human_oracle"')) {
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
            const variableName = this.computeUniqueHypName(document, position);
            const normalized = (feedback.action || 'admit').trim();
            const action: 'admit' | 'deny' = normalized === 'deny' ? 'deny' : 'admit';
            const rawText = this.generateInsertText(goal, action, variableName);
            if (options?.replaceRange) {
                const indent = this.computeIndentForAppendAtTail(document, position);
                const replaceStartChar = options.replaceRange.start.character;
                let text = (replaceStartChar > 0 ? "\n" : "") + this.applyIndent(indent, rawText);
                // Avoid trailing double blank
                if (/\n\s*\n$/.test(text)) {
                    text = text.replace(/\n\s*\n$/, "\n");
                }
                edit.replace(document.uri, options.replaceRange, text);
            } else if (options?.useExactPosition) {
                const indent = this.computeIndentForAppendAtTail(document, position);
                // When inside a by-block, ensure a single newline before our insertion and no trailing extra blank line
                // If at column 0, do not add leading newline; if at non-zero column but the tail to EOL is whitespace-only,
                // also do not add a leading newline because we will delete that tail first when deleteRange is used.
                const curLine = document.lineAt(Math.min(position.line, document.lineCount - 1));
                const tail = curLine.text.slice(position.character);
                const needsNewline = position.character > 0 && tail.trim().length > 0;
                let text = (needsNewline ? "\n" : "") + this.applyIndent(indent, rawText);
                // Avoid producing an extra blank line at end
                if (/\n\s*\n$/.test(text)) {
                    text = text.replace(/\n\s*\n$/, "\n");
                }
                edit.insert(document.uri, position, text);
            } else {
                const best = this.computeBestInsertion(document, position, rawText);
                if (best.kind === 'replace') {
                    edit.replace(document.uri, best.range, best.text);
                } else {
                    edit.insert(document.uri, best.position, best.text);
                }
            }

            const success = await vscode.workspace.applyEdit(edit);
            
            if (success) {
                this.outputChannel.appendLine(`Applied ${action} to goal: ${goal.type.substring(0, 50)}...`);
            } else {
                this.outputChannel.appendLine(
                    `Failed to apply ${feedback.action} to goal`
                );
            }

            return success;

        } catch (error) {
            const errorMsg = `Error applying feedback: ${error}`;
            this.outputChannel.appendLine(errorMsg);
            vscode.window.showErrorMessage(errorMsg);
            return false;
        }
    }

    private computeIndentForAppendAtTail(document: vscode.TextDocument, position: vscode.Position): string {
        // Goal: append at tail of tactic block with proper indentation
        const editorCfg = vscode.workspace.getConfiguration('editor', document.uri);
        const tabSize = editorCfg.get<number>('tabSize', 2);
        const insertSpaces = editorCfg.get<boolean>('insertSpaces', true);
        const indentUnit = insertSpaces ? ' '.repeat(Math.max(1, tabSize)) : '\t';

        // Look backwards to find the appropriate indentation context
        for (let lineNum = position.line; lineNum >= 0; lineNum--) {
            const line = document.lineAt(lineNum);
            const lineText = line.text.trim();
            
            // Skip empty lines
            if (lineText.length === 0) continue;
            
            const lineIndent = line.text.slice(0, line.firstNonWhitespaceCharacterIndex);
            
            // If we find a 'by' line, we should indent one level deeper
            if (/\bby\s*$/.test(lineText) || /\bby\s+\w/.test(lineText)) {
                return lineIndent + indentUnit;
            }
            
            // If we find a line that looks like it's inside a proof block (starts with have, exact, apply, etc.)
            // use the same indentation level
            if (/^\s*(have|exact|apply|rw|simp|sorry|let|obtain)\b/.test(line.text)) {
                return lineIndent;
            }
            
            // If we find a theorem/def/lemma line, indent one level deeper
            if (/^\s*(theorem|def|lemma|example|instance)\b/.test(line.text)) {
                return lineIndent + indentUnit;
            }
        }
        
        // Fallback: use current line's indentation or add one indent unit if we're at column 0
        const cur = document.lineAt(Math.min(position.line, document.lineCount - 1));
        const curIndent = cur.text.slice(0, cur.firstNonWhitespaceCharacterIndex);
        return curIndent.length > 0 ? curIndent : indentUnit;
    }

    private applyIndent(indent: string, text: string): string {
        return text.split('\n').map(line => (line.length > 0 ? indent + line : line)).join('\n');
    }

    /**
     * Calculate the range where text was inserted for history tracking
     */
    private calculateInsertionRange(
        document: vscode.TextDocument,
        position: vscode.Position,
        options?: { useExactPosition?: boolean; replaceRange?: vscode.Range }
    ): vscode.Range {
        if (options?.replaceRange) {
            return options.replaceRange;
        }
        
        // For other cases, estimate based on position
        // This is a rough estimate since the exact range depends on insertion logic
        const estimatedEndLine = position.line + 2; // Most have blocks span 2-3 lines
        const estimatedEnd = new vscode.Position(
            Math.min(estimatedEndLine, document.lineCount - 1),
            0
        );
        
        return new vscode.Range(position, estimatedEnd);
    }

    /**
     * Get the original text that will be replaced/overwritten
     */
    private getOriginalText(
        document: vscode.TextDocument,
        position: vscode.Position,
        options?: { useExactPosition?: boolean; replaceRange?: vscode.Range }
    ): string {
        if (options?.replaceRange) {
            // If we're replacing a specific range, get the text in that range
            return document.getText(options.replaceRange);
        }
        
        // For insertions, we need to capture what might be overwritten
        // This is tricky because the insertion logic is complex
        
        // Try to get the current line and any following content that might be affected
        const currentLine = Math.min(position.line, document.lineCount - 1);
        const lineText = document.lineAt(currentLine).text;
        
        // If we're at the end of a line, capture the rest of the line
        const restOfLine = lineText.slice(position.character);
        
        // Also check if there are subsequent lines that might be affected
        let captureEnd = currentLine;
        for (let i = currentLine + 1; i < Math.min(document.lineCount, currentLine + 3); i++) {
            const nextLineText = document.lineAt(i).text.trim();
            if (nextLineText === '' || nextLineText.startsWith('--')) {
                continue;
            }
            // If we find a line with content, it might be affected
            if (nextLineText.match(/^(exact|apply|rw|simp|sorry)/)) {
                captureEnd = i;
                break;
            }
        }
        
        // Create range from current position to end of potentially affected area
        const captureRange = new vscode.Range(
            position,
            new vscode.Position(captureEnd, document.lineAt(captureEnd).text.length)
        );
        
        return document.getText(captureRange);
    }

    /**
     * Rollback the operation for a specific goal
     */
    async rollbackOperation(document: vscode.TextDocument, goalIndex: number): Promise<boolean> {
        try {
            this.outputChannel.appendLine(`[ROLLBACK] Starting rollback for goal ${goalIndex}`);
            if (!this.historyManager.canRollback(goalIndex)) {
                this.outputChannel.appendLine(`[ROLLBACK] No operation available to rollback for goal ${goalIndex}`);
                vscode.window.showInformationMessage(`目标 ${goalIndex} 没有可回滚的操作`);
                return false;
            }

            // Validate that the operation is still valid
            const isValid = await this.historyManager.validateOperation(document, goalIndex);
            if (!isValid) {
                vscode.window.showWarningMessage('无法回滚：代码已被修改');
                return false;
            }

            const operation = this.historyManager.getOperation(goalIndex);
            if (!operation) {
                return false;
            }

            // Find the current by block range (which may be different from the original range)
            // We need to find the current complete by block and replace it entirely
            const currentPosition = operation.byBlockRange.start;
            
            // We need to use an external way to get current by block info
            // For now, let's use a simpler approach: find by scanning from the original position
            const currentByBlockRange = await this.findCurrentByBlockRange(document, operation.byBlockRange);
            
            if (!currentByBlockRange) {
                vscode.window.showErrorMessage('无法找到当前by块进行回滚');
                return false;
            }
            
            const currentByBlockContent = document.getText(currentByBlockRange);
            
            vscode.window.showInformationMessage(`🔄 当前by块: "${currentByBlockContent.substring(0, 50)}..."`);
            vscode.window.showInformationMessage(`🔄 原始by块: "${operation.originalByBlockContent.substring(0, 50)}..."`);
            
            // Replace the current complete by block with the original content
            const edit = new vscode.WorkspaceEdit();
            edit.replace(document.uri, currentByBlockRange, operation.originalByBlockContent);

            const success = await vscode.workspace.applyEdit(edit);

            if (success) {
                this.outputChannel.appendLine(`Rolled back ${operation.type} operation for goal ${goalIndex}`);
                this.historyManager.clearOperation(goalIndex);
                vscode.window.showInformationMessage(`成功回滚目标 ${goalIndex} 的操作`);
            } else {
                this.outputChannel.appendLine(`Failed to rollback operation for goal ${goalIndex}`);
            }

            return success;

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
    canRollbackGoal(goalIndex: number): boolean {
        return this.historyManager.canRollback(goalIndex);
    }

    /**
     * Check if rollback is available for a specific goal
     */
    canRollback(goalIndex: number): boolean {
        return this.historyManager.canRollback(goalIndex);
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
     * Decide the best insertion location:
     * 1) Replace the nearest 'sorry' token in the current proof block
     * 2) Otherwise, insert after a nearby 'by' with one indentation level
     * 3) Fallback: insert at current cursor
     */
    private computeBestInsertion(
        document: vscode.TextDocument,
        position: vscode.Position,
        rawText: string
    ): { kind: 'replace'; range: vscode.Range; text: string } | { kind: 'insert'; position: vscode.Position; text: string } {
        const sorryRegex = /\b(?:sorry|admit)\b/;
        const editorCfg = vscode.workspace.getConfiguration('editor', document.uri);
        const tabSize = editorCfg.get<number>('tabSize', 2);
        const insertSpaces = editorCfg.get<boolean>('insertSpaces', true);
        const indentUnit = insertSpaces ? ' '.repeat(Math.max(1, tabSize)) : '\t';

        // Search forward up to 200 lines for 'sorry'
        const maxScan = 200;
        const totalLines = document.lineCount;

        const makeIndented = (indent: string, text: string) => {
            // Apply indent to every non-empty line
            return text
                .split('\n')
                .map(line => (line.length > 0 ? indent + line : line))
                .join('\n');
        };

        // Helper to check a line for 'sorry' token and produce a replace range
        const checkLineForSorry = (lineNum: number) => {
            if (lineNum < 0 || lineNum >= totalLines) return undefined as undefined | { kind: 'replace'; range: vscode.Range; text: string };
            const line = document.lineAt(lineNum);
            const match = line.text.match(sorryRegex);
            if (!match || match.index == null) return undefined;
            const start = new vscode.Position(lineNum, match.index);
            const end = new vscode.Position(lineNum, match.index + match[0].length);
            const indent = line.text.slice(0, line.firstNonWhitespaceCharacterIndex);
            const text = makeIndented(indent, rawText);
            return { kind: 'replace', range: new vscode.Range(start, end), text } as const;
        };

        // 1) If the cursor is within a by-block and on a line after 'by', prefer inserting as the next line with one indent
        const cmLine = document.lineAt(position.line);
        const byBlock = this.findByBlockLight(document, position);
        if (byBlock && position.line >= byBlock.startLine && position.line <= byBlock.endLine) {
            const editorCfg = vscode.workspace.getConfiguration('editor', document.uri);
            const tabSize = editorCfg.get<number>('tabSize', 2);
            const insertSpaces = editorCfg.get<boolean>('insertSpaces', true);
            const indentUnit = insertSpaces ? ' '.repeat(Math.max(1, tabSize)) : '\t';
            const indentStr = ' '.repeat(byBlock.indentLevel) + indentUnit;
            const text = makeIndented(indentStr, rawText);
            // insert at beginning of current line if on code, otherwise at next line start
            const insertLine = position.character === 0 ? position.line : position.line;
            return { kind: 'insert', position: new vscode.Position(insertLine, 0), text } as const;
        }

        // 2) Look for a recent 'by' to place after, and ensure we are inside a proof block
        const byRegex = /\bby\b/;
        for (let delta = 0; delta <= 30; delta++) {
            const ln = position.line - delta;
            if (ln < 0) break;
            const line = document.lineAt(ln);
            if (byRegex.test(line.text)) {
                // Determine insertion line just after 'by' and any blank/comment lines
                let insertLine = ln + 1;
                while (insertLine < totalLines) {
                    const nl = document.lineAt(insertLine);
                    const t = nl.text.trim();
                    if (sorryRegex.test(nl.text)) break; // insert before a sorry
                    if (t.length === 0) { insertLine++; continue; } // skip blanks
                    if (t.startsWith('--')) { insertLine++; continue; } // skip comments
                    break; // stop before first real code line
                }
                // Choose indent: one indent unit deeper than the 'by' line
                const byIndent = line.text.slice(0, line.firstNonWhitespaceCharacterIndex);
                const indentStr = byIndent + indentUnit;
                const text = makeIndented(indentStr, rawText);
                const insertPos = new vscode.Position(insertLine, 0);
                return { kind: 'insert', position: insertPos, text } as const;
            }
        }

        // 3) Fallback: insert at cursor with current line indent
        const curLine = document.lineAt(position.line);
        const curIndent = curLine.text.slice(0, curLine.firstNonWhitespaceCharacterIndex);
        const text = makeIndented(curIndent, rawText);
        return { kind: 'insert', position, text } as const;
    }

    // Lightweight by-block finder for indentation and bounds only
    private findByBlockLight(document: vscode.TextDocument, position: vscode.Position): { startLine: number; endLine: number; indentLevel: number } | null {
        const byRegex = /\bby\b/;
        const total = document.lineCount;
        // search up for a line containing 'by'
        for (let ln = position.line; ln >= Math.max(0, position.line - 60); ln--) {
            const line = document.lineAt(ln);
            const m = line.text.match(byRegex);
            if (m && m.index != null) {
                const indent = line.firstNonWhitespaceCharacterIndex;
                // scan down to find end line (first non-empty non-comment with indent <= by indent)
                let end = ln;
                for (let dn = ln + 1; dn < Math.min(total, ln + 200); dn++) {
                    const l = document.lineAt(dn);
                    const t = l.text.trim();
                    if (t.length === 0 || t.startsWith('--')) { continue; }
                    const ind = l.firstNonWhitespaceCharacterIndex;
                    if (ind <= indent) { break; }
                    end = dn;
                }
                return { startLine: ln + 1, endLine: end, indentLevel: indent };
            }
        }
        return null;
    }

    /**
     * Generate a unique hypothesis name near the insertion point.
     * Prefers h, h1, h2, ... avoiding collisions with existing 'have <id> :'.
     */
    private computeUniqueHypName(document: vscode.TextDocument, position: vscode.Position): string {
        const nameRegex = /\bhave\s+([a-zA-Z_][\w']*)\s*:/g;
        const taken = new Set<string>();
        const total = document.lineCount;
        const scanStart = Math.max(0, position.line - 300);
        const scanEnd = Math.min(total - 1, position.line + 300);
        for (let ln = scanStart; ln <= scanEnd; ln++) {
            const text = document.lineAt(ln).text;
            let m: RegExpExecArray | null;
            nameRegex.lastIndex = 0;
            while ((m = nameRegex.exec(text)) !== null) {
                taken.add(m[1]);
            }
        }
        const base = 'h_annotated_';
        if (!taken.has(base)) return base + '1';
        let idx = 1;
        while (taken.has(base + idx)) idx++;
        return base + idx;
    }

    /**
     * Heuristically decide if the current proof block is already completed.
     * Consider completed if there is no 'sorry' and the line before 'end of block' looks like 'exact _' or 'qed-like'.
     * To keep simple, we only check absence of 'sorry' within a limited window backward from the cursor.
     */
    private isProofBlockComplete(document: vscode.TextDocument, position: vscode.Position): boolean {
        const window = 200;
        const sorryRegex = /\b(?:sorry|admit)\b/;
        const endLine = position.line;
        const startLine = Math.max(0, endLine - window);
        for (let ln = startLine; ln <= endLine; ln++) {
            const text = document.lineAt(ln).text;
            if (sorryRegex.test(text)) return true;
        }
        return false;
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

    /**
     * Find the current by block range by scanning from a position
     */
    private async findCurrentByBlockRange(document: vscode.TextDocument, originalRange: vscode.Range): Promise<vscode.Range | null> {
        const byRegex = /\bby\b/;
        const total = document.lineCount;
        
        // Look for the by block that starts at or near the original range start
        // The original range start should be the 'by' keyword line
        const searchStartLine = originalRange.start.line;
        
        // Check if there's still a 'by' at the original position
        if (searchStartLine < total) {
            const originalLine = document.lineAt(searchStartLine);
            if (byRegex.test(originalLine.text)) {
                // Found the 'by' at original position, now find the current end of this by block
                const byIndent = originalLine.firstNonWhitespaceCharacterIndex;
                
                let byEndLine = searchStartLine;
                for (let ln = searchStartLine + 1; ln < Math.min(total, searchStartLine + 100); ln++) {
                    const line = document.lineAt(ln);
                    const text = line.text.trim();
                    
                    // Skip empty lines and comments
                    if (text === '' || text.startsWith('--')) {
                        continue;
                    }
                    
                    const indent = line.firstNonWhitespaceCharacterIndex;
                    if (indent <= byIndent) {
                        // Found a line at same or less indentation, this is the end
                        break;
                    }
                    
                    byEndLine = ln;
                }
                
                // Create range from start of by line to end of last line in block
                const startPos = new vscode.Position(searchStartLine, 0);
                const endLine = document.lineAt(byEndLine);
                const endPos = new vscode.Position(byEndLine, endLine.text.length);
                
                return new vscode.Range(startPos, endPos);
            }
        }
        
        return null;
    }

    dispose(): void {
        this.outputChannel.dispose();
        this.historyManager.dispose();
    }
}