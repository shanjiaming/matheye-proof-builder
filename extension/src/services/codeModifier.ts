import * as vscode from 'vscode';
import { ProofGoal, UserFeedback } from '../types';

/**
 * Service for modifying Lean source code based on user feedback on proof goals
 */
export class CodeModifierService {
    private outputChannel: vscode.OutputChannel;
    private nextVariableIndex: number = 1;

    constructor() {
        this.outputChannel = vscode.window.createOutputChannel("MathEye CodeModifier");
    }

    /**
     * Apply user feedback to proof goals by inserting code at cursor position
     */
    async applyFeedback(
        document: vscode.TextDocument,
        goals: ProofGoal[],
        feedback: UserFeedback,
        position: vscode.Position,
        options?: { useExactPosition?: boolean }
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
            if (options?.useExactPosition) {
                const indent = this.computeIndentForAppendAtTail(document, position);
                const curLine = document.lineAt(Math.min(position.line, document.lineCount - 1));
                // In exact-tail mode, start on a new line when position is not at column 0.
                // This avoids appending after code on the same line like "... by sorry  have ...".
                const needsNewline = position.character > 0;
                const text = (needsNewline ? "\n" : "") + this.applyIndent(indent, rawText);
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

        // 1) Do NOT replace sorry anymore; treat sorry as a completion token

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

    dispose(): void {
        this.outputChannel.dispose();
    }
}