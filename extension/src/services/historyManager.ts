import * as vscode from 'vscode';

/**
 * Represents a single operation that can be undone
 */
export interface AnchorPathItem { kind: string; idx: number }

export interface HistoryOperation {
    // core intent
    type: 'admit' | 'deny';
    goalIndex: number;
    // storage: full by-block range and original text content
    byBlockRange: vscode.Range;
    originalByBlockContent: string;
    // extra diagnostics kept for eligibility checks
    insertedText: string;
    byBlockStartLine: number;
    absStartLine: number;
    absStartChar: number;
    absEndLine: number;
    absEndChar: number;
    timestamp: number;
    documentUri: string;
}

/**
 * Manages history for rollback functionality in have by blocks
 */
export class HistoryManager {
    private operationsByDoc: Map<string, HistoryOperation[]> = new Map();
    private outputChannel: vscode.OutputChannel;

    constructor() {
        this.outputChannel = vscode.window.createOutputChannel("MathEye History");
    }

    /**
     * Record a new operation that can be rolled back
     */
    recordOperation(operation: HistoryOperation): void {
        const key = operation.documentUri;
        if (!this.operationsByDoc.has(key)) {
            this.operationsByDoc.set(key, []);
        }
        this.operationsByDoc.get(key)!.push(operation);
        this.outputChannel.appendLine(
            `Recorded ${operation.type} op for doc ${key} (stack size: ${this.operationsByDoc.get(key)!.length})`
        );
    }

    /**
     * Check if there's an operation that can be rolled back for a specific goal
     */
    canRollbackForDocument(document: vscode.TextDocument): boolean {
        const ops = this.operationsByDoc.get(document.uri.toString());
        return !!(ops && ops.length > 0);
    }

    /**
     * Check if there's a rollback operation available and if it's likely still valid (synchronous check)
     */
    canRollbackSafelyInBlock(document: vscode.TextDocument, blockRange: vscode.Range): boolean {
        const ops = this.operationsByDoc.get(document.uri.toString());
        if (!ops || ops.length === 0) return false;
        const content = document.getText(blockRange);
        // 简化安全检查：只要当前块仍然包含插入片段或块范围未坍塌，就允许回滚
        for (let i = ops.length - 1; i >= 0; i--) {
            const op = ops[i];
            if (content.includes(op.insertedText)) return true;
            if (op.byBlockRange.start.line === blockRange.start.line && op.byBlockRange.end.line === blockRange.end.line) return true;
        }
        return false;
    }

    /**
     * Get the operation for a specific goal
     */
    getLastOperationForDocument(document: vscode.TextDocument): HistoryOperation | null {
        const ops = this.operationsByDoc.get(document.uri.toString());
        return ops && ops.length > 0 ? ops[ops.length - 1] : null;
    }

    /**
     * Clear the operation for a specific goal (called after successful rollback)
     */
    clearLastOperationForDocument(document: vscode.TextDocument): void {
        const key = document.uri.toString();
        const ops = this.operationsByDoc.get(key);
        if (ops && ops.length > 0) {
            const clearedOperation = ops.pop();
            this.outputChannel.appendLine(
                `Cleared operation ${clearedOperation?.type} for doc ${key}, remaining: ${ops.length}`
            );
            if (ops.length === 0) this.operationsByDoc.delete(key);
        }
    }

    /**
     * Update fields of the last operation for this document (used to sync final ranges/text after post-edits)
     */
    updateLastOperationForDocument(
        document: vscode.TextDocument,
        updater: (op: HistoryOperation) => void
    ): void {
        const key = document.uri.toString();
        const ops = this.operationsByDoc.get(key);
        if (!ops || ops.length === 0) return;
        const last = ops[ops.length - 1];
        updater(last);
    }

    /**
     * Check if the current document state matches the recorded operation
     */
    async validateOperationInBlock(document: vscode.TextDocument, blockRange: vscode.Range): Promise<boolean> {
        // Strict validation: exact insertedText must exist in current block content
        return this.canRollbackSafelyInBlock(document, blockRange);
    }

    /**
     * @deprecated 已弃用：请改用 Lean RPC `getByBlockRange`。此方法仅为历史保留，不应在生产路径调用。
     * Find the entire by block range containing the cursor position
     */
    async findByBlockRange(document: vscode.TextDocument, position: vscode.Position): Promise<{range: vscode.Range, content: string} | null> {
        const byRegex = /by/;
        const total = document.lineCount;
        // Debug logging to output channel only
        this.outputChannel.appendLine(`[DEBUG] 搜索by块，从位置 ${position.line}:${position.character}`);
        
        // Search upward for 'by' keyword
        let byStartLine: number | null = null;
        for (let ln = position.line; ln >= Math.max(0, position.line - 50); ln--) {
            const line = document.lineAt(ln);
            if (ln >= position.line - 5 && ln <= position.line) {
                this.outputChannel.appendLine(`[DEBUG] 第${ln}行: ${JSON.stringify(line.text)}`);
            }
            if (byRegex.test(line.text)) {
                byStartLine = ln;
                this.outputChannel.appendLine(`[DEBUG] 找到 'by' 在第 ${ln} 行`);
                break;
            }
        }
        
        if (byStartLine === null) {
            this.outputChannel.appendLine(`[DEBUG] 没有找到 'by' 关键字`);
            return null;
        }
        
        // Find the end of the by block (first line with same or less indentation than the 'by' line)
        const byLine = document.lineAt(byStartLine);
        const byIndent = byLine.firstNonWhitespaceCharacterIndex;
        
        let byEndLine = byStartLine;
        for (let ln = byStartLine + 1; ln < Math.min(total, byStartLine + 100); ln++) {
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
        const startPos = new vscode.Position(byStartLine, 0);
        const endLine = document.lineAt(byEndLine);
        const endPos = new vscode.Position(byEndLine, endLine.text.length);
        const range = new vscode.Range(startPos, endPos);
        const content = document.getText(range);
        
        return { range, content };
    }

    dispose(): void {
        this.outputChannel.dispose();
    }
}
