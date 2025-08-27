import * as vscode from 'vscode';

/**
 * Represents a single operation that can be undone
 */
export interface HistoryOperation {
    type: 'admit' | 'deny';
    goalIndex: number;                  // 关联的目标索引
    byBlockRange: vscode.Range;         // 整个by block的范围
    originalByBlockContent: string;     // 整个by block的原始内容
    timestamp: number;
    documentUri: string;
}

/**
 * Manages history for rollback functionality in have by blocks
 */
export class HistoryManager {
    private operationsByGoal: Map<number, HistoryOperation[]> = new Map();
    private outputChannel: vscode.OutputChannel;

    constructor() {
        this.outputChannel = vscode.window.createOutputChannel("MathEye History");
    }

    /**
     * Record a new operation that can be rolled back
     */
    recordOperation(operation: HistoryOperation): void {
        const goalIndex = operation.goalIndex;
        if (!this.operationsByGoal.has(goalIndex)) {
            this.operationsByGoal.set(goalIndex, []);
        }
        this.operationsByGoal.get(goalIndex)!.push(operation);
        this.outputChannel.appendLine(
            `Recorded ${operation.type} operation for goal ${goalIndex} (${this.operationsByGoal.get(goalIndex)!.length} operations total)`
        );
    }

    /**
     * Check if there's an operation that can be rolled back for a specific goal
     */
    canRollback(goalIndex: number): boolean {
        const operations = this.operationsByGoal.get(goalIndex);
        return operations ? operations.length > 0 : false;
    }

    /**
     * Get the operation for a specific goal
     */
    getOperation(goalIndex: number): HistoryOperation | null {
        const operations = this.operationsByGoal.get(goalIndex);
        return operations && operations.length > 0 ? operations[operations.length - 1] : null;
    }

    /**
     * Clear the operation for a specific goal (called after successful rollback)
     */
    clearOperation(goalIndex: number): void {
        const operations = this.operationsByGoal.get(goalIndex);
        if (operations && operations.length > 0) {
            const clearedOperation = operations.pop();
            this.outputChannel.appendLine(
                `Cleared operation ${clearedOperation?.type} for goal ${goalIndex}, remaining: ${operations.length}`
            );
            
            // 如果没有剩余操作，删除整个数组
            if (operations.length === 0) {
                this.operationsByGoal.delete(goalIndex);
            }
        }
    }

    /**
     * Check if the current document state matches the recorded operation
     */
    async validateOperation(document: vscode.TextDocument, goalIndex: number): Promise<boolean> {
        const operations = this.operationsByGoal.get(goalIndex);
        if (!operations || operations.length === 0) {
            return false;
        }
        
        const operation = operations[operations.length - 1]; // Get the latest operation

        // Check if document URI matches
        if (document.uri.toString() !== operation.documentUri) {
            return false;
        }

        try {
            // Simply check if the by block range is still valid
            const currentRange = operation.byBlockRange;
            if (currentRange.start.line >= document.lineCount || currentRange.end.line >= document.lineCount) {
                return false;
            }
            
            // The operation is valid if the range exists
            return true;
            
        } catch (error) {
            this.outputChannel.appendLine(`Validation error: ${error}`);
            return false;
        }
    }

    /**
     * Find the entire by block range containing the cursor position
     */
    async findByBlockRange(document: vscode.TextDocument, position: vscode.Position): Promise<{range: vscode.Range, content: string} | null> {
        const byRegex = /by/;
        const total = document.lineCount;
        
        vscode.window.showInformationMessage(`🔍 DEBUG: 搜索by块，从位置 ${position.line}:${position.character}`);
        
        // Search upward for 'by' keyword
        let byStartLine: number | null = null;
        for (let ln = position.line; ln >= Math.max(0, position.line - 50); ln--) {
            const line = document.lineAt(ln);
            if (ln >= position.line - 5 && ln <= position.line) {
                vscode.window.showInformationMessage(`🔍 第${ln}行: "${line.text}"`);
            }
            if (byRegex.test(line.text)) {
                byStartLine = ln;
                vscode.window.showInformationMessage(`✅ 找到'by'在第${ln}行`);
                break;
            }
        }
        
        if (byStartLine === null) {
            vscode.window.showInformationMessage(`❌ 没有找到'by'关键字`);
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