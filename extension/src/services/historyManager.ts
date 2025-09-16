import * as vscode from 'vscode';

/**
 * 表示一次可回滚的操作（记录 by-block 精确范围与原始内容，避免任何字符串级编辑）
 */
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
 * 管理回滚历史（生产路径统一依赖 Lean RPC，AST-only；此处不做任何字符串级修改）
 */
export class HistoryManager {
  private operationsByDoc: Map<string, HistoryOperation[]> = new Map();
  private outputChannel: vscode.OutputChannel;

  constructor() {
    this.outputChannel = vscode.window.createOutputChannel('MathEye History');
  }

  /** 记录一次可回滚的操作 */
  recordOperation(operation: HistoryOperation): void {
    const key = operation.documentUri;
    if (!this.operationsByDoc.has(key)) this.operationsByDoc.set(key, []);
    this.operationsByDoc.get(key)!.push(operation);
    this.outputChannel.appendLine(
      `Recorded ${operation.type} op for doc ${key} (stack size: ${this.operationsByDoc.get(key)!.length})`
    );
  }

  /** 当前文档是否存在可回滚操作 */
  canRollbackForDocument(document: vscode.TextDocument): boolean {
    const ops = this.operationsByDoc.get(document.uri.toString());
    return !!(ops && ops.length > 0);
  }

  /**
   * 同步快速检查：当前 by-block 内容如果仍包含插入片段，或块范围未坍塌，则允许回滚
   */
  canRollbackSafelyInBlock(document: vscode.TextDocument, blockRange: vscode.Range): boolean {
    const ops = this.operationsByDoc.get(document.uri.toString());
    if (!ops || ops.length === 0) return false;
    const content = document.getText(blockRange);
    for (let i = ops.length - 1; i >= 0; i--) {
      const op = ops[i];
      if (content.includes(op.insertedText)) return true;
      if (
        op.byBlockRange.start.line === blockRange.start.line &&
        op.byBlockRange.end.line === blockRange.end.line
      )
        return true;
    }
    return false;
  }

  /** 获取最后一次操作 */
  getLastOperationForDocument(document: vscode.TextDocument): HistoryOperation | null {
    const ops = this.operationsByDoc.get(document.uri.toString());
    return ops && ops.length > 0 ? ops[ops.length - 1] : null;
  }

  /** 清除最后一次操作（成功回滚后调用） */
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

  /** 更新最后一次操作的字段（用于写回最终范围/文本等） */
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

  /** 严格校验：当前块中必须仍出现插入片段 */
  async validateOperationInBlock(
    document: vscode.TextDocument,
    blockRange: vscode.Range
  ): Promise<boolean> {
    return this.canRollbackSafelyInBlock(document, blockRange);
  }

  // 旧版字符串扫描 by-block 的方法已删除：统一使用 Lean RPC `getByBlockRange` 获取范围

  dispose(): void {
    this.outputChannel.dispose();
  }
}

