import * as vscode from 'vscode';
import { CursorMode, CursorModeConfig, ByBlockInfo, LogicalCursorResult } from '../types/cursorModes';

/**
 * 光标模式管理器
 */
export class CursorModeManager {
    private currentMode: CursorMode = CursorMode.CURRENT;
    private readonly modeConfigs: Record<CursorMode, CursorModeConfig> = {
        [CursorMode.CURRENT]: {
            mode: CursorMode.CURRENT,
            label: '📍 当前光标',
            icon: '📍',
            description: '使用实际光标位置'
        },
        [CursorMode.BY_START]: {
            mode: CursorMode.BY_START,
            label: '🎯 By块开始',
            icon: '🎯',
            description: '逻辑光标在by块开始'
        },
        [CursorMode.BY_END]: {
            mode: CursorMode.BY_END,
            label: '🏁 By块末尾',
            icon: '🏁',
            description: '逻辑光标在by块末尾'
        }
    };

    constructor(private context: vscode.ExtensionContext) {
        // 从配置中恢复上次的模式
        this.currentMode = this.context.globalState.get('matheye.cursorMode', CursorMode.CURRENT);
    }

    /**
     * 获取当前光标模式
     */
    getCurrentMode(): CursorMode {
        return this.currentMode;
    }

    /**
     * 设置光标模式
     */
    setMode(mode: CursorMode): void {
        this.currentMode = mode;
        this.context.globalState.update('matheye.cursorMode', mode);
    }

    /**
     * 切换到下一个模式
     */
    cycleMode(): CursorMode {
        const modes = Object.values(CursorMode);
        const currentIndex = modes.indexOf(this.currentMode);
        const nextIndex = (currentIndex + 1) % modes.length;
        const nextMode = modes[nextIndex];
        this.setMode(nextMode);
        return nextMode;
    }

    /**
     * 获取模式配置
     */
    getModeConfig(mode?: CursorMode): CursorModeConfig {
        return this.modeConfigs[mode || this.currentMode];
    }

    /**
     * 获取所有模式配置
     */
    getAllModeConfigs(): CursorModeConfig[] {
        return Object.values(this.modeConfigs);
    }

    /**
     * 计算逻辑光标位置
     */
    calculateLogicalCursor(
        actualCursor: vscode.Position,
        document: vscode.TextDocument,
        mode?: CursorMode
    ): LogicalCursorResult {
        const targetMode = mode || this.currentMode;

        // 始终尝试查找 by 块，供删除范围等逻辑使用
        const byBlock = this.findByBlock(actualCursor, document);

        // 当前模式：位置为实际光标，但也返回 byBlock 以便后续逻辑使用
        if (targetMode === CursorMode.CURRENT) {
            return {
                position: actualCursor,
                byBlock,
                mode: targetMode
            };
        }

        if (!byBlock) {
            // 未找到 by 块，则退回实际光标
            return {
                position: actualCursor,
                byBlock: undefined,
                mode: targetMode
            };
        }

        let logicalPosition: vscode.Position;

        switch (targetMode) {
            case CursorMode.BY_START:
                logicalPosition = byBlock.startPosition;
                break;
            case CursorMode.BY_END:
                logicalPosition = byBlock.endPosition;
                break;
            default:
                logicalPosition = actualCursor;
        }

        return {
            position: logicalPosition,
            byBlock,
            mode: targetMode
        };
    }

    /**
     * 查找包含指定位置的by块
     */
    private findByBlock(position: vscode.Position, document: vscode.TextDocument): ByBlockInfo | undefined {
        const byRegex = /\bby\b/;
        const currentLine = position.line;
        
        // 从当前位置向上搜索by关键字（搜索范围：30行）
        for (let delta = 0; delta <= 30; delta++) {
            const lineNum = currentLine - delta;
            if (lineNum < 0) break;
            
            const line = document.lineAt(lineNum);
            const match = line.text.match(byRegex);
            
            if (match && match.index !== undefined) {
                const byPosition = new vscode.Position(lineNum, match.index + match[0].length);
                const indentLevel = line.firstNonWhitespaceCharacterIndex;
                
                // 查找by块的结束位置
                const endPosition = this.findByBlockEnd(byPosition, document, indentLevel);
                
                // 检查当前位置是否在这个by块范围内
                if (position.line >= lineNum && position.line <= endPosition.line) {
                    return {
                        byPosition,
                        startPosition: new vscode.Position(lineNum, match.index + match[0].length),
                        endPosition,
                        indentLevel
                    };
                }
            }
        }
        
        return undefined;
    }

    /**
     * 查找by块的结束位置
     */
    private findByBlockEnd(byPosition: vscode.Position, document: vscode.TextDocument, byIndentLevel: number): vscode.Position {
        const totalLines = document.lineCount;
        let lastContentLine = byPosition.line;
        
        // 从by位置向下搜索，找到相同或更浅缩进级别的非空行作为结束位置
        for (let lineNum = byPosition.line + 1; lineNum < totalLines; lineNum++) {
            const line = document.lineAt(lineNum);
            const text = line.text.trim();
            
            // 跳过空行和注释
            if (text.length === 0 || text.startsWith('--')) {
                continue;
            }
            
            const lineIndentLevel = line.firstNonWhitespaceCharacterIndex;
            
            // 如果发现相同或更浅的缩进级别，说明by块结束了
            if (lineIndentLevel <= byIndentLevel) {
                break;
            }
            
            lastContentLine = lineNum;
        }
        
        // 返回最后一个有内容行的末尾位置
        const lastLine = document.lineAt(lastContentLine);
        return new vscode.Position(lastContentLine, lastLine.text.length);
    }

    /**
     * 计算删除范围（从逻辑光标到by块末尾）
     */
    calculateDeleteRange(
        actualCursor: vscode.Position,
        document: vscode.TextDocument,
        mode?: CursorMode
    ): vscode.Range | undefined {
        const logicalResult = this.calculateLogicalCursor(actualCursor, document, mode);
        
        if (!logicalResult.byBlock) {
            return undefined;
        }
        
        // 删除范围：从逻辑光标位置到by块末尾
        return new vscode.Range(
            logicalResult.position,
            logicalResult.byBlock.endPosition
        );
    }
}