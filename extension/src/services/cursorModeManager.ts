import * as vscode from 'vscode';
import { CursorMode, CursorModeConfig, ByBlockInfo, LogicalCursorResult } from '../types/cursorModes';
import { LeanClientService } from './leanClient';

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

    constructor(private context: vscode.ExtensionContext, private leanClient: LeanClientService) {
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
    async calculateLogicalCursor(
        actualCursor: vscode.Position,
        document: vscode.TextDocument,
        mode?: CursorMode
    ): Promise<LogicalCursorResult> {
        const targetMode = mode || this.currentMode;
        // Ask server for current by-block/tactic range
        const byBlockRange = await this.leanClient.getByBlockRange(actualCursor, document);
        const byBlock: ByBlockInfo | undefined = byBlockRange.success && byBlockRange.range ? {
            byPosition: actualCursor,
            startPosition: byBlockRange.range.start,
            endPosition: byBlockRange.range.end,
            indentLevel: 0
        } : undefined;

        // 当前模式：位置为实际光标，但也返回 byBlock 以便后续逻辑使用
        if (targetMode === CursorMode.CURRENT) {
            return { position: actualCursor, byBlock, mode: targetMode };
        }

        if (!byBlock) {
            // 未找到 by 块，则退回实际光标
            return { position: actualCursor, byBlock: undefined, mode: targetMode };
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

        return { position: logicalPosition, byBlock, mode: targetMode };
    }

    /**
     * 查找包含指定位置的by块
     */
    // Legacy regex path removed; server is the source of truth.

    /**
     * 查找by块的结束位置
     */
    // End-finder removed; server RPC provides accurate range.

    /**
     * 计算删除范围（从逻辑光标到by块末尾）
     */
    async calculateDeleteRange(
        actualCursor: vscode.Position,
        document: vscode.TextDocument,
        mode?: CursorMode
    ): Promise<vscode.Range | undefined> {
        const logicalResult = await this.calculateLogicalCursor(actualCursor, document, mode);
        
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
