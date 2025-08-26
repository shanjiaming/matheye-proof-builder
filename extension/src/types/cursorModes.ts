/**
 * 三种光标模式定义
 */
export enum CursorMode {
    /** 当前模式：使用实际光标位置 */
    CURRENT = 'current',
    /** By块开始模式：逻辑上认为光标在当前by块的by之后开始 */
    BY_START = 'by_start', 
    /** By块末尾模式：逻辑上认为光标在当前by块的末尾 */
    BY_END = 'by_end'
}

/**
 * 光标模式配置
 */
export interface CursorModeConfig {
    mode: CursorMode;
    label: string;
    icon: string;
    description: string;
}

/**
 * By块信息
 */
export interface ByBlockInfo {
    /** by关键字位置 */
    byPosition: import('vscode').Position;
    /** by块开始位置（by之后） */
    startPosition: import('vscode').Position;
    /** by块结束位置 */
    endPosition: import('vscode').Position;
    /** 缩进级别 */
    indentLevel: number;
}

/**
 * 逻辑光标计算结果
 */
export interface LogicalCursorResult {
    /** 计算得出的逻辑光标位置 */
    position: import('vscode').Position;
    /** 当前by块信息（如果存在） */
    byBlock?: ByBlockInfo;
    /** 使用的光标模式 */
    mode: CursorMode;
}