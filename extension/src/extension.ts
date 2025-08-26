import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import { LeanClientService } from './services/leanClient';
import { CodeModifierService } from './services/codeModifier';
import { TranslationService } from './services/translationService';
import { CursorModeManager } from './services/cursorModeManager';
import { ProofGoal, UserFeedback } from './types';
import { CursorMode } from './types/cursorModes';

/**
 * Main extension entry point
 * Implements Paperproof-style architecture with vscode-lean4 integration
 */
export function activate(context: vscode.ExtensionContext) {
    console.log('MathEye Proof Builder is now active!');

    const leanClient = new LeanClientService();
    const codeModifier = new CodeModifierService();
    const translationService = new TranslationService();
    const cursorModeManager = new CursorModeManager(context);
    const outputChannel = vscode.window.createOutputChannel("MathEye");
    const config = () => vscode.workspace.getConfiguration();
    const logLevel = () => (config().get<string>('matheye.logLevel', 'error')) as 'off'|'error'|'info'|'debug';
    const debounceMs = () => config().get<number>('matheye.updateDebounceMs', 250);
    const logDebug = (msg: string) => { if (logLevel() === 'debug') outputChannel.appendLine(msg); };
    const logInfo = (msg: string) => { if (logLevel() !== 'off' && logLevel() !== 'error') outputChannel.appendLine(msg); };
    const logError = (msg: string) => { if (logLevel() !== 'off') outputChannel.appendLine(msg); };

    // Cache heavy web assets once per activation
    const cachedAssets = getLocalAssets();
    
    // Global state for webview panel
    let currentPanel: vscode.WebviewPanel | undefined = undefined;
    let currentEditor: vscode.TextEditor | undefined = undefined;
    let currentGoals: ProofGoal[] = [];
    let currentPosition: vscode.Position | undefined = undefined;
    let positionLocked: boolean = false;

    // Register command: Start Proof Builder
    let startProofBuilderCommand = vscode.commands.registerCommand('matheye.startProofBuilder', async () => {
        const editor = vscode.window.activeTextEditor;
        if (!editor) {
            vscode.window.showErrorMessage('No active editor found');
            return;
        }

        if (editor.document.languageId !== 'lean4') {
            vscode.window.showWarningMessage('MathEye works with Lean 4 files only');
            return;
        }

        // Check if Lean server is ready
        const isReady = await leanClient.isLeanServerReady();
        if (!isReady) {
            vscode.window.showErrorMessage('Lean server is not ready. Please wait for Lean to initialize.');
            return;
        }

        logInfo('Starting MathEye Proof Builder...');

        try {
            // Get proof goals at current cursor position
            const position = editor.selection.active;
            const response = await leanClient.getProofGoals(position, editor.document);
            
            logInfo(`Found ${response.goals.length} proof goals`);

            // Create or update webview panel for user interaction
            currentEditor = editor;
            currentGoals = response.goals;
            currentPosition = position;
            const getState = () => ({ goals: currentGoals, positionLocked, lockedPosition: currentPosition });
            currentPanel = createProofGoalsPanel(context, getState, async (message) => {
                // Handle feedback using latest editor, goals and cursor position
                const editorNow = vscode.window.activeTextEditor ?? currentEditor;
                if (!editorNow) {
                    vscode.window.showErrorMessage('No active editor to apply feedback');
                    return;
                }
                const posNow = editorNow.selection?.active ?? currentPosition;
                if (!posNow) {
                    vscode.window.showErrorMessage('No valid cursor position');
                    return;
                }
                // Log incoming feedback for debugging
                outputChannel.appendLine(`[Feedback] action=${(message as any)?.action}, goalIndex=${(message as any)?.goalIndex}`);

                if (message.action === 'toggleLock') {
                    positionLocked = !positionLocked;
                    if (positionLocked) {
                        // Immediately lock to current selection to avoid a 0-goal blink
                        currentPosition = posNow;
                        if (currentPanel) {
                            try { currentPanel.webview.postMessage({ type: 'lockState', locked: true, line: currentPosition.line }); } catch {}
                        }
                        updateProofGoals(editorNow);
                        // Then normalize asynchronously to the tactic's insertion point and refresh once more
                        leanClient.getInsertionPoint(posNow, editorNow.document).then((insPos) => {
                            currentPosition = insPos;
                            vscode.window.showInformationMessage(`已固定光标于第 ${insPos.line + 1} 行`);
                            updateProofGoals(editorNow);
                        });
                    } else {
                        vscode.window.showInformationMessage('已解除光标固定');
                        if (currentPanel) {
                            try {
                                currentPanel.webview.postMessage({ type: 'lockState', locked: false, line: null });
                            } catch {}
                        }
                        updateProofGoals(editorNow);
                    }
                    return;
                }
                if (message.action === 'cycleCursorMode') {
                    logInfo('Cycle cursor mode requested');
                    const nextMode = cursorModeManager.cycleMode();
                    const config = cursorModeManager.getModeConfig(nextMode);
                    vscode.window.showInformationMessage(
                        `光标模式切换为: ${config.label} - ${config.description}`
                    );
                    // 刷新目标显示
                    await updateProofGoals(editorNow);
                    return;
                }
                if (message.action === 'toggleTranslation') {
                    logInfo('Toggle translation requested');
                    try {
                        const enabled = await translationService.toggleTranslation();
                        const statusMsg = enabled ? '已开启目标翻译' : '已关闭目标翻译';
                        logInfo(`Translation ${enabled ? 'enabled' : 'disabled'}`);
                        vscode.window.showInformationMessage(statusMsg);
                        if (currentPanel) {
                            try {
                                currentPanel.webview.postMessage({ 
                                    type: 'translationState', 
                                    enabled: enabled 
                                });
                            } catch (e) {
                                logError(`Failed to post translation state message: ${e}`);
                            }
                        }
                        // Refresh goals to trigger translation if enabled
                        updateProofGoals(editorNow);
                    } catch (error) {
                        logError(`Toggle translation failed: ${error}`);
                        vscode.window.showErrorMessage(`翻译开关失败: ${error}`);
                    }
                    return;
                }
                if (!currentGoals || currentGoals.length === 0) {
                    vscode.window.showInformationMessage('当前证明已完成，无需插入。');
                    return;
                }
                const goalsNow = currentGoals;
                // 使用“逻辑光标”对齐 by 块规则，避免实际插入点造成的不一致
                const logicalResult = cursorModeManager.calculateLogicalCursor(posNow, editorNow.document);
                const deleteRange = cursorModeManager.calculateDeleteRange(posNow, editorNow.document);
                
                const rawAction = (message.action || '').trim();
                const act = rawAction === 'admit' ? 'admit' : 'deny';
                
                outputChannel.appendLine(`[Feedback] resolvedAction=${act}, logicalCursor=(${logicalResult.position.line},${logicalResult.position.character}), mode=${logicalResult.mode}`);
                if (deleteRange) {
                    outputChannel.appendLine(`[Feedback] deleteRange=[(${deleteRange.start.line},${deleteRange.start.character}) to (${deleteRange.end.line},${deleteRange.end.character})]`);
                }
                
                // 使用修改后的applyFeedback方法，传递删除范围和逻辑光标信息
                codeModifier.applyFeedbackWithLogicalCursor(
                    editorNow.document, 
                    goalsNow, 
                    { goalIndex: message.goalIndex, action: act }, 
                    logicalResult,
                    deleteRange
                );
            }, () => {
                // Clear global panel state when disposed
                currentPanel = undefined;
            }, currentPanel, translationService, cursorModeManager, cachedAssets);
            
            logDebug(`Panel created/updated. currentPanel exists: ${!!currentPanel}`);

        } catch (error) {
            const errorMsg = `Failed to start proof builder: ${error}`;
            logError(errorMsg);
            vscode.window.showErrorMessage(errorMsg);
        }
    });

    // Register command: Analyze Proof Goals (simplified version)
    // Register command: Toggle Cursor Mode
    let cycleCursorModeCommand = vscode.commands.registerCommand('matheye.cycleCursorMode', async () => {
        const nextMode = cursorModeManager.cycleMode();
        const config = cursorModeManager.getModeConfig(nextMode);
        vscode.window.showInformationMessage(
            `光标模式切换为: ${config.label} - ${config.description}`
        );
        
        // 如果webview已打开，刷新显示
        if (currentPanel && currentEditor) {
            await updateProofGoals(currentEditor);
        }
    });

    let analyzeCommand = vscode.commands.registerCommand('matheye.analyzeProofGoals', async () => {
        const editor = vscode.window.activeTextEditor;
        if (!editor || editor.document.languageId !== 'lean4') {
            vscode.window.showWarningMessage('Please open a Lean 4 file');
            return;
        }

        try {
            const position = editor.selection.active;
            const response = await leanClient.getProofGoals(position, editor.document);
            
            const message = `Analysis complete: Found ${response.goals.length} proof goals`;
            vscode.window.showInformationMessage(message);
            
            outputChannel.appendLine(message);
            response.goals.forEach((goal, index) => {
                outputChannel.appendLine(`${index + 1}. ${goal.name || 'unnamed'}: ${goal.type}`);
            });
            outputChannel.show();

        } catch (error) {
            vscode.window.showErrorMessage(`Analysis failed: ${error}`);
        }
    });

    // Paperproof-style cursor monitoring with cancellation token
    let cancellationToken: vscode.CancellationTokenSource | null = null;

    const updateProofGoals = async (textEditor: vscode.TextEditor | undefined) => {
        // Enhanced debugging to understand what's happening
        logDebug(`updateProofGoals called`);
        logDebug(`currentPanel exists: ${!!currentPanel}`);
        logDebug(`textEditor exists: ${!!textEditor}`);
        logDebug(`textEditor language: ${textEditor?.document?.languageId || 'none'}`);
        
        // Only update if we have an active panel (like Paperproof)
        if (!currentPanel || !textEditor) {
            logDebug("No panel or editor, skipping update");
            return;
        }

        if (textEditor.document.languageId !== 'lean4') {
            logDebug("Not Lean4 file, skipping update");
            return;
        }

        // Cancel previous request if still running
        if (cancellationToken) {
            cancellationToken.cancel();
        }
        cancellationToken = new vscode.CancellationTokenSource();

        try {
            // 计算逻辑光标位置
            const actualPosition = positionLocked && currentPosition ? currentPosition : textEditor.selection.active;
            const logicalResult = cursorModeManager.calculateLogicalCursor(actualPosition, textEditor.document);
            const position = logicalResult.position;
            const cursorModeLabelNow = cursorModeManager.getModeConfig(logicalResult.mode).label;
            logDebug(`Updating goals at line ${position.line}, char ${position.character}`);
            
            const response = await leanClient.getProofGoals(position, textEditor.document);
            
            // Check if request was cancelled
            if (cancellationToken.token.isCancellationRequested) {
                logDebug("Request was cancelled");
                return;
            }
            
            // Update cached state and webview content
            currentEditor = textEditor;
            
            // Show goals immediately; kick off translations asynchronously so UI is never blocked
            currentGoals = response.goals.map(g => ({ ...g }));
            if (translationService.isTranslationEnabled()) {
                logDebug('Translation enabled, start async translations...');
                const versionAtStart = Date.now();
                const goalsSnapshot = currentGoals.map(g => g.type);
                Promise.all(goalsSnapshot.map(async (goalText, idx) => {
                    try {
                        const result = await translationService.translateGoal(goalText);
                        // Only apply if panel still exists and goal matches snapshot at same index
                        const editorNow = vscode.window.activeTextEditor;
                        if (!currentPanel || !editorNow) return;
                        if (!currentGoals[idx] || currentGoals[idx].type !== goalText) return;
                        currentGoals[idx] = {
                            ...currentGoals[idx],
                            translation: result.translated,
                            translationError: result.error
                        };
                        try {
                          currentPanel.webview.postMessage({
                            type: 'goalsData',
                            goals: currentGoals,
                            translationEnabled: translationService.isTranslationEnabled(),
                            positionLocked,
                            lockedLine: currentPosition?.line ?? null,
                            cursorModeLabel: cursorModeLabelNow
                          });
                        } catch {}
                    } catch (error) {
                        logError(`Translation failed for goal: ${error}`);
                    }
                })).catch(() => {});
            }
            
            currentPosition = position;
            try {
                // Non-blocking incremental update via postMessage
                try {
                  currentPanel.webview.postMessage({
                    type: 'goalsData',
                    goals: currentGoals,
                    translationEnabled: translationService.isTranslationEnabled(),
                    positionLocked,
                    lockedLine: currentPosition?.line ?? null,
                    cursorModeLabel: cursorModeLabelNow
                  });
                } catch {}
            } catch (e) {
                logDebug(`Webview update failed (maybe disposed): ${e}`);
                currentPanel = undefined;
                return;
            }
            logInfo(`Updated: Found ${response.goals.length} proof goals at line ${position.line}`);
            
        } catch (error) {
            logError(`Failed to update goals: ${error}`);
        }
    };

    // Add event listeners (like Paperproof)
    let debounceTimer: NodeJS.Timeout | undefined;
    const triggerUpdate = (editor?: vscode.TextEditor) => {
        if (debounceTimer) clearTimeout(debounceTimer);
        debounceTimer = setTimeout(() => updateProofGoals(editor ?? vscode.window.activeTextEditor), debounceMs());
    };

    const onActiveEditorChange = vscode.window.onDidChangeActiveTextEditor((editor) => triggerUpdate(editor));
    const onSelectionChange = vscode.window.onDidChangeTextEditorSelection((event) => {
        triggerUpdate(event.textEditor);
    });

    // Also update when the document changes (to follow re-elaboration timing)
    const onTextChange = vscode.workspace.onDidChangeTextDocument(() => {
        triggerUpdate(vscode.window.activeTextEditor);
    });

    context.subscriptions.push(
        startProofBuilderCommand,
        cycleCursorModeCommand,
        analyzeCommand,
        onActiveEditorChange,
        onSelectionChange,
        onTextChange,
        leanClient,
        translationService,
        outputChannel
    );
}

/**
 * Create or update webview panel for proof goals interaction
 */
function createProofGoalsPanel(
    context: vscode.ExtensionContext,
    getState: () => { goals: ProofGoal[]; positionLocked: boolean; lockedPosition?: vscode.Position },
    onFeedback: (message: UserFeedback) => Promise<void>,
    onDisposed: () => void,
    existingPanel?: vscode.WebviewPanel,
    translationService?: TranslationService,
    cursorModeManager?: CursorModeManager,
    assets?: { katexCssHref: string; markedJsHref: string; domPurifyJsHref: string; katexJsHref: string; autoRenderJsHref: string }
): vscode.WebviewPanel {
    // Reuse existing panel if available
    const panel = existingPanel || vscode.window.createWebviewPanel(
        'matheyeProofBuilder',
        'MathEye Proof Builder',
        vscode.ViewColumn.Two,
        {
            enableScripts: true,
            retainContextWhenHidden: true
        }
    );

    // Set webview content (once)
    const s0 = getState();
    panel.webview.html = getWebviewContent(
        s0.goals,
        s0.positionLocked,
        s0.lockedPosition,
        translationService?.isTranslationEnabled(),
        cursorModeManager?.getCurrentMode(),
        assets ?? getLocalAssets(),
        panel.webview.cspSource
    );

    // Handle messages from webview
    panel.webview.onDidReceiveMessage((message) => {
        console.log('Webview message received:', message);
        onFeedback(message);
    }, undefined, context.subscriptions);

    // Refresh when panel becomes visible again (incremental render)
    panel.onDidChangeViewState(() => {
        // Trigger a refresh using latest known state
        const s = getState();
        try {
          panel.webview.postMessage({
            type: 'goalsData',
            goals: s.goals,
            translationEnabled: translationService?.isTranslationEnabled() ?? false,
            positionLocked: s.positionLocked,
            lockedLine: s.lockedPosition?.line ?? null
          });
        } catch {}
    }, null, context.subscriptions);

    // Handle panel disposal
    panel.onDidDispose(() => {
        try { onDisposed(); } catch {}
    }, null, context.subscriptions);

    return panel;
}

/**
 * Generate HTML content for webview
 */
function getWebviewContent(
    goals: ProofGoal[],
    positionLocked: boolean,
    lockedPos?: vscode.Position,
    translationEnabled?: boolean,
    cursorMode?: CursorMode,
    assets?: { katexCssHref: string; markedJsHref: string; domPurifyJsHref: string; katexJsHref: string; autoRenderJsHref: string },
    cspSource?: string
): string {
    const lockLabel = positionLocked ? '▶ 解除固定' : '⏸ 固定光标';
    const translationLabel = translationEnabled ? '🌐 关闭翻译' : '🌐 开启翻译';
    
    // 获取光标模式标签
    const cursorModeLabel = (() => {
        switch (cursorMode) {
            case CursorMode.CURRENT: return '📍 当前光标';
            case CursorMode.BY_START: return '🎯 By块开始';
            case CursorMode.BY_END: return '🏁 By块末尾';
            default: return '📍 当前光标';
        }
    })();
    const lockInfo = positionLocked && lockedPos ? `<span class="lock-info">已固定于第 ${lockedPos.line + 1} 行</span>` : '';
    const goalsHtml = goals.map((goal, index) => {
        const hasTranslation = !!translationEnabled;
        return `
            <div class="goal">
                <div class="goal-header">
                    <span class="goal-name">${goal.name || `Goal ${index + 1}`}</span>
                </div>
                <div class="goal-content">
                    <div class="goal-section">
                        <div class="goal-section-title">Lean 表示：</div>
                        <div class="goal-type">${goal.type}</div>
                    </div>
                    ${hasTranslation ? `
                        <div class="goal-section">
                            <div class="goal-section-title">自然语言：</div>
                            <div class="goal-translation ${goal.translationError ? 'error' : ''}" ${goal.translationError ? '' : `data-raw="${encodeURIComponent(goal.translation ?? (goal.translationError ? '' : '翻译中...'))}"`}>
                                ${goal.translationError || (goal.translation ? '' : '翻译中...')}
                            </div>
                        </div>
                    ` : ''}
                </div>
                <div class="actions">
                    <button onclick="sendFeedback(${index}, 'admit')" class="btn admit">✓ 正确</button>
                    <button onclick="sendFeedback(${index}, 'deny')" class="btn deny">✗ 错误</button>
                </div>
            </div>
        `;
    }).join('');

    return `
        <!DOCTYPE html>
        <html lang="en">
        <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <meta http-equiv="Content-Security-Policy" content="default-src 'none'; img-src ${cspSource ?? 'data:'} data:; style-src 'unsafe-inline' ${cspSource ?? ''}; script-src 'unsafe-inline' ${cspSource ?? ''}; font-src ${cspSource ?? ''} data:;">
            <title>MathEye Proof Builder</title>
            <style>
                body {
                    font-family: var(--vscode-font-family);
                    color: var(--vscode-foreground);
                    background: var(--vscode-editor-background);
                    padding: 20px;
                }
                .goal {
                    border: 1px solid var(--vscode-panel-border);
                    margin: 10px 0;
                    padding: 15px;
                    border-radius: 5px;
                    border-left: 4px solid var(--vscode-textLink-foreground);
                }
                .goal-header {
                    font-size: 16px;
                    margin-bottom: 10px;
                }
                .goal-name {
                    font-weight: bold;
                    color: var(--vscode-symbolIcon-variableForeground);
                }
                .goal-content {
                    margin: 10px 0;
                }
                .goal-section {
                    margin: 8px 0;
                }
                .goal-section-title {
                    font-weight: bold;
                    color: var(--vscode-textLink-foreground);
                    margin-bottom: 4px;
                    font-size: 14px;
                }
                .goal-type {
                    color: var(--vscode-symbolIcon-typeForeground);
                    font-family: monospace;
                    background: var(--vscode-textCodeBlock-background);
                    padding: 8px;
                    border-radius: 3px;
                    white-space: pre-wrap;
                    word-break: break-all;
                }
                .goal-translation {
                    color: var(--vscode-foreground);
                    background: var(--vscode-input-background);
                    border: 1px solid var(--vscode-input-border);
                    padding: 8px;
                    border-radius: 3px;
                    line-height: 1.4;
                }
                .goal-translation.error {
                    color: var(--vscode-errorForeground);
                    background: var(--vscode-inputValidation-errorBackground);
                    border-color: var(--vscode-inputValidation-errorBorder);
                }
                .actions {
                    margin: 10px 0;
                }
                .btn {
                    margin: 0 5px;
                    padding: 8px 16px;
                    border: none;
                    border-radius: 3px;
                    cursor: pointer;
                    font-size: 14px;
                }
                .btn.admit { background: #28a745; color: white; }
                .btn.deny { background: #dc3545; color: white; }
                .btn:hover { opacity: 0.8; }
                .btn.lock { background: #6c757d; color: white; margin-left: 10px; }
                .btn.cursor-mode { background: #17a2b8; color: white; margin-right: 10px; }
                .btn.translation { background: #007acc; color: white; margin-right: 10px; }
                .toolbar { display: flex; align-items: center; justify-content: space-between; }
                .lock-info { color: var(--vscode-descriptionForeground); margin-left: 10px; }
                h1 {
                    color: var(--vscode-editor-foreground);
                    border-bottom: 1px solid var(--vscode-panel-border);
                    padding-bottom: 10px;
                }
            </style>
            ${assets ? `<style>${assets.katexCssHref}</style>` : ''}
        </head>
        <body>
            <div class="toolbar">
              <h1>MathEye 证明构建器</h1>
              <div>
                <button onclick="cycleCursorMode()" class="btn cursor-mode">
                  ${cursorModeLabel}
                </button>
                <button onclick="toggleTranslation()" class="btn translation">${translationLabel}</button>
                <button onclick="toggleLock()" class="btn lock">${lockLabel}</button>
                ${lockInfo}
              </div>
            </div>
            <p>共发现 ${goals.length} 个待证目标。</p>
            ${goals.length === 0 ? `<p>当前光标位置没有待证目标。移动光标或编辑代码后将自动刷新。</p>` : `<p>请对每个目标给出反馈：</p>`}
            <div id="goals-root">
            ${goalsHtml}
            </div>
            
            ${assets ? `<script>${assets.markedJsHref}</script>` : ''}
            ${assets ? `<script>${assets.domPurifyJsHref}</script>` : ''}
            ${assets ? `<script>${assets.katexJsHref}</script>` : ''}
            ${assets ? `<script>${assets.autoRenderJsHref}</script>` : ''}
            <script>
                console.log('Webview script loading...');
                const vscode = acquireVsCodeApi();
                console.log('vscode API acquired:', !!vscode);
                
                function sendFeedback(goalIndex, action) {
                    console.log('sendFeedback called:', goalIndex, action);
                    vscode.postMessage({
                        goalIndex: goalIndex,
                        action: action
                    });
                }
                function toggleLock() {
                    console.log('toggleLock called');
                    vscode.postMessage({ goalIndex: -1, action: 'toggleLock' });
                }
                function cycleCursorMode() {
                    console.log('cycleCursorMode called');
                    vscode.postMessage({ goalIndex: -1, action: 'cycleCursorMode' });
                }
                function toggleTranslation() {
                    console.log('toggleTranslation clicked');
                    vscode.postMessage({ goalIndex: -1, action: 'toggleTranslation' });
                }
                
                // Test if buttons exist
                document.addEventListener('DOMContentLoaded', function() {
                    console.log('DOM loaded');
                    const translationBtn = document.querySelector('.btn.translation');
                    console.log('Translation button found:', !!translationBtn);
                    if (translationBtn) {
                        console.log('Translation button text:', translationBtn.textContent);
                    }
                });
                function buildGoalHtml(goal, index, translationEnabled) {
                  const hasTranslation = !!translationEnabled;
                  const isError = !!goal.translationError;
                  const rawText = goal.translation ? goal.translation : (isError ? '' : '翻译中...');
                  const dataRaw = (!isError && hasTranslation) ? ('data-raw="' + encodeURIComponent(rawText) + '"') : '';
                  const translationBlock = hasTranslation
                    ? ('<div class="goal-section">'
                      + '<div class="goal-section-title">自然语言：</div>'
                      + '<div class="goal-translation ' + (isError ? 'error' : '') + '" ' + dataRaw + '>'
                      + (goal.translationError || (goal.translation ? '' : '翻译中...'))
                      + '</div>'
                      + '</div>')
                    : '';
                  const goalName = goal.name ? goal.name : ('Goal ' + (index + 1));
                  return (
                    '<div class="goal">'
                    + '<div class="goal-header">'
                    + '<span class="goal-name">' + goalName + '</span>'
                    + '</div>'
                    + '<div class="goal-content">'
                    + '<div class="goal-section">'
                    + '<div class="goal-section-title">Lean 表示：</div>'
                    + '<div class="goal-type">' + goal.type + '</div>'
                    + '</div>'
                    + translationBlock
                    + '</div>'
                    + '<div class="actions">'
                    + '<button class="btn admit" data-idx="' + index + '">✓ 正确</button>'
                    + '<button class="btn deny" data-idx="' + index + '">✗ 错误</button>'
                    + '</div>'
                    + '</div>'
                  );
                }

                function renderGoalsData(data) {
                  const root = document.getElementById('goals-root');
                  if (!root) return;
                  const goals = Array.isArray(data.goals) ? data.goals : [];
                  const html = goals.map((g, i) => buildGoalHtml(g, i, !!data.translationEnabled)).join('');
                  root.innerHTML = html;
                  // update toolbar lock state label/info if provided
                  if (typeof data.positionLocked === 'boolean') {
                    const btn = document.querySelector('.btn.lock');
                    if (btn) btn.textContent = data.positionLocked ? '▶ 解除固定' : '⏸ 固定光标';
                    const info = document.querySelector('.lock-info');
                    if (info) info.textContent = (data.positionLocked && data.lockedLine != null) ? ('已固定于第 ' + (data.lockedLine + 1) + ' 行') : '';
                  }
                  if (typeof data.translationEnabled === 'boolean') {
                    const tbtn = document.querySelector('.btn.translation');
                    if (tbtn) tbtn.textContent = data.translationEnabled ? '🌐 关闭翻译' : '🌐 开启翻译';
                  }
                  // Update cursor mode label if provided
                  if (typeof data.cursorModeLabel === 'string') {
                    const cbtn = document.querySelector('.btn.cursor-mode');
                    if (cbtn) cbtn.textContent = data.cursorModeLabel;
                  }

                  // Attach click handlers (avoid inline onclick to prevent quoting issues)
                  root.querySelectorAll('.btn.admit').forEach((btn) => {
                    btn.addEventListener('click', () => {
                      const idx = parseInt(btn.getAttribute('data-idx') || '0', 10);
                      sendFeedback(idx, 'admit');
                    });
                  });
                  root.querySelectorAll('.btn.deny').forEach((btn) => {
                    btn.addEventListener('click', () => {
                      const idx = parseInt(btn.getAttribute('data-idx') || '0', 10);
                      sendFeedback(idx, 'deny');
                    });
                  });
                  renderTranslations();
                }

                window.addEventListener('message', function(event) {
                  const msg = event.data;
                  if (msg && msg.type === 'lockState') {
                    const btn = document.querySelector('.btn.lock');
                    if (btn) btn.textContent = msg.locked ? '▶ 解除固定' : '⏸ 固定光标';
                    const info = document.querySelector('.lock-info');
                    if (info) info.textContent = (msg.locked && msg.line != null) ? ('已固定于第 ' + (msg.line + 1) + ' 行') : '';
                  }
                  if (msg && msg.type === 'translationState') {
                    const btn = document.querySelector('.btn.translation');
                    if (btn) btn.textContent = msg.enabled ? '🌐 关闭翻译' : '🌐 开启翻译';
                  }
                  if (msg && msg.type === 'goalsData') {
                    renderGoalsData(msg);
                  }
                });

                function renderTranslations() {
                  const blocks = document.querySelectorAll('.goal-translation');
                  blocks.forEach((el) => {
                    if (el.classList.contains('error')) return;
                    const rawEnc = el.getAttribute('data-raw') || '';
                    if (!rawEnc) return;
                    let raw = '';
                    try { raw = decodeURIComponent(rawEnc); } catch { raw = ''; }
                    if (!raw) return;
                    try {
                      const html = (window.marked && window.marked.parse) ? window.marked.parse(raw) : raw;
                      const safeHtml = (window.DOMPurify && window.DOMPurify.sanitize) ? window.DOMPurify.sanitize(html) : html;
                      el.innerHTML = safeHtml;
                      if (window.renderMathInElement) {
                        window.renderMathInElement(el, {
                          delimiters: [
                            { left: '$$', right: '$$', display: true },
                            { left: '$', right: '$', display: false },
                            { left: '\\(', right: '\\)', display: false },
                            { left: '\\[', right: '\\]', display: true }
                          ],
                          throwOnError: false
                        });
                      }
                    } catch (e) {
                      console.warn('Render translation failed', e);
                    }
                  });
                }

                document.addEventListener('DOMContentLoaded', renderTranslations);
                setTimeout(renderTranslations, 200);
            </script>
        </body>
        </html>
    `;
}

export function deactivate() {
    console.log('MathEye Proof Builder deactivated');
}

// Build local URIs for KaTeX fonts/CSS and local scripts to avoid CDN
function getLocalAssets(): {
    katexCssHref: string; markedJsHref: string; domPurifyJsHref: string; katexJsHref: string; autoRenderJsHref: string
} {
    // __dirname points to extension/out at runtime; go up to extension/
    const base = path.join(__dirname, '..');
    const nodeRoot = path.join(base, 'node_modules');
    const read = (p: string) => fs.readFileSync(p, 'utf8');
    const fontsDir = path.join(nodeRoot, 'katex', 'dist', 'fonts');
    let css = read(path.join(nodeRoot, 'katex', 'dist', 'katex.min.css'));
    // Inline KaTeX fonts as data URIs to avoid CSP/scheme fetches
    css = css.replace(/url\(([^)]+)\)/g, (m, p1) => {
        let ref = String(p1).trim().replace(/^['\"]|['\"]$/g, '');
        if (!ref.startsWith('fonts/')) return m;
        try {
            const fontPath = path.join(fontsDir, ref.replace(/^fonts\//, ''));
            const ext = path.extname(fontPath).toLowerCase();
            const mime = ext === '.woff2' ? 'font/woff2'
                : ext === '.woff' ? 'font/woff'
                : ext === '.ttf' ? 'font/ttf'
                : ext === '.otf' ? 'font/otf'
                : 'application/octet-stream';
            const bin = fs.readFileSync(fontPath);
            const b64 = bin.toString('base64');
            return `url('data:${mime};base64,${b64}')`;
        } catch {
            return m;
        }
    });
    const marked = read(path.join(nodeRoot, 'marked', 'marked.min.js'));
    const purify = read(path.join(nodeRoot, 'dompurify', 'dist', 'purify.min.js'));
    const katex = read(path.join(nodeRoot, 'katex', 'dist', 'katex.min.js'));
    const auto = read(path.join(nodeRoot, 'katex', 'dist', 'contrib', 'auto-render.min.js'));
    return { katexCssHref: css, markedJsHref: marked, domPurifyJsHref: purify, katexJsHref: katex, autoRenderJsHref: auto };
}