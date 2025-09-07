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
    vscode.window.showInformationMessage('DEBUG: 扩展已重新加载');

    const outputChannel = vscode.window.createOutputChannel("MathEye");

    // Preflight: ensure Lean side is built before user interaction in Dev Host
    (async () => {
        try {
            const cp = require('child_process') as typeof import('child_process');
            const fs = require('fs') as typeof import('fs');
            // Robustly resolve repo root: prefer extension/../ (two levels up from out/)
            const candidates = [
                path.resolve(__dirname, '..', '..'),            // <repo>
                path.resolve(__dirname, '..', '..', '..'),      // <repo>/..
                path.resolve(__dirname, '.'),                    // extension/out
            ];
            let repoRootGuess = candidates.find(p => fs.existsSync(path.join(p, 'MathEye.lean')));
            if (!repoRootGuess) repoRootGuess = path.resolve(__dirname, '..', '..');
            outputChannel.appendLine(`[Preflight] repoRoot=${repoRootGuess}`);
            // Run `lake build MathEye` at repo root; tolerate environments without lake
            outputChannel.appendLine('[Preflight] lake build MathEye...');
            await new Promise<void>((resolve) => {
                const p = cp.spawn('lake', ['build', 'MathEye'], { cwd: repoRootGuess, shell: true });
                p.stdout?.on('data', (d: any) => outputChannel.appendLine(String(d)));
                p.stderr?.on('data', (d: any) => outputChannel.appendLine(String(d)));
                p.on('exit', () => resolve());
                p.on('error', () => resolve());
            });
            // Try to restart Lean server if extension is present
            try { await vscode.commands.executeCommand('lean4.restartServer'); } catch {}

            // Developer convenience: auto-open a default test file under test_cases so你不必手动点开
            try {
                const testFile = path.join(repoRootGuess, 'test_cases', 'test_01_basic_theorem.lean');
                if (fs.existsSync(testFile)) {
                    const doc = await vscode.workspace.openTextDocument(testFile);
                    await vscode.window.showTextDocument(doc, { preview: false });
                }
            } catch {}
        } catch (e) {
            outputChannel.appendLine(`[Preflight] skipped or failed: ${e}`);
        }
    })();

    const isTest = process.env.MATHEYE_TEST_MODE === '1';
    const forceReal = process.env.MATHEYE_USE_REAL_RPC === '1';
    const useMock = isTest && !forceReal;
    const leanClient: LeanClientService = useMock
      ? new (require('./test/mockLeanClient').MockLeanClientService)()
      : new LeanClientService(outputChannel);
    const translationService = new TranslationService(outputChannel);
    const codeModifier = new CodeModifierService(outputChannel, leanClient);
    const cursorModeManager = new CursorModeManager(context, leanClient);
    
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

    // Register command: Insert have snippet via Lean RPC (AST-based)
    const insertHaveCmd = vscode.commands.registerCommand('matheye.insertHaveSnippet', async () => {
        const editor = vscode.window.activeTextEditor;
        if (!editor) return;
        if (!isTest && editor.document.languageId !== 'lean4') {
            vscode.window.showWarningMessage('This command works with Lean 4 files only');
            return;
        }
        vscode.window.showInformationMessage('Insert Have Snippet (free-form) 已禁用：请使用“Insert Have (Admit/Deny)”以保持 AST-only 精确编辑。');
    });

    // Quick actions: Insert have by action (admit/deny) via server AST path
    const insertHaveAdmit = vscode.commands.registerCommand('matheye.insertHaveAdmit', async () => {
        const editor = vscode.window.activeTextEditor; if (!editor) return;
        if (!isTest && editor.document.languageId !== 'lean4') return;
        try { require('fs').appendFileSync(require('path').resolve(__dirname, './ext_calls.log'), `insertHaveAdmit ${editor.document.uri} @ ${editor.selection.active.line}:${editor.selection.active.character}\n`); } catch {}
        // In real RPC mode, give Lean server a brief moment to be ready
        if (process.env.MATHEYE_USE_REAL_RPC === '1') {
            // 放宽等待窗口，避免VS Code测试宿主安装/激活lean4扩展的竞态
            for (let i = 0; i < 60; i++) {
                if (await leanClient.isLeanServerReady()) break;
                await new Promise(r => setTimeout(r, 200));
            }
        }
        // Ensure imports/macros first, then re-anchor
        await codeModifier.ensureImportsAndMacros(editor.document);
        // Try to anchor inside the exact by-block to avoid seam positions around '|' and '=>'
        let pos = editor.selection.active;
        let byRange: vscode.Range | undefined = undefined;
        let includeByOnSeq = false;
        try {
            // 重试等待 by/战术容器可用，避免刚载入时 infoTree 尚未就绪
            let br = await leanClient.getByBlockRange(pos, editor.document);
            for (let i = 0; i < 20 && (!br.success || !br.range); i++) {
                await new Promise(r => setTimeout(r, 150));
                br = await leanClient.getByBlockRange(pos, editor.document);
            }
            try {
                if (process.env.MATHEYE_TEST_MODE === '1') {
                    const p = require('path'); const fs = require('fs');
                    const logPath = p.resolve(__dirname, 'insert_debug.log');
                    fs.appendFileSync(logPath, `getByBlockRange success=${br.success} range=${br.range ? `[${br.range.start.line}:${br.range.start.character}-${br.range.end.line}:${br.range.end.character}]` : 'none'} isTactic=${br.isTacticContext} isTerm=${br.isTermContext} syntax=${(br as any).syntaxKind}\n`);
                }
            } catch {}
            if (br.success && br.range) {
                const kindStr = (br as any).syntaxKind || '';
                // Use precise context detection: only wrap with `by` in term context
                if (kindStr && !String(kindStr).startsWith('Lean.Parser.Tactic.')) {
                    // 容器是 term（如 byTactic）— 需要补 `by`
                    byRange = br.range;
                    includeByOnSeq = true;
                } else if (br.isTacticContext) {
                    // Already in tactic context - insert tactics directly (never include `by`)
                    if (br.isMatchAlt) {
                        // Inside match alternative - position after '=>'
                        const line = br.range.start.line;
                        const txt = editor.document.lineAt(line).text;
                        const arrow = txt.indexOf('=>');
                        if (arrow >= 0) {
                            const hasSpace = txt.slice(arrow + 2).startsWith(' ');
                            pos = new vscode.Position(line, arrow + 2 + (hasSpace ? 1 : 0));
                            const br2 = await leanClient.getByBlockRange(pos, editor.document);
                            byRange = br2.success ? br2.range : br.range;
                            includeByOnSeq = false; // tactic context
                        } else {
                            byRange = br.range;
                            includeByOnSeq = false; // tactic context
                        }
                    } else {
                        // Regular tactic context (inside by-block)
                        byRange = br.range;
                        includeByOnSeq = false; // tactic context
                    }
                } else {
                    // In term context - need to wrap with 'by'
                    byRange = br.range;
                    includeByOnSeq = true;
                }
            }
        } catch {}
        // Snap to canonical insertion point以避免缝隙；然后再次拉取 by 块范围（更稳定）
        try { pos = await leanClient.getInsertionPoint(pos, editor.document); } catch {}
        try {
            let br2 = await leanClient.getByBlockRange(pos, editor.document);
            for (let i = 0; i < 10 && (!br2.success || !br2.range); i++) {
                await new Promise(r => setTimeout(r, 120));
                br2 = await leanClient.getByBlockRange(pos, editor.document);
            }
            if (br2.success && br2.range) {
                const kindStr2 = (br2 as any).syntaxKind || '';
                if (kindStr2 && !String(kindStr2).startsWith('Lean.Parser.Tactic.')) {
                    byRange = br2.range;
                    includeByOnSeq = true;
                } else {
                    byRange = br2.range;
                    includeByOnSeq = false;
                }
            }
        } catch {}
        // 调用 RPC（短轮询直到成功或超时），避免刚载入时类型/路径未就绪
        let res = await leanClient.insertHaveByAction(pos, editor.document, 'admit', byRange, includeByOnSeq, true);
        try {
          if (process.env.MATHEYE_TEST_MODE === '1') {
            const p = require('path'); const fs = require('fs');
            const logPath = p.resolve(__dirname, 'insert_debug.log');
            const brs = byRange ? `[${byRange.start.line}:${byRange.start.character}-${byRange.end.line}:${byRange.end.character}]` : 'none';
            fs.appendFileSync(logPath, `admit@ ${pos.line}:${pos.character} byRange=${brs} includeBy=${includeByOnSeq} -> success=${res.success} range=${res.range ? `[${res.range.start.line}:${res.range.start.character}-${res.range.end.line}:${res.range.end.character}]` : 'none'} newText.len=${res.newText?.length ?? 0}\n`);
          }
        } catch {}
        // 不重试：失败即失败，避免不透明 fallback
        if (!res.success || !res.newText || !res.range) return;

        // 仅允许整篇替换：要求服务器返回整文件范围
        const wholeRangeReturned = res.range.start.line === 0 && res.range.start.character === 0 && res.range.end.line >= editor.document.lineCount - 1;
        if (!wholeRangeReturned) {
            throw new Error('服务器未返回整篇替换范围');
        }
        const we = new vscode.WorkspaceEdit();
        const fullRange = new vscode.Range(0, 0, editor.document.lineCount, 0);
        we.replace(editor.document.uri, fullRange, res.newText);
        await vscode.workspace.applyEdit(we);
    });
    const insertHaveDeny = vscode.commands.registerCommand('matheye.insertHaveDeny', async () => {
        const editor = vscode.window.activeTextEditor; if (!editor) return;
        if (!isTest && editor.document.languageId !== 'lean4') return;
        // In real RPC mode, give Lean server a brief moment to be ready
        if (process.env.MATHEYE_USE_REAL_RPC === '1') {
            // 放宽等待窗口，避免VS Code测试宿主安装/激活lean4扩展的竞态
            for (let i = 0; i < 60; i++) {
                if (await leanClient.isLeanServerReady()) break;
                await new Promise(r => setTimeout(r, 200));
            }
        }
        // Ensure imports/macros first, then re-anchor
        await codeModifier.ensureImportsAndMacros(editor.document);
        let pos = editor.selection.active;
        let byRange: vscode.Range | undefined = undefined;
        let includeByOnSeq = false;
        try {
            // 重试等待 by/战术容器可用，避免刚载入时 infoTree 尚未就绪
            let br = await leanClient.getByBlockRange(pos, editor.document);
            for (let i = 0; i < 20 && (!br.success || !br.range); i++) {
                await new Promise(r => setTimeout(r, 150));
                br = await leanClient.getByBlockRange(pos, editor.document);
            }
            if (br.success && br.range) {
                const kindStr = (br as any).syntaxKind || '';
                // Use precise context detection: only wrap with `by` in term context
                if (kindStr && !String(kindStr).startsWith('Lean.Parser.Tactic.')) {
                    byRange = br.range;
                    includeByOnSeq = true;
                } else if (br.isTacticContext) {
                    // Already in tactic context - insert tactics directly (never include `by`)
                    if (br.isMatchAlt) {
                        // Inside match alternative - position after '=>'
                        const line = br.range.start.line;
                        const txt = editor.document.lineAt(line).text;
                        const arrow = txt.indexOf('=>');
                        if (arrow >= 0) {
                            const hasSpace = txt.slice(arrow + 2).startsWith(' ');
                            pos = new vscode.Position(line, arrow + 2 + (hasSpace ? 1 : 0));
                            const br2 = await leanClient.getByBlockRange(pos, editor.document);
                            byRange = br2.success ? br2.range : br.range;
                            includeByOnSeq = false; // tactic context
                        } else {
                            byRange = br.range;
                            includeByOnSeq = false; // tactic context
                        }
                    } else {
                        // Regular tactic context (inside by-block)
                        byRange = br.range;
                        includeByOnSeq = false; // tactic context
                    }
                } else {
                    // In term context - need to wrap with 'by'
                    byRange = br.range;
                    includeByOnSeq = true;
                }
            }
        } catch {}
        // 容器就绪后再锚定一次，并再次获取 by 块范围
        try { pos = await leanClient.getInsertionPoint(pos, editor.document); } catch {}
        try {
            let br2 = await leanClient.getByBlockRange(pos, editor.document);
            for (let i = 0; i < 10 && (!br2.success || !br2.range); i++) {
                await new Promise(r => setTimeout(r, 120));
                br2 = await leanClient.getByBlockRange(pos, editor.document);
            }
            if (br2.success && br2.range) {
                const kindStr2 = (br2 as any).syntaxKind || '';
                if (kindStr2 && !String(kindStr2).startsWith('Lean.Parser.Tactic.')) {
                    byRange = br2.range;
                    includeByOnSeq = true;
                } else {
                    byRange = br2.range;
                    includeByOnSeq = false;
                }
            }
        } catch {}
        // 调用 RPC（短轮询直到成功或超时）
        let res = await leanClient.insertHaveByAction(pos, editor.document, 'deny', byRange, includeByOnSeq, true);
        try {
          if (process.env.MATHEYE_TEST_MODE === '1') {
            const p = require('path'); const fs = require('fs');
            const logPath = p.resolve(__dirname, 'insert_debug.log');
            const brs = byRange ? `[${byRange.start.line}:${byRange.start.character}-${byRange.end.line}:${byRange.end.character}]` : 'none';
            fs.appendFileSync(logPath, `deny@ ${pos.line}:${pos.character} byRange=${brs} includeBy=${includeByOnSeq} -> success=${res.success} range=${res.range ? `[${res.range.start.line}:${res.range.start.character}-${res.range.end.line}:${res.range.end.character}]` : 'none'} newText.len=${res.newText?.length ?? 0}\n`);
          }
        } catch {}
        // 不重试：失败即失败
        if (!res.success || !res.newText || !res.range) return;

        // 仅允许整篇替换：要求服务器返回整文件范围
        const wholeRangeReturned = res.range.start.line === 0 && res.range.start.character === 0 && res.range.end.line >= editor.document.lineCount - 1;
        if (!wholeRangeReturned) {
            throw new Error('服务器未返回整篇替换范围');
        }
        const we = new vscode.WorkspaceEdit();
        const fullRange = new vscode.Range(0, 0, editor.document.lineCount, 0);
        we.replace(editor.document.uri, fullRange, res.newText);
        await vscode.workspace.applyEdit(we);
    });

    // Testing/utility: apply admit through CodeModifierService to record history
    const insertHaveAdmitWithHistory = vscode.commands.registerCommand('matheye.insertHaveAdmitWithHistory', async () => {
        const editor = vscode.window.activeTextEditor; if (!editor) return;
        if (!isTest && editor.document.languageId !== 'lean4') return;
        await codeModifier.ensureImportsAndMacros(editor.document);
        const posNow = editor.selection.active;
        const logical = await cursorModeManager.calculateLogicalCursor(posNow, editor.document);
        const delRange = await cursorModeManager.calculateDeleteRange(posNow, editor.document);
        const goalsResp = await leanClient.getProofGoals(posNow, editor.document);
        await codeModifier.applyFeedbackWithLogicalCursor(editor.document, goalsResp.goals as any, { goalIndex: 0, action: 'admit' }, logical, delRange);
    });

    // Testing/utility: rollback last operation in current document
    const rollbackCurrentBlock = vscode.commands.registerCommand('matheye.rollbackCurrentBlock', async () => {
        const editor = vscode.window.activeTextEditor; if (!editor) return;
        await codeModifier.rollbackOperation(editor.document);
    });

    // Register command: Start Proof Builder
    let startProofBuilderCommand = vscode.commands.registerCommand('matheye.startProofBuilder', async () => {
        const editor = vscode.window.activeTextEditor;
        if (!editor) {
            vscode.window.showErrorMessage('No active editor found');
            return;
        }

        if (!isTest && editor.document.languageId !== 'lean4') {
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
                            try { currentPanel.webview.postMessage({ type: 'lockState', locked: true, line: currentPosition.line }); } catch (e) {}
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
                            } catch (e) {}
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
                    // 立刻强制刷新一次（避免等待焦点/选择变动）
                    lastUpdateKey = null as any;
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
                if (message.action === 'rollback') {
                    logInfo(`Rollback current by-block requested`);
                    try {
                        vscode.window.showInformationMessage(`回滚当前 by 块请求已收到，正在处理...`);
                        const success = await codeModifier.rollbackOperation(editorNow.document);
                        if (success) {
                            logInfo('Rollback completed successfully');
                            updateProofGoals(editorNow);
                        }
                    } catch (error) {
                        logError(`Rollback failed: ${error}`);
                        vscode.window.showErrorMessage(`回滚失败: ${error}`);
                    }
                    return;
                }
                if (!currentGoals || currentGoals.length === 0) {
                    vscode.window.showInformationMessage('当前证明已完成，无需插入。');
                    return;
                }
                const goalsNow = currentGoals;
                // 使用"逻辑光标"对齐 by 块规则，避免实际插入点造成的不一致
                const logicalResult = await cursorModeManager.calculateLogicalCursor(posNow, editorNow.document);
                const deleteRange = await cursorModeManager.calculateDeleteRange(posNow, editorNow.document);
                
                const rawAction = (message.action || '').trim();
                const act = rawAction === 'admit' ? 'admit' : 'deny';
                
                outputChannel.appendLine(`[Feedback] resolvedAction=${act}, logicalCursor=(${logicalResult.position.line},${logicalResult.position.character}), mode=${logicalResult.mode}`);
                if (deleteRange) {
                    outputChannel.appendLine(`[Feedback] deleteRange=[(${deleteRange.start.line},${deleteRange.start.character}) to (${deleteRange.end.line},${deleteRange.end.character})]`);
                }
                
                // 使用修改后的applyFeedback方法，传递删除范围和逻辑光标信息
                await codeModifier.applyFeedbackWithLogicalCursor(
                    editorNow.document, 
                    goalsNow, 
                    { goalIndex: message.goalIndex, action: act }, 
                    logicalResult,
                    deleteRange
                );
                
                // 代码插入完成后，立即更新goals显示
                // Proactively update canRollback based on actual selection to avoid UI lag
                try {
                    const selPos = (vscode.window.activeTextEditor ?? editorNow).selection.active;
                    const can = await codeModifier.canRollbackInCurrentBlock(editorNow.document, selPos);
                    if (currentPanel) {
                        try { currentPanel.webview.postMessage({ type: 'canRollbackState', canRollback: can }); } catch (e) {}
                    }
                } catch (e) {}
                setTimeout(() => updateProofGoals(editorNow), 100);
            }, () => {
                // Clear global panel state when disposed
                currentPanel = undefined;
            }, currentPanel, translationService, cursorModeManager, cachedAssets, codeModifier);
            
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

    // (Removed) AST round-trip debug command
    const astTestCommand = vscode.commands.registerCommand('matheye.testASTRoundTrip', async () => {
        vscode.window.showInformationMessage('AST test command removed in AST-only workflow.');
    });

    // Paperproof-style cursor monitoring with cancellation token
    let cancellationToken: vscode.CancellationTokenSource | null = null;

    let isUpdating = false;
    let lastUpdateKey: string | null = null;
    let lastTranslatedGoalsKey: string | null = null;
    const updateProofGoals = async (textEditor: vscode.TextEditor | undefined) => {
        // Only update if we have both a panel and an editor
        if (!currentPanel || !textEditor) return;
        if (isUpdating) return;

        if (textEditor.document.languageId !== 'lean4') {
            // logDebug("Not Lean4 file, skipping update");
            return;
        }

        // Include cursor mode in key so UI updates when mode changes even if cursor/selection doesn't
        const modeKey = cursorModeManager.getCurrentMode();
        const key = `${textEditor.document.uri.toString()}@${textEditor.document.version}:${textEditor.selection.active.line}:${textEditor.selection.active.character}:mode=${modeKey}`;
        if (key === lastUpdateKey) return;
        lastUpdateKey = key;

        // Cancel previous request if still running
        if (cancellationToken) {
            cancellationToken.cancel();
        }
        cancellationToken = new vscode.CancellationTokenSource();
        isUpdating = true;

        try {
            // 计算逻辑光标位置
            const actualPosition = positionLocked && currentPosition ? currentPosition : textEditor.selection.active;
            const logicalResult = await cursorModeManager.calculateLogicalCursor(actualPosition, textEditor.document);
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
                const goalsSnapshot = currentGoals.map(g => g.type).join('\n---\n');
                if (goalsSnapshot !== lastTranslatedGoalsKey) {
                    lastTranslatedGoalsKey = goalsSnapshot;
                    const arr = currentGoals.map(g => g.type);
                    Promise.all(arr.map(async (goalText, idx) => {
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
                            cursorModeLabel: cursorModeLabelNow,
                            // Use actual selection for canRollback, not logical cursor
                            canRollback: await codeModifier.canRollbackInCurrentBlock(textEditor.document, (vscode.window.activeTextEditor ?? textEditor).selection.active)
                          });
                        } catch (e) {
                            logError(`Failed to post message in translation loop: ${e}`);
                        }
                    } catch (error) {
                        logError(`Translation failed for goal: ${error}`);
                    }
                })).catch((e) => {
                    logError(`Error in Promise.all for translations: ${e}`);
                });
                }
            }
            
            currentPosition = position;
            try {
                // Non-blocking incremental update via postMessage
                currentPanel.webview.postMessage({
                    type: 'goalsData',
                    goals: currentGoals,
                    translationEnabled: translationService.isTranslationEnabled(),
                    positionLocked,
                    lockedLine: currentPosition?.line ?? null,
                    cursorModeLabel: cursorModeLabelNow,
                    // Use actual selection for canRollback, not logical cursor
                    canRollback: await codeModifier.canRollbackInCurrentBlock(textEditor.document, (vscode.window.activeTextEditor ?? textEditor).selection.active)
                });
            } catch (e) {
                logDebug(`Webview update failed (maybe disposed): ${e}`);
                currentPanel = undefined;
                return;
            }
            logInfo(`Updated: Found ${response.goals.length} proof goals at line ${position.line}`);
            
        } catch (error) {
            logError(`Failed to update goals: ${error}`);
        } finally {
            isUpdating = false;
        }
    };

    // Add event listeners (like Paperproof)
    let debounceTimer: NodeJS.Timeout | undefined;
    const triggerUpdate = (editor?: vscode.TextEditor) => {
        if (debounceTimer) clearTimeout(debounceTimer);
        const target = editor ?? vscode.window.activeTextEditor;
        if (!target) return;
        debounceTimer = setTimeout(() => updateProofGoals(target), debounceMs());
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
        insertHaveCmd,
        insertHaveAdmit,
        insertHaveDeny,
        insertHaveAdmitWithHistory,
        rollbackCurrentBlock,
        cycleCursorModeCommand,
        analyzeCommand,
        astTestCommand,
        onActiveEditorChange,
        onSelectionChange,
        onTextChange,
        codeModifier,
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
    assets?: { katexCssHref: string; markedJsHref: string; domPurifyJsHref: string; katexJsHref: string; autoRenderJsHref: string },
    codeModifier?: any
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
        panel.webview.cspSource,
        codeModifier
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
            lockedLine: s.lockedPosition?.line ?? null,
            cursorModeLabel: cursorModeManager ? cursorModeManager.getModeConfig().label : undefined,
            canRollback: (() => {
              const activeEditor = vscode.window.activeTextEditor;
              if (!activeEditor) return false;
              // Best effort: compute at current selection
              // Note: async check isn't available here; keep false for initial render
              return false;
            })()
          });
        } catch (e) {}
    }, null, context.subscriptions);

    // Handle panel disposal
    panel.onDidDispose(() => {
        try { onDisposed(); } catch (e) {}
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
    cspSource?: string,
    codeModifier?: any
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
        // 初始渲染时不显示回滚按钮，只有后续动态更新时才显示
        const hasHistory = false;
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
                .btn.rollback { background: #fd7e14; color: white; margin-right: 10px; }
                .btn.rollback.disabled { opacity: 0.5; cursor: not-allowed; filter: grayscale(40%); }
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
                <button onclick="rollbackCurrent()" class="btn rollback disabled">↶ 回滚</button>
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
                function rollbackCurrent() {
                    console.log('rollbackCurrent clicked');
                    vscode.postMessage({ goalIndex: -1, action: 'rollback' });
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
                  // Update rollback button style (disabled look but still clickable)
                  const rbtn = document.querySelector('.btn.rollback');
                  if (rbtn) {
                    if (data.canRollback) rbtn.classList.remove('disabled');
                    else rbtn.classList.add('disabled');
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
                  // rollback handled by toolbar button
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
                  if (msg && msg.type === 'canRollbackState') {
                    const rbtn = document.querySelector('.btn.rollback');
                    if (rbtn) {
                      if (msg.canRollback) rbtn.classList.remove('disabled');
                      else rbtn.classList.add('disabled');
                    }
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
