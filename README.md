# MathEye — AST‑First Proof Builder (Lean 4 + VSCode)

MathEye 是一个“AST 优先”的 Lean 4 扩展与服务器模块：所有编辑都在 Lean 端基于 `Syntax` 进行结构化修改，统一交由 Lean 的 formatter 输出；VSCode 端仅以一个 TextEdit 落地该子树的文本。无正则、无字符串拼接。

## 快速使用
```bash
# 1) 构建 Lean 侧
lake build

# 2) 构建 VSCode 扩展
cd extension
npm install
npm run compile

# 3) VSCode 中按 F5 启动扩展宿主
# 打开 .lean 文件，将光标放进 by 块
# 在命令面板中运行：
#  - MathEye: Start Proof Builder（推荐 UI 流程）
#    在面板中使用“✅/❌”按钮提交反馈（见本文下方“UI 使用指南”）。
#  - 或直接运行：MathEye: Insert Have (Admit) / (Deny)（快捷命令）
```

### 配置
- `matheye.fullFileReplace`（已废弃，现始终启用整篇替换）
  - 为避免 Lean 服务器快照与 VSCode 文档状态长期漂移，现统一采用“整篇替换”策略：
    客户端以服务器返回的 AST 子树编辑为依据，确定性地合成新的整篇文档文本，并一次性替换整个文件。
  - 该选项保留于 package.json 仅作占位，当前实现不再读取此配置。

### 命令
- `MathEye: Insert Have (Admit)` — 在 by 块尾部追加 `have` + `exact`
- `MathEye: Insert Have (Deny)` — 在 by 块尾部追加 `have … : ¬(goal)`
- `MathEye: Insert Have Snippet` — 调试辅助（生产流不使用）

提示：若文件顶部缺少 `import MathEye` 与 `macro "human_oracle" : tactic => `(tactic| sorry)`，扩展会自动注入一次，随后再调用 RPC。

## UI 使用指南（Proof Builder 面板）

启动方式：
- 打开 Lean 4 文件，在命令面板运行 “MathEye: Start Proof Builder”。
- 视图将显示当前光标处的 proof goals，并提供交互按钮。

面板元素与按钮：
- 目标列表：显示当前 goals（Lean 原始 pretty 文本）。
- ✅ 接受（Admit）：
  - 语义：在逻辑光标到 by 块结尾处删除旧战术（服务器 AST 裁剪），随后在 by 块末尾追加 `have h : goal := by human_oracle` 与 `exact h`。
  - 行为：完全在服务器 AST 上完成，VSCode 仅落地一个 TextEdit 于该 by 块范围。
- ❌ 拒绝（Deny）：
  - 语义：同样裁剪光标之后的战术，并在 by 块末尾追加 `have h : ¬(goal) := by human_oracle`（不追加 exact）。
- 🔒 锁定光标（Toggle Lock）：
  - 固定当前的逻辑光标位置，避免你移动实际光标时 UI 抖动或短暂 0-goal 状态。
- 🔁 切换光标模式（Cycle Cursor Mode）：
  - 三种模式：
    - 当前光标（CURRENT）
    - By 块开始（BY_START）
    - By 块末尾（BY_END）
  - 逻辑光标用于定义“从光标到末尾”的裁剪区间（服务器 AST 裁剪）。
- 🌐 目标翻译（Toggle Translation）：
  - 显示/隐藏自然语言翻译（若启用翻译服务）。
- ↩️ 回滚（Rollback）：
  - 恢复最近一次在当前 by 块中应用的插入操作（范围与文本基于历史记录严格匹配）。

注意：
- 面板中的所有编辑都通过服务器 AST 执行，并且只替换 by 块对应的最小文本范围（除非你启用了整篇替换）。
- 文件顶部如缺少宏 `macro "human_oracle" : tactic => `(tactic| sorry)`，会自动注入一次。

## 端到端设计

### 客户端（VSCode）
- `CursorModeManager`
  - 通过服务器 `getByBlockRange` 获取精准 by 块范围，计算逻辑光标与删除区间（异步、AST 背书）。
  - 已移除所有正则扫描与缩进推断逻辑。
- `CodeModifierService`
  - 调用服务器 `insertHaveByAction(pos, action)` 执行“从逻辑光标到末尾裁剪 + 追加 have”并格式化子树。
  - 始终合成整篇文档并以单一 TextEdit 替换整文件，杜绝局部替换导致的快照漂移。
  - 文件顶部缺失 `human_oracle` 宏时自动注入一次。
- `LeanClientService`
  - 封装 `getByBlockRange`、`insertHaveByAction`，负责 VSCode Range 转换与 RPC 调用。

### Proof Builder 面板架构
- 命令 `MathEye: Start Proof Builder` 创建/更新面板并监听：
  - 光标移动/选择变化 → 触发异步刷新（防抖）
  - 文档变化 → 跟随 Lean 重新 elaboration 的窗口刷新
- 面板与 CodeModifier/TranslationManager 协作：
  - 接收 UI 按钮事件（✅/❌/锁定/翻译开关/回滚/光标模式切换）
  - 通过 LeanClientService 调用服务器 RPC，更新文档与 UI

### 服务器（MathEye.lean）
- `getByBlockRange(pos)`
  - 利用 `r.tacticInfo.stx.getRange?` 返回当前 by 块的 `RangeDto`。
- `insertHaveByAction(pos, action)`
  - 以客户端传入的 by 块范围确定容器；在容器内选择稳定锚点读取目标类型（失败直接报错，不做 `_` 回退）。
  - AST-only：保留稳定锚点前的 tactics，整体裁剪其后，解析并追加 have/exact，重建 tacticSeq；
  - PrettyPrinter 打印正文，并按“容器起始列”做固定缩进嵌入；返回 `{ range, newText }`（容器最小范围与文本）。

### 为什么是 AST‑Only 且安全
- 所有结构性修改都在服务器 `Syntax` 执行，无正则、无字符串层修补。
- parser 仅用于“生成 `Syntax`”，不用于“搜索/替换文本”。
- LSP 落地必须是文本编辑；我们只做一个 TextEdit（by 块范围），不会牵动其它区域（除非你启用整篇替换）。

## 测试与脚手架
- Lean 构建：`lake build`
- 扩展构建：`cd extension && npm install && npm run compile`
- VSCode 集成测试脚手架（需在 VSCode 测试宿主运行）：
  - `extension/src/test/suite/runTest.ts`
  - `extension/src/test/suite/suite.ts`
  - 运行（mock）：`npm run test:integration`
  - 运行（real, 在线）：`MATHEYE_USE_REAL_RPC=1 npm run test:integration`
  - 运行（real, 离线 VSIX）：`MATHEYE_USE_REAL_RPC=1 MATHEYE_LEAN4_VSIX=/abs/path/leanprover.lean4-*.vsix npm run test:integration`
  - 运行（real, 离线目录预置，推荐）：
    - `mkdir -p extension/out/.vscode-test/extensions`
    - `ln -s ~/.cursor/extensions/leanprover.lean4-0.0.209-universal extension/out/.vscode-test/extensions/`
    - `MATHEYE_USE_REAL_RPC=1 npm run test:integration`
  - 测试做了什么：打开合成 Lean 文件，将光标放在“`|` 前”和“`=>` 后（含/不含空格）”，执行 `matheye.insertHaveAdmit`，断言插入结构正确；测试会将“前快照（*.pre.out.lean）/后快照（*.post.out.lean）”写入 `extension/out/test/suite`；并对后快照执行 `lake env lean` 编译验证。
 
### 本仓样例与清理
- `test_cases/` 仅保留 `.lean` 样例；所有结果日志、临时与调试产物均已清理。
- 历史 Round‑Trip 记录移动至 `logs/roundtrip_outputs.log`，仅供参考。

## 我们删掉了什么
- 移除所有正则/启发式路径及其调用：无“by/sorry”扫描、无缩进猜测、无文本拼接。
- 移除 `SmartByBlockFinder` 及依赖；不再使用 AST 测试工具（扩展内旧的 jixia 调用）。
- 仅保留必要的历史/回滚记录（基于 Range），其余冗余代码已清理。

## 生产不变式（硬约束）
- 只在 AST 层编辑；仅替换最小容器范围；无正则、无字符串拼接。
- 容器确定性：客户端传入 by 块范围；服务端在容器内选择稳定锚点读取类型。
- 无回退：类型读取失败直接报错（不使用 `_`）。
- PrettyPrinter 输出 + 固定列缩进嵌入；头部形态不被改写（内联时使用“=>\n + 正文”合法形态）。

## 弃用/开发专用接口
- 文档：`docs/DEPRECATED_APIS_CN.md`
- 代码保留但不在生产调用；如需启用，务必补充 E2E/real 测试并复核不变式。

## 运维与扩展
- 宏注入：若缺失，首次在文件顶部注入 `macro "human_oracle" : tactic => `(tactic| sorry)`，以确保 `by human_oracle` 可编译。
- Range 仅用于“落地”AST 修改（TextEdit），不用于字符串切片。
- 要新增 AST 编辑：按照同一模式新增 Lean RPC，返回 `{ range, newText }`；客户端仅应用该编辑即可。
