# MathEye 当前实现（完整说明）

本文记录目前“插入 have/ exact（Admit/Deny）”能力的端到端实现逻辑、约束、不变式与接口细节，来源以代码为准（Lean: `MathEye.lean`；扩展端: `extension/src/extension.ts`, `extension/src/services/leanClient.ts`）。本说明不包含已弃用的 dev-only/原型接口（这些接口被保留但不在生产路径使用）。

## 总览
- 架构分层：
  - VSCode 扩展负责：
    - 命令入口：`matheye.insertHaveAdmit` / `matheye.insertHaveDeny`；
    - 先用 `getByBlockRange` 精确定位当前 by/分支容器范围，并随 RPC 一起传入；
    - 应用 Lean 端返回的最小范围 `TextEdit`（容器子树），不做二次字符串加工。
  - Lean 端（`MathEye.lean`）负责：
    - 核心 RPC：`insertHaveByAction`（唯一生产入口，支持 `blockRange?`）；
    - 容器：优先使用扩展传入的 by 块范围确定容器；否则退回语法路径选择 tacticSeq；
    - 稳定锚点：在容器内靠前合法位置（避开 `|/=>` seam）读取目标类型；
    - AST 编辑：保留 stablePos 之前的所有 tactics（prefix），整体裁剪其后，然后追加 have/exact；重建 `tacticSeq1Indented`；
    - Pretty 打印正文并按“容器起始列”做固定缩进嵌入；
    - 查询辅助：`getByBlockRange`（返回当前 by/战术容器范围）。

- 关键不变式：
  - 仅做 AST 层面编辑；不做字符串级替换/拼接；
  - 容器确定性：优先以客户端传入范围为准；
  - 使用稳定锚点 `stablePos`（容器内部）获取目标类型，避免 seam 位置造成的 metavariable 失配；
  - 从 stablePos 到容器末尾整体裁剪，避免重复 have/exact；
  - 无 fallback：若无法安全读取类型，直接返回失败（不使用 `_` 等退路）；
  - Pretty 打印 + 固定列缩进嵌入；非 `tacticSeq` 容器（如 `=> rfl`）返回“`=>` 后换行 + 缩进正文”的统一形态（不拼接 `by` 关键字）。

## VSCode 扩展端
- 文件：`extension/src/extension.ts`
- 命令：
  - `matheye.insertHaveAdmit` / `matheye.insertHaveDeny`
    - 如处于真实测试模式，会等待 Lean Server ready（最多 ~2.25s，15×150ms）。
    - 通过 `LeanClientService.getByBlockRange(pos)` 获取当前 by/分支容器范围；
    - 将调用位置锚定到该行的 `=>` 后（考虑 `=>` 后是否有空格），从而避开 `|/=>` 接缝；
    - 调用 `LeanClientService.insertHaveByAction(pos, action)`；
    - 将返回的 `{ range, newText }` 作为一个 `WorkspaceEdit` 应用（最小替换，无二次加工）。

- Lean 客户端：`extension/src/services/leanClient.ts`
  - `insertHaveByAction`：
    - 通过 `$/lean/rpc/connect` 建立会话；
    - 调用 `MathEye.insertHaveByAction`，并传入 `blockRange`；
    - 若成功，返回 VSCode 的 `Range` + `string`；失败直接报错，不做任何字符串修补。

- human_oracle：
  - 测试样例中在文件顶部提供：
    - `import MathEye`
    - `macro "human_oracle" : tactic => `(tactic| sorry)`
  - 其他扩展入口（如历史管理/高级交互）里，会在缺失时一次性注入上述导入与宏；对 Admit/Deny 主路径不做额外字符串编辑。

## Lean 端 RPC：insertHaveByAction
- 文件：`MathEye.lean`
- 签名：
  - 输入：`{ pos : Lsp.Position, action : String, blockRange? : RangeDto }`，其中 `action ∈ { "admit", "deny" }`；
  - 输出：`{ success, range, newText, errorMsg? }`；
- 流程：
  1. 读取语法路径 `results`；若客户端传入 `blockRange`，优先使用该范围确定容器，否则按路径选择包含关系最大的 tacticSeq 作为容器。
  2. 在容器内部选择稳定锚点 `stablePos`（靠前且合法），再以该帧 `ctxInfo` 读取目标类型（失败则返回错误）。
  3. AST 重写：保留 stablePos 之前的 tactics，整体裁剪其后，解析并追加 have/exact，重建 `tacticSeq1Indented`。
  4. Pretty 打印正文，按“容器起始列”统一缩进；若容器非 `tacticSeq`，返回“`\n` + 缩进正文”。
  4. 目标类型与 snippet 构造：
     - 在 `rStable` 的上下文中取得目标类型 `ty` 并 pretty-print 成 `tyStr`；
     - 生成变量名 `h_{line}_{character}`；
     - Admit：`have h : ty := by human_oracle` + `exact h`；
       Deny：`have h : ¬ (ty) := by human_oracle`；
     - 用 Parser（`parseTacticSegments`）将 snippet 解析为战术 `Syntax` 数组。
  5. 全量裁剪 + 重建：
     - `baseArgs := flatten(container)` 得到容器内原战术序列；
     - `kept := filter (end ≤ stablePos)` 保留 stablePos 之前的战术；
     - `newArgs := kept ++ parsedSnippet`；
     - `newStx := tacticSeq1Indented(newArgs)`；
     - `body := formatTacticSeq(newStx)`（内部对每个 `tactic` 调用 PrettyPrinter）。
  6. 计算最小替换范围与最终文本：
     - `rr := RangeDto.fromStringRange(container.range)`；
     - 计算 `baseIndent` = 容器起始列对应的空格串；
     - 若容器本身是 `tacticSeq`：返回 `body` 的按行缩进文本；
     - 否则（内联场景，如 `=> rfl`）：返回 `"\n" ++ indented(body)`，即头部为 `=>` 后换行，正文缩进两格，Lean 语法正确。

- 失败路径（不做补救）：
  - `goalsAt?` 为空；`stablePos` 处无目标；容器无范围；
  - 目标类型读取失败（Meta/pp 错误）；
  - 以上直接返回失败/错误信息，不做任何退路。

## Lean 端 RPC：getByBlockRange
- 用途：客户端结构化定位 by/分支容器范围，避免把光标放在 `|/=>` 接缝。
- 流程：
  - 从 `pos` → `hoverPos`，`goalsAt?` 得到路径；
  - 按容器选择规则选中 `tacticSeq` 容器（或退回当前战术节点）；
  - 返回其 `range`（LSP 坐标），供客户端定位。

## 生成文本的统一规格
- 容器为 `tacticSeq`：直接替换块体，`body` 按容器起始列缩进，每条 tactic 单独一行；
- 容器非 `tacticSeq`（如 `| zero => rfl`）：
  - 最终头部形态为 `| zero =>` 换行；
  - 正文按两格缩进输出 have/exact 序列；
  - 这是 Lean 合法的“将单条战术替换为战术序列块”的形态（无需在头部再写 `by`）。

## 约束与保证
- 仅使用 Lean Parser/PrettyPrinter 进行结构化编辑与格式化（核心路径不使用启发式 formatter）。
- 仅替换 by/战术容器内的最小文本范围，不触碰容器外部。
- 从 stablePos 到容器末尾“全量裁剪”，杜绝重复 have；
- 变量命名固定为 `h_{line}_{character}`，避免冲突概率高但可读。

## 测试（mock 与 real）
- mock：`cd extension && npm run test:integration`（每个用例的 post 文件将用 `lake env lean` 编译验证）
- real：
  - 在线安装：`MATHEYE_USE_REAL_RPC=1 npm run test:integration`
  - 离线安装两种方式（二选一）：
    - 使用 VSIX：`MATHEYE_USE_REAL_RPC=1 MATHEYE_LEAN4_VSIX=/abs/path/leanprover.lean4-*.vsix npm run test:integration`
    - 预置扩展目录（推荐本仓做法）：将本机已安装的 lean4 扩展目录软链到 `extension/out/.vscode-test/extensions/`
      - 例：`ln -s ~/.cursor/extensions/leanprover.lean4-0.0.209-universal extension/out/.vscode-test/extensions/`
- 覆盖点：光标在 `|` 前、`=>` 后（含/不含空格）、已有 rfl/已有 have 的分支、重复 admit/deny 等；
- 断言：头部合法（`=>` 后换行或 `=> by`）、rfl 被裁剪、不重复 have/exact、`lake env lean` 编译通过。

## 与已弃用（dev-only/原型）接口的关系
- 早期调试/原型：
  - 语法快照/DTO：`getASTAtPosition`/`syntaxToDto`/`dtoToSyntax`；
  - 启发式 formatter：`formatSyntaxCustom`/`formatASTToText`；
  - 回环校验：`testRoundTripConversion`/`testFileRoundTripConversion`；
  - 旧编辑原型：`insertHaveAtPosition`/`trimTacticSequenceAt`。
- 现状：
  - 以上均已从调用侧收敛（不在生产路径使用），以免误用；但代码与文档予以保留，标注 Deprecated/Dev-only 以备后续实验；
  - 生产路径只保留 `insertHaveByAction`/`getByBlockRange` + Parser/PrettyPrinter + tacticSeq 重建。

## 依赖与环境
- Lean 版本：`lean-toolchain` 指定；
- Lake 工程：`lake build MathEye` 产出 `.olean`；
- VSCode 测试宿主：通过 `@vscode/test-electron` 启动，确保安装 `leanprover.lean4` 扩展；
- human_oracle：保持保留（用于 Admit/Deny 示例）。

## 小结
- 生产逻辑完全落在 AST 层：定位容器 → 稳定锚点 → 全量裁剪 → 解析并追加 → tacticSeq 重建 → PrettyPrinter 输出；
- 客户端仅做“精确定位到 `=>` 后”的前置步骤，避免 seam，编辑仍由 Lean 端统一完成；
- 不做字符串级拼接/正则修补；失败则失败，避免不透明 fallback。
