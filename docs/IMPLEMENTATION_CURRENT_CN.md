# MathEye 当前实现（完整说明）

本文记录目前“插入 have/ exact（Admit/Deny）”能力的端到端实现逻辑、约束、不变式与接口细节，来源以代码为准（Lean: `MathEye.lean`；扩展端: `extension/src/extension.ts`, `extension/src/services/leanClient.ts`）。本说明不包含已弃用的 dev-only/原型接口（这些接口被保留但不在生产路径使用）。

## 总览
- 架构分层：
  - VSCode 扩展负责：
    - 命令入口：`matheye.insertHaveAdmit` / `matheye.insertHaveDeny`；
    - 依赖 `getByBlockRange` 返回的 by 容器范围，将调用点对齐到 `byRange.start` 作为锚点；
    - 仅做导入与宏注入（缺则补齐）；不做字符串级“找 by/找 =>”与范围探针；
    - 应用 Lean 端返回的整篇替换文本；缩进/换行交由 PrettyPrinter。
  - Lean 端（`MathEye.lean`）负责：
    - 核心 RPC：`insertHaveByAction`（唯一生产入口，支持 `blockRange?`）；
    - 统一容器/范围决策：在服务端基于 InfoTree AST 选择 by 容器与范围；
    - AST 编辑：保留 stablePos 之前的战术，整体裁剪其后，然后追加 have/exact，重建 `tacticSeq1Indented`；
    - Pretty 打印正文并按容器起始列缩进；返回整篇替换文本；
    - 查询辅助：`getByBlockRange`（返回当前 by 容器/战术容器范围与上下文信息）。

- 关键不变式：
  - 仅做 AST 层面编辑；不做字符串级替换/拼接；
  - 容器确定性：容器/范围由服务端 AST 统一决策；
  - 快照稳定：用“文件末尾位置”获得完整 InfoTree，再以调用点 `pos` 作为查询点进行容器选择；
  - 无不透明回退：类型读取失败即报错，不用 `_` 或字符串修补；
  - 从 stablePos 到容器末尾整体裁剪，杜绝重复 have/exact；
  - Pretty 打印 + 固定列缩进；内联 `rfl` 等非 `tacticSeq` 容器会被转换为“`by` 块 + 缩进正文”的统一形态。

## VSCode 扩展端
- 文件：`extension/src/extension.ts`
- 命令：
  - `matheye.insertHaveAdmit` / `matheye.insertHaveDeny`
    - 如处于真实测试模式，会等待 Lean Server ready（最多 ~2.25s，15×150ms）。
    - 通过 `LeanClientService.getByBlockRange(pos)` 获取 by 容器范围；
    - 将调用位置对齐为 `byRange.start`（完全使用 RPC 的 AST 结果）；
    - 调用 `LeanClientService.insertHaveByAction(pos, action, byRange, includeByOnSeq?, returnWholeFile=true)`；
    - 将返回的整篇文本作为 `WorkspaceEdit` 应用（整篇替换，无二次加工）。

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
-- 流程：
  1. 以“文件末尾位置”获取完整 InfoTree 快照，使用 `pos` 作为查询点；
  2. 若 `goalsAt?` 为空：在全树收集 `byTactic` 并用“最近起点”规则选择 by 容器；否则按路径从 term 路径选中 by 容器；
  3. 在 by 容器内部选择稳定锚点 `stablePos`，以 `g.withContext` 读取目标类型并 pretty；
  4. AST 重写：保留 stablePos 之前的 tactics，整体裁剪其后，解析并追加 have/exact，重建 `tacticSeq1Indented`；
  5. Pretty 打印正文并按容器起始列缩进；返回整篇替换文本。
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
  - 用“文件末尾位置”获取完整 InfoTree；
  - tactic 路径命中时，从 term 路径选中最小 `byTactic` 容器，范围为 `by.start → 子 tacticSeq 最右 stop`；
  - tactic 路径未命中时，收集全文件 `byTactic` 并用“最近起点”规则选取；
  - 返回 `range`、`syntaxKind`、`isTacticContext`/`isTermContext` 等信息。

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
- 覆盖点：光标在 `|` 前、`=>` 后（含/不含空格）、inline `:= by rfl`、已有 have 的分支、重复 admit/deny 等；
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
