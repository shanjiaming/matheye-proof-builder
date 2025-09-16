# MathEye Architecture (Lean 4 + VSCode)

This document describes the modules, RPC flows, and client wiring for the AST‑first proof editing.

## Modules

- Lean (MathEye.lean)
  - RPC: `getByBlockRange(pos)` → `RangeDto`
  - RPC: `insertHaveByAction(pos, action, blockRange?)` → `{ range, newText }`
  - Helpers (production): `parseTacticSegments`, `flattenTacticSeqArgs`, `buildIndentedSeq`, `formatTacticSeq`

- VSCode Extension
  - `LeanClientService`: RPC bridge
  - `CursorModeManager`: async, AST‑backed logical cursor and delete range
  - `CodeModifierService`: applies AST edits via server, maintains history/rollback
  - Commands:
    - `matheye.startProofBuilder`
    - `matheye.insertHaveAdmit` / `matheye.insertHaveDeny`

## RPC Flow

1) UI triggers edit (✅/❌ or command).
2) Client calls `getByBlockRange(pos)` for accurate by‑block range, and passes it to `insertHaveByAction` for AST edit.

AST‑only 容器选择（现状）

- 服务端在两处统一做“容器与范围”决策：`getByBlockRange` 与 `insertHaveByAction`。
- 快照来源：不再依赖调用点的 InfoTree，而是以“文件末尾位置”获取完整 InfoTree，再用调用点 `pos` 作为查询点进行决策，避免 0:0 等位置 InfoTree 未建全的问题。
- tactic 路径命中时：从 term 路径选出覆盖 `pos` 的最小 `byTactic` 容器，范围一律为 `by.start → tacticSeq 子树最右 stop`。
- tactic 路径未命中时：遍历整棵 InfoTree 收集所有 `byTactic`，用“最近起点”规则选择容器（start ≥ pos 的最小者，否则 start < pos 的最大者）。
- 返回结构包含：`range`、是否在 tactic/term 上下文、`syntaxKind`（命中 by 时为 `Lean.Parser.Term.byTactic`）。

客户端职责收敛

- 客户端不再做字符串级的“找 by”或范围探针，仅：
  - ensureImports（`import MathEye` 与 `human_oracle` 宏）；
  - 以服务器返回的 `byRange.start` 作为锚点，再发起一次 RPC；
  - 要求服务端返回整篇替换文本，缩进/格式完全由 PrettyPrinter 决定。
3) Server (Lean) does: resolve container from range → stable anchor → Meta (goal type) → AST trim/append → format subtree → returns `{ range, newText }`.
4) Client deterministically synthesizes the full document from `{ range, newText }` and applies exactly one TextEdit replacing the entire file (full‑file replacement to avoid snapshot drift).

## Cursor Modes

- `CURRENT` (actual cursor)
- `BY_START` (by block start)
- `BY_END` (by block end)

The logical cursor defines where the server will trim tactics to the end of the by block.

## Safety and Purity

- All structure edits on `Syntax` (Lean server). No regex, no TS string heuristics.
- Parser only used to build `Syntax`, not to scan or rewrite text.
- Client lands AST result using one TextEdit (LSP standard), minimal surface change.

Note: There is no fallback (e.g., `_` types). If goal type cannot be obtained at a stable anchor, the server returns an explicit error.

## Rollback

- `HistoryManager` records `{ byBlockRange, insertedText, replacedText, absolute ranges }`.
- Rollback verifies current slice equals recorded text before restoration.

## Testing

- VSCode integration harness (see README): `@vscode/test-electron` runner.
- Extend tests to open a sample, run edit, save, and compile with `lake env lean`.
