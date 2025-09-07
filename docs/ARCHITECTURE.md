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
