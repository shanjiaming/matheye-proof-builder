# 已弃用/开发专用接口（不用于生产）

说明：以下接口与路径在生产逻辑中不再调用，但代码予以保留，并在注释中标注 Deprecated/Dev-only，便于后续做 AST 观察、回环验证与格式化实验。任何时候若要纳入生产路径，需重新审阅并补充 E2E 与 real 测试。

本文归档当前仓库中保留但不用于生产路径的接口与类型，防止误用。

- 语法快照/DTO（调试）
  - `SyntaxNodeDto`
  - `syntaxToDto`
  - `dtoToSyntax`
  - `getASTAtPosition`（RPC 标注已移除）

- 启发式格式化（调试）
  - `formatSyntaxCustom`
  - `formatSyntax`
  - `formatASTToText`（RPC 标注已移除）

- AST 回环与文件级试验（调试）
  - `testRoundTripConversion`（RPC 标注已移除）
  - `convertASTToText`（RPC 标注已移除）
  - `testFileRoundTripConversion`（RPC 标注已移除）
  - `final_roundtrip_tool.py`（开发脚本）

- 旧的编辑原型（历史遗留）
  - `insertHaveAtPosition`（不再导出）
  - `trimTacticSequenceAt`
  - `insertHaveStatement`

说明：
- 以上接口仅用于早期调试与迁移探索，现已被 `insertHaveByAction` + `getByBlockRange` 的 AST-only 容器重建方案取代。
- 生产路径依赖 Lean Parser/PrettyPrinter 输出；以上“启发式/回环”接口可能输出不规范文本，因此不应再被调用。
- 若需临时调试，可在本文件范围内启用，但请勿暴露为 RPC 或纳入产品逻辑。
