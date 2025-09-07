# 变更记录（Changelog）

## 2025-09-03
- 生产路径确定性与无回退：
  - `insertHaveByAction` 移除 `_` 类型回退；类型读取失败直接报错。
  - 客户端传入 `blockRange`，服务端据此确定容器，不再误选叶子战术。
  - 容器内稳定锚点读取类型；AST-only 执行“保留前缀 + 裁剪尾部 + 追加 have/exact + tacticSeq 重建”。
  - PrettyPrinter 输出正文，并按“容器起始列”做固定缩进嵌入；非序列容器返回“\n + 缩进正文”。
- VSCode 扩展：
  - `insertHaveByAction(..., byBlockRange?)`；命令执行前确保 `import MathEye` 与 `human_oracle` 宏，随后重新锚定。
  - 回滚：先读取 `replacedText` 再应用编辑，保证可逆。
  - 测试 runner 支持离线 real：`MATHEYE_LEAN4_VSIX` 或预置扩展目录（符号链接）。
- 文档：
  - 更新 `docs/IMPLEMENTATION_CURRENT_CN.md`、`docs/DEPRECATED_APIS_CN.md`、`README.md`；新增 `docs/TESTING.md`。

