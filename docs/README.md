# Docs Index

## 项目约束（必须遵守）
- 一定不能做字符串程度的编辑，所有编辑都在 AST 上完成
- 不能特判，要通用地覆盖
- 要跑通所有测试，并且在 real 模式下跑通
- 不要预设运行结果打印过多无效日志，先观察输出
- 不要 fallback。用确定的控制流理解与驾驭程序；让错误自然暴露
- 能用命令行或工具完成的任务，不要依赖人工
- 用户报告的 bug 必须复现，无法复现则说明原因并索取信息
- 寻找过时内容并更新
- 自主探索、写测试、找 bug
- 始终用中文沟通

以上内容原位于 `CLAUDE.md` 与 `warning.md`，现合并至此，作为单点来源。

## 权威文档（生产）：
- ARCHITECTURE.md — 架构总览与模块边界
- IMPLEMENTATION_CURRENT_CN.md — 当前生产实现细节与不变式
- TESTING.md — 本地测试（mock/real）与离线运行指南
- DEPRECATED_APIS_CN.md — 弃用/开发专用接口说明（保留但不在生产路径调用）
- CHANGELOG.md — 变更记录

存档（历史/阶段性）：
- archive/AST_SYSTEM_DESIGN.md — 早期 jixia/Python round‑trip/formatter 方案
- archive/IMPLEMENTATION_STATUS.md — 旧格式化工具里程碑
- archive/TASK_CONTEXT_CN.md — 阶段性任务背景
- archive/VSCode_AST_Migration_Plan.md — 迁移计划（已完成，方案有调整）

## 说明
- 生产路径只参考“权威文档”。
- 存档文档仅供参考，内容与现行实现可能不一致。
