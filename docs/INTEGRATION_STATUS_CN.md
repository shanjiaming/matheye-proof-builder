# MathEye 集成状态与问题总览（实时）

本文记录当前代码库的整体状况、测试方法、已知问题、复现步骤、证据与下一步计划。目标是让任何人都能基于此文档独立完成“复现—诊断—修复—验证”的闭环。

## 一、项目结构与目标

- Lean 侧：`MathEye.lean`（RPC 方法、AST-only 编辑逻辑，不做字符串级编辑、不做 probing；用文件末尾快照 + 全文件 by 容器选择）
- VS Code 扩展：`extension/`（TypeScript，命令与 RPC 客户端、单元与集成测试）
- Lake 工程：`lakefile.lean`，工具链：`lean-toolchain`（Lean 4.20.0）

核心目标：在“real 模式”集成测试中，针对 `:= by rfl` 等 inline 情形，调用 RPC 后将其转换为 `:= by` 块并吞掉行尾 `rfl`，随后 `lake env lean` 编译通过。

## 二、测试方法

### 1. 扩展单元测试

```
cd extension
npm ci
npm run test   # 或 npm run test:unit
```

期望：所有 unit 用例通过。

### 2. real 模式集成测试（VS Code 测试宿主 + 实际 Lean 服务器）

```
cd extension
npm run test:integration:real
```

当前 real 测试入口：`extension/src/test/suite/` 下 `suite.ts`/`cases.ts`/`single_case.ts`。

重要说明：测试会尝试编译 Lean 侧（`lake build` + 直接 `lean` 编译），设置 `LEAN_PATH`，并在测试运行前后做最小的“加载状态校验”。

## 三、日志与取证

- 扩展侧 RPC 日志：
  - `extension/out/rpc_debug.log`
  - 含 `getByBlockRange` / `insertHaveByAction` 调用、异常、以及（若加载成功）`BUILD_TAG=...`
- Mocha 结果：
  - `extension/out/test/suite/mocha_results.log`
- 服务器侧（按代码写入的 /tmp 文件，注意 VS Code 测试宿主可能不可见）：
  - `/tmp/getByBlockRange_debug.log`
  - `/tmp/insertHaveByAction_debug.log`
  - `/tmp/*_no_probe.log`（若加载到新实现）

当前现象（已更新）：
- 预热与构建后，服务端已注册 RPC（日志出现 BUILD_TAG=NO_PROBE_VER_1）。
- 早前的“exact 缺失/错位”问题已消失（Admit 路径会生成 `have h …; exact h` 且可编译）。
- 现存失败集中在 inline `:= by rfl`：有时无法稳定获得战术节点，或 by 容器范围退化，导致 `rfl` 未被吞掉（日志报 “rfl should be trimmed”）。

## 四、已知问题（本质）

- 不是加载问题，RPC 已注册（BUILD_TAG 已观测）。
- 目前失败为 inline `:= by rfl` 场景：战术节点在光标附近偶发缺失，仅有 term by 容器；或 by 容器范围退化为 token 级，进而未吞掉 rfl。
- 我们已统一 getByBlockRange 与 insertHaveByAction 的容器/范围计算；对“仅 term 无 tactic”的位置，使用“全文件收集 by + 最近起点选择”的 AST-only 策略。

## 五、Lean 侧逻辑（当前实现要点）

- 完全 AST-only，不做字符串级编辑；彻底移除 probing/窗口扫描（包括所有 `List.range` 探针）。
- term by 容器（例如 `:= by rfl`）：
  - 起点：by 容器 `range.start`
  - 终点：递归 `lastStopInSubtree` 获取 tacticSeq 子树中最右叶子战术的 stop；若无则在容器子树中取最右 stop；若仍无则用 tail/stop。
  - 退化区间（stop ≤ start）一律失败。
- tactic 上下文：替换整个 tacticSeq 容器。
- `getByBlockRange`、`insertHaveByAction` 返回体带 `buildTag=NO_PROBE_VER_1`（用于测试宿主加载确认）。

## 六、我已做的验证与尝试（最新）

1) 加载状态校验：已能稳定观测 `BUILD_TAG=NO_PROBE_VER_1`；RPC 方法存在。

2) 行为验证：admit/deny 在 by 块（非 inline）可正常插入 `have …` 并（admit）附加 `exact …`，不再出现 “exact 缺失/错位”。

3) 失败重现（inline by rfl）：某些位置仅有 term by 容器（无 tactic 节点），原先基于 goalsAt? 的路径返回空；现改为用“全文件收集 by + 最近起点选择”直接确定容器范围，再于容器体内选择稳定位置读取类型。

## 七、如何复现当前失败

```
cd extension
npm run compile
npm run test:integration:real

# 观察：
# - extension/out/rpc_debug.log 会反复出现：
#   [getByBlockRange] -> error=Error: No RPC method 'MathEye.getByBlockRange' found
#   [insertHaveByAction] EXCEPTION ... No RPC method 'MathEye.insertHaveByAction' found
# - extension/out/test/suite/mocha_results.log 会显示 inline by rfl 的断言失败。
```

## 八、建议的下一步（逻辑修正与日志）

1) getByBlockRange：已完成统一容器/范围推导；加入 InfoTree term 路径回退，记录详细路径与最终 LSP 范围到 `/tmp/getByBlockRange_debug.log`。

2) insertHaveByAction：当 goalsAt? 为空时，先用 InfoTree 推导 by 容器与稳定位置，再次用 goalsAt? 读取类型；范围推导与 getByBlockRange 完全一致；详细过程写入 `/tmp/insertHaveByAction_debug.log`。

## 九、如何手工验证加载是否成功

1) 在 VS Code（非测试宿主）中：
- 打开仓库根路径（确保 `lakefile.lean` 可见），安装并启用 `leanprover.lean4` 扩展。
- 先执行 `lake build MathEye`，再打开 `test_cases/test_01_basic_theorem.lean` 或 `.it_scratch/` 下某个含 `import MathEye` 的文件。
- 观察 infoview 是否正常 elaboration（无 unknown import），执行扩展命令（如 `matheye.insertHaveAdmit`），再观察扩展日志/控制台是否出现 RPC 的响应（不是“method not found”）。

2) 检查 Lean 搜索路径：
```
lake print-paths
```
- 确保输出包含：`<repo>/.lake/build/lib/lean`。

## 十、AST 逻辑不变性的说明

- 不做字符串级编辑；不做 probing；替换范围由 AST 决定；退化区间失败。
- 当前失败与“加载问题”无关（实测 BUILD_TAG 存在），是 inline by rfl 在光标附近缺失 tactic 节点导致；我们以 InfoTree term 路径补强，仍保持 AST-only。

## 十一、关键文件位置

- Lean 侧：`MathEye.lean`
- VS Code 扩展入口：`extension/src/extension.ts`
- 扩展服务：`extension/src/services/*.ts`
- 集成测试：`extension/src/test/suite/*.ts`
- 测试日志：
  - `extension/out/rpc_debug.log`
  - `extension/out/test/suite/mocha_results.log`
  - （若可见）`/tmp/getByBlockRange_debug.log`, `/tmp/insertHaveByAction_debug.log`

## 十二、后续计划（执行顺序）

1) 仅在测试流程中，保证 lean4 扩展以 lake 方式启动服务（例如：`lake serve` 或 wrapper）。
2) 在测试前置加“启动后自检”，若 RPC 未注册则明确报告“加载失败”并终止。
3) 一旦加载确认（`BUILD_TAG` 出现），跑 inline by rfl 的 admit/deny 用例，验证 `:= by` 结构与无 `rfl`，并 `lake env lean` 编译通过。
4) 若出现与 AST 逻辑相关的失败，再分析 AST，不在“加载问题”未解决时堆补丁。
