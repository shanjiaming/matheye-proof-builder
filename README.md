## MathEye Proof Builder

An interactive, low‑code proof builder for Lean 4. This README explains how the system runs end‑to‑end, what data we can access today, what granularity we aim for (goals, hypotheses, local context, AST/syntax), and how we plan to evolve the RPC contract to unlock richer functionality.

---

### Architecture (one‑look overview)

- **VS Code extension (TypeScript)**
  - Paperproof‑style panel显示当前 goals，并提供交互按钮（✓ 正确 / ✗ 错误 / 固定光标 / 翻译开关）
  - 通过 vscode‑lean4 复用内置服务（如 `$ /lean/plainGoal`），并调用自定义 Lean RPC（`MathEye.*`）
  - 根据用户反馈在活动 `.lean` 文档中插入编辑

- **Lean side（Lean 4 包）**
  - 用 `@[server_rpc_method]` 定义 RPC 方法
  - 读取 `InfoTree`、`Syntax`、`LocalContext` 等，计算插入点与（未来）结构化上下文

- **Bridge（vscode‑lean4）**
  - `$ /lean/plainGoal`：获取易读的目标（含 hypotheses）
  - `$ /lean/rpc/connect` + `$ /lean/rpc/call`：调用自定义 RPC（如 `MathEye.getInsertionPoint`）

---

### 运行流程（一次点击从 UI 到代码）

1) 用户在面板对某个 goal 点 ✓ 或 ✗。
2) 扩展用 `$/lean/plainGoal` 刷新 goals，并调用自定义 RPC：`MathEye.getInsertionPoint`，让 Lean 给出“语义上的插入点”（tactic 尾部）。
3) 扩展根据动作：
   - ✓：插入 `have h : <goal> := by sorry` + `exact h`
   - ✗：插入 `have h : ¬ (<goal>) := by sorry`
   插入点与缩进以 Lean 返回的位置为准，必要时起新行。
4) 通过 `workspace.applyEdit` 应用编辑。

---

### 我们现在能拿到的数据粒度（实际可用）

- 来自 `$ /lean/plainGoal`（稳定，已用）：
  - `goals: [ { hyps: string[], goal: string } ]`（由 vscode‑lean4 提供）
  - 我们将 `hyps` 拼接并在末行加 `⊢ goal`，作为当前可显示/插入的“目标字符串”。

- 来自 `MathEye.getInsertionPoint`（已实现）：
  - 输入：`pos`（LSP 光标位置）
  - 输出：`pos`（tactic 语法节点的尾位置）。我们用它来避免基于正则的插入点猜测。

结论：目前“最小闭环”仅依赖 goal 的字符串展示与 tactic 尾插入；这适合 MVP，但不足以驱动更智能的代码生成。

---

### 我们期望的更细粒度（提议中的 Lean 侧 RPC）

目标：不只要字符串，还要拿到结构化上下文与语法信息，从而：
- 精确获得局部变量列表、类型（以及 binderInfo：显式/隐式/实例隐式）
- 区分哪些 hypothesis/locals 应作为 lemma 参数，哪些保留为隐式
- 提供稳定的 pretty‑print 输出，避免前端自行拼接

拟新增 RPC（均基于 `InfoTree`/`LocalContext`/`MetavarContext`/`Syntax`）：

1) `MathEye.getStructuredContext`（上下文结构）
- 输入：`pos`
- 输出：
  - `tacticRange`: `{ start, stop }`
  - `goal`: pretty‑printed type
  - `locals`: `{ name, type, binderInfo }[]`
  - `hyps`: `{ name, type }[]`
- 用途：生成参数化 lemma 骨架，自动补全 `exact` 的实参等。

2) `MathEye.getInsertionSpec`（插入策略）
- 输入：`pos`
- 输出：`{ kind: "appendTail", pos } | { kind: "replaceSorry", range }`
- 用途：由 Lean 决定在 tactic 中“追加”还是“替换 sorry”，前端只执行编辑。

3) `MathEye.getTacticBounds`（tactic 边界）
- 输入：`pos`
- 输出：`{ start, tail, end }`（LSP 坐标）
- 用途：多行插入、重排等需要准确块边界的编辑。

4) `MathEye.prettyPrint(expr/id)`（统一渲染）
- 输入：某个表达式或名称
- 输出：稳定字符串
- 用途：避免 TS 侧字符串拼接的“反繁饰/去糖”不一致问题。

备注：AST 本体不直接跨 RPC 传输（体量与稳定性问题），而是由 Lean 侧基于 `InfoTree` 提供“结构化摘要”（context/spec/pretty），满足可用性与兼容性。

---

### 目前的前端编辑策略

- 语义插入点：调用 `MathEye.getInsertionPoint` 获取 tactic 尾部。
- 缩进：基于当前行与编辑器设置（tabSize/insertSpaces）选择缩进；必要时起新行。
- 片段：
  - admit：`have h : <goal> := by sorry` + `exact h`
  - deny：`have h : ¬ (<goal>) := by sorry`
- 不自动替换 `sorry`（将来由 `getInsertionSpec` 决定）。

---

### 反繁饰与一致性

- 依赖 Lean 侧 pretty‑print：避免前端对 `¬`, `∧` 等自己做去糖；Lean 给出“人可读且稳定”的字符串。
- 名称与实参顺序：在 `getStructuredContext` 中由 Lean 侧判定/建议，前端只渲染。

---

### 构建、调试与测试（标准流程）

- 构建
  - `cd extension && npm ci && npm run compile`

- 本地调试（推荐）
  - F5 选择：`Run MathEye Extension (Open example/Basic.lean)`（会自动打开示例）
  - 设置 `matheye.logLevel = debug`，在“输出→MathEye”查看 RPC/反馈日志

- 单元测试
  - `cd extension && npm test`
  - 当前测试涵盖：缩进、deny 生成 `¬`、不同 tabSize 的缩进

---

### 从本仓库安装到本地（开发/试用）

1) 先决条件
   - 安装 VS Code 与 vscode‑lean4 扩展
   - 安装 Node.js 18+ 与 npm
   - 安装 Lean 工具链（本仓库自带 `lean-toolchain` 指定版本）

2) 获取代码并构建扩展
```bash
git clone <this-repo>
cd matheye-proof-builder/extension
npm ci
npm run compile
```

3) 本地运行（调试方式，推荐）
- 在仓库根目录打开 VS Code，按 F5 选择 `Run MathEye Extension (Open example/Basic.lean)`。
- 在新开的开发主机窗口中打开任意 `.lean` 文件，运行 “MathEye: Start Proof Builder”。

4) 或打包 VSIX 安装
```bash
cd matheye-proof-builder/extension
npm run compile
npx vsce package
# 生成 .vsix 后，在 VS Code 扩展面板中“从 VSIX 安装”
```

注意：若已安装过同名扩展，建议先禁用/卸载再安装 VSIX，避免多个实例冲突。

---

#### 通过本地目录安装（Install Extension from Location）

不打包 VSIX，直接从目录安装扩展：

1) 先编译扩展
```bash
cd matheye-proof-builder/extension
npm run compile
```
2) 在 VS Code 打开命令面板，运行 “Developer: Install Extension from Location…”。
3) 选择路径：`/Users/sjm/coding/projects/lean-plugin/matheye-proof-builder/extension`。
4) 安装完成后执行 “Developer: Reload Window”。

说明：这种安装方式基于本地目录（类似符号链接）。更新代码后再次 `npm run compile` 并重载窗口即可生效；卸载可在“扩展”面板正常卸载。

---

### 目标翻译（可选，OpenAI）

- 面板可显示“自然语言”翻译。要启用：
  - 在 VS Code 设置中填入 `matheye.openai.apiKey`，或
  - 设置环境变量 `OPENAI_API_KEY`
- 可选配置：`matheye.openai.model`、`matheye.openai.baseUrl`、`matheye.openai.timeout`
- 未配置 API key 时会提示并退化为原文显示。

---

### 当前实现的关键代码

```53:73:MathEye.lean
@[server_rpc_method]
def getInsertionPoint (params : InputParams) : RequestM (RequestTask InsertionPoint) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    let doc ← readDoc
    let text : FileMap := doc.meta.text
    let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos
    let results := snap.infoTree.goalsAt? text hoverPos
    match results.head? with
    | some r =>
      let stx := r.tacticInfo.stx
      let stxTailPos := stx.getTailPos?.getD (stx.getPos?.getD hoverPos)
      let tailLsp := text.utf8PosToLspPos stxTailPos
      return { pos := tailLsp }
    | none =>
      return { pos := params.pos }
```

```96:143:extension/src/extension.ts
leanClient.getInsertionPoint(posNow, editorNow.document).then((insPos) => {
  const rawAction = (message.action || '').trim();
  const act = rawAction === 'admit' ? 'admit' : 'deny';
  codeModifier.applyFeedback(editorNow.document, goalsNow, { goalIndex: message.goalIndex, action: act }, insPos, { useExactPosition: true });
});
```

```31:61:extension/src/services/codeModifier.ts
const normalized = (feedback.action || 'admit').trim();
const action: 'admit' | 'deny' = normalized === 'deny' ? 'deny' : 'admit';
// admit: have+exact; deny: have : ¬ (...)
```

---

### 路线图摘要

- Lean 侧提供结构化上下文（`getStructuredContext`）→ 支持自动生成 lemma 骨架与实参。
- Lean 侧提供插入策略（`getInsertionSpec`）→ 统一“替换 sorry / 追加尾部”。
- 统一 prettyPrint → 消除前端去糖与格式分歧。

