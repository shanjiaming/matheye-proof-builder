# MathEye 代码执行跟踪 - 具体变量值分析

## 调试场景：debug_scenario.lean

```lean
theorem debug_example (n : Nat) : n = n := by
  -- 假设用户光标在这里 (第8行，character 2)
  sorry
```

---

## 第一步：用户在VSCode中点击"接受"(Admit)按钮

### VSCode扩展端调用流程

#### 1. extension.ts 中的 insertHaveAdmit 命令

**位置**: `extension/src/extension.ts:163`

**关键变量值**:
```typescript
// 用户点击位置
const editor = vscode.window.activeTextEditor;
const pos = editor.selection.active;
// pos = { line: 7, character: 2 }  // sorry 前面的位置

// 检测到的by块范围
let byRange = {
  start: { line: 6, character: 0 },  // ":= by" 的开始
  stop: { line: 8, character: 6 }    // "sorry" 的结束
};

// 调用参数
const action = 'admit';  // 用户点击了"接受"
const includeByOnSeq = false;  // 在tactic上下文中，无需添加"by"
const returnWholeFile = true;  // 返回整个文件替换
```

#### 2. leanClient.ts 中的 RPC调用

**位置**: `extension/src/services/leanClient.ts:151`

**RPC参数构建**:
```typescript
const rpcParams = {
    method: "MathEye.insertHaveByAction",
    params: {
        pos: { line: 7, character: 2 },        // 用户光标位置
        tactic: "admit",                       // 操作类型
        byRange: {                             // by块范围
            start: { line: 6, character: 0 },
            stop: { line: 8, character: 6 }
        },
        includeByOnSeq: false,                 // 不需要添加"by"
        returnWholeFile: true                  // 返回完整文件
    }
};
```

---

## 第二步：Lean服务器端处理

### MathEye.lean 中的 insertHaveByAction 函数

**位置**: `MathEye.lean:625`

**输入参数值**:
```lean
params : InsertHaveByActionParams := {
  pos := { line := 7, character := 2 },      -- 用户光标位置
  action := "admit",                         -- 操作类型
  blockRange? := some {                      -- by块范围
    start := { line := 6, character := 0 },
    stop := { line := 8, character := 6 }
  },
  includeByOnSeq? := some false,             -- 不需要添加"by"
  returnWholeFile? := some true              -- 返回完整文件
}
```

#### 3. 服务器获取语法快照

**位置**: `MathEye.lean:628`

```lean
withWaitFindSnapAtPos params.pos fun snap => do
  -- snap 是当前文件的语法快照
  -- 包含完整的AST信息和上下文
```

#### 4. 确定容器范围

**位置**: `MathEye.lean:637-643`

```lean
let originalStx := chooseSmallestTacticSeq stxs r.tacticInfo.stx
let rr : RangeDto := match originalStx.getRange? with
  | some rg => RangeDto.fromStringRange text rg
  | none    => { start := params.pos, stop := params.pos }

-- 在我们的例子中：
-- originalStx 是整个 by 块的 tacticSeq
-- rr = {
--   start := { line := 6, character := 0 },  -- ":= by" 开始
--   stop := { line := 8, character := 6 }    -- "sorry" 结束
-- }
```

#### 5. 计算稳定位置

**位置**: `MathEye.lean:644-651`

```lean
let blockStartUtf8 := text.lspPosToUtf8Pos rr.start
let blockStopUtf8  := text.lspPosToUtf8Pos rr.stop
let lo := if blockStartUtf8.byteIdx + 1 < blockStopUtf8.byteIdx then ⟨blockStartUtf8.byteIdx + 1⟩ else blockStartUtf8
let hi := if blockStopUtf8.byteIdx > blockStartUtf8.byteIdx + 1 then ⟨blockStopUtf8.byteIdx - 1⟩ else blockStopUtf8
let stablePos := if hoverPos.byteIdx < lo.byteIdx then lo else if hoverPos.byteIdx > hi.byteIdx then hi else hoverPos

-- 在我们的例子中：
-- blockStartUtf8 = ⟨位置6行的开始⟩
-- blockStopUtf8 = ⟨位置8行"sorry"结束⟩
-- stablePos = ⟨用户光标位置，保持不变⟩
```

#### 6. 获取证明目标类型

**位置**: `MathEye.lean:722-782`

这是最复杂的部分，需要从AST中提取目标类型：

```lean
let tyStr? ← do
  -- 尝试多种策略获取目标类型
  -- 最终应该返回： "n = n" (字符串形式)
```

#### 7. 构建插入的have语句

**位置**: `MathEye.lean:654-655`

```lean
let name := s!"h_{params.pos.line}_{params.pos.character}"
let action := params.action.trim

-- 结果：
-- name = "h_7_2"  -- 基于光标位置生成唯一名称
-- action = "admit"  -- 确认是接受操作
```

#### 8. 构造新的AST

**位置**: `MathEye.lean:830-900`

```lean
-- 构造 have 语句的AST
let haveStx := buildHaveStatement name tyStr action

-- 在我们的例子中会生成：
-- have h_7_2 : n = n := by human_oracle

-- 构造 exact 语句的AST
let exactStx := buildExactStatement name

-- 生成：
-- exact h_7_2
```

#### 9. 重新组装tactic序列

**位置**: `MathEye.lean:900-950`

```lean
-- 原始tactic序列：[sorry]
-- 插入后的序列：[have h_7_2 : n = n := by human_oracle, exact h_7_2]
```

#### 10. 格式化输出

**位置**: `MathEye.lean:950-1000`

```lean
-- 使用Lean的PrettyPrinter格式化整个新的by块
let formattedText := formatTacticSeq newSeq

-- 输出结果：
-- have h_7_2 : n = n := by human_oracle
-- exact h_7_2
```

---

## 第三步：返回结果给VSCode

### 返回的InsertHaveByActionResult

```lean
{
  newText := "have h_7_2 : n = n := by human_oracle\nexact h_7_2",
  range := {
    start := { line := 6, character := 0 },
    stop := { line := 8, character := 6 }
  },
  success := true,
  errorMsg := none
}
```

---

## 第四步：VSCode应用更改

### extension.ts 中的应用逻辑

**位置**: `extension/src/extension.ts:172-180`

```typescript
// 验证返回的是完整文件范围
const wholeRangeReturned = res.range.start.line === 0 &&
                          res.range.start.character === 0 &&
                          res.range.end.line >= editor.document.lineCount - 1;

if (!wholeRangeReturned) {
    throw new Error('服务器未返回整篇替换范围');
}

// 创建WorkspaceEdit应用更改
const we = new vscode.WorkspaceEdit();
const fullRange = new vscode.Range(0, 0, editor.document.lineCount, 0);
we.replace(editor.document.uri, fullRange, res.newText);
await vscode.workspace.applyEdit(we);
```

---

## 最终结果

原始文件：
```lean
theorem debug_example (n : Nat) : n = n := by
  sorry
```

处理后的文件：
```lean
theorem debug_example (n : Nat) : n = n := by
  have h_7_2 : n = n := by human_oracle
  exact h_7_2
```

---

## 关键变量追踪总结

| 变量名 | 值 | 含义 |
|--------|-----|------|
| `params.pos` | `{line: 7, character: 2}` | 用户光标位置 |
| `params.action` | `"admit"` | 用户选择的操作 |
| `blockRange` | `{start: {line:6, char:0}, stop:{line:8, char:6}}` | by块范围 |
| `name` | `"h_7_2"` | 生成的假设变量名 |
| `tyStr` | `"n = n"` | 提取的目标类型 |
| `originalStx` | `tacticSeq([...])` | 原始的tactic序列AST |
| `newSeq` | `tacticSeq([haveStx, exactStx])` | 新的tactic序列AST |

这个跟踪显示了MathEye如何从一个简单的用户点击开始，经过复杂的AST操作，最终生成正确的Lean代码。

