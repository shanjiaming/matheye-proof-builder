# MathEye AST操作详解 - 核心机制理解

## 引言

MathEye最核心的创新在于**完全基于AST的证明编辑**。不同于传统的文本编辑方式，MathEye直接操作Lean的抽象语法树（AST），确保编辑的精确性和安全性。

---

## 核心概念

### 1. Syntax（语法树）
Lean中的`Syntax`是代码的AST表示，每个节点都包含：
- **kind**：节点类型（如`tacticSeq`, `have`, `exact`等）
- **range**：源代码中的位置范围
- **children**：子节点数组
- **value**：原子节点的值（如标识符、关键字等）

### 2. Tactic Sequence（战术序列）
在`by`块中的所有战术组成一个`tacticSeq`：
```lean
theorem example : P := by
  tactic1
  tactic2
  tactic3
-- 这是一个 tacticSeq，包含 [tactic1, tactic2, tactic3]
```

---

## 关键AST操作函数详解

### 1. `chooseSmallestTacticSeq` - 选择最小容器

**目的**：找到包含用户光标的最小战术序列容器

**输入**：
```lean
-- 用户光标在 "sorry" 前面
theorem debug_example (n : Nat) : n = n := by
  sorry  -- ← 用户光标在这里
```

**执行过程**：
```lean
def chooseSmallestTacticSeq (stxs : List Syntax) (fallback : Syntax) : Syntax :=
  -- 从路径中找到最小的 tacticSeq
  -- 在我们的例子中：整个 by 块的 tacticSeq
```

**输出**：
```lean
-- 返回包含整个 by 块的 tacticSeq AST节点
-- 范围：从 ":= by" 到 "sorry" 结束
```

### 2. `parseTacticSegments` - 解析战术片段

**目的**：将文本解析为AST节点

**输入**：
```lean
let haveText := "have h : n = n := by human_oracle"
let exactText := "exact h"
```

**执行过程**：
```lean
def parseTacticSegments (text : String) : Syntax :=
  -- 使用Lean's parser解析文本为AST
  -- haveText → haveStx (Have节点)
  -- exactText → exactStx (Exact节点)
```

**输出**：
```lean
-- haveStx: Have(kind: "have", children: [name, type, body])
-- exactStx: Exact(kind: "exact", children: [name])
```

### 3. `buildTacticSeq` - 重新构建战术序列

**目的**：将修改后的战术重新组装成序列

**输入**：
```lean
let originalSeq := [sorryStx]  -- 原始序列只有一个 sorry
let insertions := [haveStx, exactStx]  -- 要插入的新战术
```

**执行过程**：
```lean
def buildTacticSeq (original : Array Syntax) (insertions : Array Syntax) : Syntax :=
  -- 在 stablePos 位置插入新的战术
  -- 保留原有战术，插入新战术
```

**输出**：
```lean
-- newSeq: TacticSeq(kind: "tacticSeq", children: [haveStx, exactStx])
```

### 4. `formatTacticSeq` - 格式化输出

**目的**：将AST转换回格式化的Lean代码

**输入**：
```lean
let newSeq := tacticSeq([haveStx, exactStx])
```

**执行过程**：
```lean
def formatTacticSeq (seq : Syntax) : String :=
  -- 使用Lean's PrettyPrinter
  -- 自动处理缩进和换行
```

**输出**：
```lean
"have h_7_2 : n = n := by human_oracle
exact h_7_2"
```

---

## 完整AST操作流程图

```
原始代码：
theorem debug_example (n : Nat) : n = n := by
  sorry

     ↓ 用户点击"接受"

1. 定位容器：
   - 找到包含光标的 tacticSeq
   - 范围：[line6:0] 到 [line8:6]

2. 确定插入位置：
   - stablePos = 用户光标位置
   - 计算插入点（tacticSeq内的合适位置）

3. 获取目标类型：
   - 从AST中提取当前证明目标
   - tyStr = "n = n"

4. 构造新AST：
   - 解析 "have h_7_2 : n = n := by human_oracle"
   - 解析 "exact h_7_2"
   - 创建新的 Have 和 Exact 节点

5. 重新组装：
   - 原始序列：[sorryStx]
   - 新序列：[haveStx, exactStx]

6. 格式化输出：
   - 使用PrettyPrinter生成格式化代码
   - 处理缩进和换行

最终结果：
theorem debug_example (n : Nat) : n = n := by
  have h_7_2 : n = n := by human_oracle
  exact h_7_2
```

---

## 关键数据结构详解

### Syntax节点类型

```lean
inductive Syntax where
  | missing              -- 缺失的语法
  | node info kind args  -- 复合节点（有子节点）
  | atom info val        -- 原子节点（关键字、标识符等）
  | ident info raw val pre  -- 标识符节点
```

### 在我们的例子中

```lean
-- 原始的 sorry 节点
sorryStx := Syntax.atom ⟨sourceInfo⟩ "sorry"

-- 生成的 have 节点
haveStx := Syntax.node ⟨sourceInfo⟩ `Lean.Parser.Tactic.have #[
  Syntax.atom ⟨⟩ "have",
  Syntax.ident ⟨⟩ "h_7_2" `h_7_2 [],
  Syntax.atom ⟨⟩ ":",
  -- ... 类型和主体部分
]

-- 生成的 exact 节点
exactStx := Syntax.node ⟨sourceInfo⟩ `Lean.Parser.Tactic.exact #[
  Syntax.atom ⟨⟩ "exact",
  Syntax.ident ⟨⟩ "h_7_2" `h_7_2 []
]
```

---

## 安全性和精确性保证

### 1. 类型安全
- 所有操作都在编译时类型检查的Lean代码中进行
- 避免了字符串处理的错误可能性

### 2. 位置精确性
- 使用AST的range信息确定精确的编辑位置
- 避免了基于文本的启发式搜索

### 3. 格式一致性
- 使用Lean's官方PrettyPrinter确保格式统一
- 自动处理缩进、换行等格式问题

### 4. 语义完整性
- AST操作保持代码的语义结构
- 确保生成的代码在Lean中是有效的

---

## 调试技巧

### 查看AST结构
```lean
-- 在Lean中查看语法树
#eval IO.println (← Lean.Syntax.toString <$> parseTactic "have h : P := sorry")
```

### 检查范围信息
```lean
-- 查看节点的源代码范围
def debugRange (stx : Syntax) : String :=
  match stx.getRange? with
  | some rg => s!"Range: {rg.start} to {rg.stop}"
  | none => "No range"
```

这个AST操作机制是MathEye能够实现精确、安全证明编辑的核心。通过直接操作语法树而不是文本字符串，MathEye确保了编辑操作的可靠性和正确性。


