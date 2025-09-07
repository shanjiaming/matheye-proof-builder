# 自己验证变量值 - 简单步骤

## 第一步：打开测试文件
在VSCode中打开：`simple_debug.lean`

## 第二步：定位光标
把光标放在 `sorry` 关键字的前面：
```lean
theorem simple_test : 1 = 1 := by
  -- 把光标放在这里 ↓
  sorry
```

## 第三步：运行MathEye命令
按 `Ctrl+Shift+P` (或 `Cmd+Shift+P` 在Mac上)，输入：
`MathEye: Insert Have (Admit)`

## 第四步：查看生成的日志文件
运行命令后，查看这些文件的内容：

### 查看RPC调用记录：
```bash
cat /Users/sjm/coding/projects/lean-plugin/matheye-proof-builder/tmp/matheye_rpc_called.log
```

### 查看参数值：
```bash
cat /Users/sjm/coding/projects/lean-plugin/matheye-proof-builder/tmp/debug_params.log
```

### 查看位置计算：
```bash
cat /Users/sjm/coding/projects/lean-plugin/matheye-proof-builder/tmp/debug_positions.log
```

### 查看变量名生成：
```bash
cat /Users/sjm/coding/projects/lean-plugin/matheye-proof-builder/tmp/debug_names.log
```

## 第五步：观察实际代码变化
运行MathEye命令后，你的代码会自动变成：
```lean
theorem simple_test : 1 = 1 := by
  have h_行号_列号 : 1 = 1 := by human_oracle
  exact h_行号_列号
```

## 关键要点
- **不要相信任何文档**，直接看这些日志文件
- **变量值都是动态的**，取决于你的光标位置
- **每次运行都会生成新的日志**，覆盖之前的
- **如果失败了**，检查日志中的错误信息

现在试试看，你会看到所有变量的具体值！

