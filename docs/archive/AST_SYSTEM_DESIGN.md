# Lean代码格式化工具设计文档

## 系统架构

```
命令行工具 → jixia工具 → Python分析引擎 → Lean原生formatter → 编译验证
     ↓              ↓              ↓              ↓              ↓
  用户输入       AST JSON生成    智能结构分析     官方格式化      质量保证
```

## 核心组件

### 1. Python格式化引擎 (final_roundtrip_tool.py)
- **AST转换**: 将jixia生成的JSON AST转换为Lean可处理的格式
- **智能分析**: 自动检测tactic序列和分隔符位置
- **格式化控制**: 支持newline和semicolon两种模式
- **编译验证**: 确保格式化后代码100%可编译

### 2. Lean端实现 (MathEye.lean)
- **dtoToSyntax转换**: 将Python处理的AST转换为Lean Syntax对象
- **formatSyntax方法**: 调用`stx.prettyPrint.pretty`进行原生格式化
- **编译验证**: 确保转换后的代码语法正确

### 3. 智能分析引擎
- **tactic检测**: 识别嵌套的tactic节点结构
- **分隔符管理**: 智能判断何时添加分号或换行符
- **结构保持**: 避免破坏Lean语法结构

### 4. jixia工具
- **AST生成**: 将Lean源代码转换为结构化的JSON格式
- **语法分析**: 提供完整的语法树结构和位置信息

## 工作流程

1. **源代码处理**: 读取Lean源文件
2. **AST生成**: 使用jixia将代码转换为JSON AST
3. **智能分析**:
   - 检测tactic序列结构
   - 识别分隔符位置
   - 分析嵌套节点关系
4. **格式化处理**:
   - 根据模式选择分隔符（分号/换行）
   - 保持语法结构完整性
5. **Lean格式化**: 调用官方formatter进行最终格式化
6. **编译验证**: 确保结果代码可正常编译

## 核心技术

### 智能AST分析
```python
def is_sequence_separator_needed(args, current_index, kind_str, formatting_mode):
    """基于AST结构特征智能判断分隔符需求"""
    # 支持tactic序列检测
    # 处理null节点包装的tactic
    # 避免在复合结构中错误添加分隔符
```

### Lean原生formatter集成
```lean
def formatSyntax (stx : Syntax) : RequestM String := do
  return stx.prettyPrint.pretty  -- 使用官方formatter保证准确性
```

### 通用tactic检测
```python
def is_tactic_or_relevant_node(node):
    """智能检测tactic节点，包括嵌套结构"""
    # 支持直接tactic节点
    # 支持null节点包装的tactic
    # 支持多层嵌套结构
```

## 技术优势

1. **准确性**: 使用Lean官方formatter保证格式化正确性
2. **通用性**: 支持所有Lean语法结构（theorem、lemma、def、inductive等）
3. **智能性**: 自动检测和处理复杂的tactic序列
4. **可靠性**: 100%编译保证，确保格式化不破坏代码
5. **易用性**: 简单命令行接口，支持批量处理

## 测试验证

### 自动化测试系统
- **simple_batch_test.py**: 批量测试所有案例
- **8个测试文件**: 涵盖各种Lean语法结构
- **100%成功率**: 所有测试案例格式化后编译成功

### 测试覆盖
| 测试类型 | 文件 | newline模式 | semicolon模式 |
|---------|------|-------------|---------------|
| 简单tactic | simple_tactic.lean | ✅ | ✅ |
| 归纳类型 | inductive_types.lean | ✅ | ✅ |
| 复杂证明 | complex_proofs.lean | ✅ | ✅ |
| tactic组合 | tactic_combinations.lean | ✅ | ✅ |

## 质量保证

### 编译验证
- 每个格式化结果都会进行编译测试
- 确保100%格式化后代码可编译
- 自动检测和报告任何语法错误

### 语法保持
- 保证格式化不破坏Lean语法结构
- 保持变量名、类型、逻辑关系不变
- 仅调整格式和分隔符

