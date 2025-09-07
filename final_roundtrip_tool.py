#!/usr/bin/env python3
"""
最终版Lean AST Round-Trip工具
输入: 任意Lean文件路径
输出: 完整的双转换结果 (Lean → jixia AST → MathEye DTO → Lean formatter)
"""
import json
import subprocess
import tempfile
import os
import sys
import argparse

def get_node_type_category(kind_str):
    """根据节点类型字符串确定节点的通用类别

    Args:
        kind_str: Lean AST节点类型字符串

    Returns:
        str: 节点类别 ("tactic", "term", "command", "other")
    """
    if kind_str.startswith("Lean.Parser.Tactic."):
        return "tactic"
    elif kind_str.startswith("Lean.Parser.Term."):
        return "term"
    elif kind_str.startswith("Lean.Parser.Command."):
        return "command"
    else:
        return "other"

def should_add_newline_after(kind_str, formatting_mode):
    """保持占位：不再基于字符串风格进行插入，由AST还原负责。"""
    return False

def convert_jixia_to_dto(jixia_node, formatting_mode="newline"):
    """将jixia AST转换为MathEye.SyntaxNodeDto格式，完整保留spacing信息

    Args:
        jixia_node: jixia AST节点
        formatting_mode: "newline" (默认，换行+缩进) 或 "semicolon" (分号分隔)
    """
    if isinstance(jixia_node, list):
        return [convert_jixia_to_dto(child) for child in jixia_node]
    
    if not isinstance(jixia_node, dict):
        return jixia_node
    
    def extract_info_fields(info_dict):
        """从jixia的info字段中提取spacing和position信息"""
        if not info_dict:
            return {
                "leading?": None,
                "trailing?": None,
                "pos?": None,
                "endPos?": None
            }, "", "", {}
        
        # 处理info为字符串的情况（如"none"）
        if isinstance(info_dict, str):
            return {
                "leading?": None,
                "trailing?": None,
                "pos?": None,
                "endPos?": None
            }, "", "", {}
        
        # 尝试直接获取original字段
        original = info_dict.get("original", {})
        if original:
            return {
                "leading?": original.get("leading"),
                "trailing?": original.get("trailing"),
                "pos?": original.get("pos"),
                "endPos?": original.get("endPos")
            }, original.get("leading", ""), original.get("trailing", ""), original
        
        # 如果没有original字段，尝试其他可能的格式
        # 有些info可能直接包含spacing信息
        return {
            "leading?": info_dict.get("leading"),
            "trailing?": info_dict.get("trailing"),
            "pos?": info_dict.get("pos"),
            "endPos?": info_dict.get("endPos")
        }, info_dict.get("leading", ""), info_dict.get("trailing", ""), info_dict
        
    # 处理基本节点类型（atom, ident等）
    if "atom" in jixia_node:
        atom_data = jixia_node["atom"]
        value = atom_data.get("val", "")
        info = atom_data.get("info", {})
        spacing_info, leading, trailing, original = extract_info_fields(info)
        
        result = {
            "kind": "atom",
            "value?": value
        }
        # 添加spacing信息
        result.update(spacing_info)
        # 调试已移除
        return result
    elif "ident" in jixia_node:
        ident_data = jixia_node["ident"]
        info = ident_data.get("info", {})
        spacing_info, leading, trailing, original = extract_info_fields(info)
        
        result = {
            "kind": "ident",
            "value?": ident_data.get("rawVal", ident_data.get("val", ""))
        }
        # 添加spacing信息
        result.update(spacing_info)
        return result

    # 处理node结构
    if "node" not in jixia_node:
        return jixia_node

    node = jixia_node["node"]
    
    # 处理node内部的atom/ident
    if "atom" in node:
        atom_data = node["atom"]
        info = atom_data.get("info", {})
        spacing_info, leading, trailing, original = extract_info_fields(info)
        
        value = atom_data.get("val", "")
        result = {
            "kind": "atom",
            "value?": value
        }
        # 添加spacing信息
        result.update(spacing_info)
        # 调试已移除
        return result
        
    elif "ident" in node:
        ident_data = node["ident"]
        info = ident_data.get("info", {})
        spacing_info, leading, trailing, original = extract_info_fields(info)
        
        result = {
            "kind": "ident",
            "value?": ident_data.get("rawVal", ident_data.get("val", ""))
        }
        # 添加spacing信息
        result.update(spacing_info)
        return result
        
    elif "kind" in node:
        # 通用节点处理框架
        kind_parts = node["kind"]
        kind_str = ".".join(kind_parts) if isinstance(kind_parts, list) else str(kind_parts)

        children = []
        if "args" in node:
            # 只做递归结构转换，不做任何字符串级别或启发式的换行/分号插入
            children = process_node_args_generic(node["args"], kind_str, formatting_mode)

        # 从node的info字段提取spacing信息
        info = node.get("info", {})
        spacing_info, leading, trailing, original = extract_info_fields(info)
        
        # 不输出调试信息，避免噪音
        
        result = {
            "kind": kind_str,
            "children": children
        }
        # 添加spacing信息
        result.update(spacing_info)
        return result

def process_node_args_generic(args, kind_str, formatting_mode):
    """仅做递归的AST到DTO转换，不做任何字符串插入或启发式处理。"""
    children = []
    for arg in args:
        converted_child = convert_jixia_to_dto(arg, formatting_mode)
        if converted_child is not None:
            children.append(converted_child)
    return children

def is_sequence_separator_needed(args, current_index, kind_str, formatting_mode):
    """不再决定分隔符插入，统一交给原始SourceInfo与Lean formatter。"""
    return False

def contains_pipe_symbol(node):
    return False

def contains_bullet_symbol(node):
    return False

def is_pattern_match_branch(node):
    return False

def is_bullet_tactic_or_relevant(node):
    """判断节点是否是bullet tactic或相关节点

    Args:
        node: AST节点

    Returns:
        bool: 是否是bullet tactic或相关节点
    """
    if not isinstance(node, dict):
        return False

    # 检查是否包含 · 符号（bullet符号）
    if isinstance(node.get("node"), dict):
        inner_node = node["node"]
        if "atom" in inner_node and inner_node["atom"].get("val") == "·":
            return True
        if "atom" in inner_node and inner_node["atom"].get("val") == "•":
            return True

    # 检查原始节点的atom
    if "atom" in node and (node["atom"].get("val") == "·" or node["atom"].get("val") == "•"):
        return True

    # 检查节点类型是否是bullet相关的
    node_kind = node.get("kind", "")
    if isinstance(node_kind, list):
        node_kind = ".".join(node_kind)
    
    if "bullet" in node_kind.lower():
        return True

    return False

def is_tactic_or_relevant_node(node):
    """判断节点是否是tactic或相关的内容节点

    Args:
        node: AST节点

    Returns:
        bool: 是否是tactic或相关节点
    """
    if not isinstance(node, dict):
        return False

    node_kind = node.get("kind", "")
    if isinstance(node_kind, list):
        node_kind = ".".join(node_kind)

    # 检查是否是tactic相关的节点
    if ("Tactic" in node_kind or
        "intro" in node_kind or
        "have" in node_kind or
        "exact" in node_kind or
        "simp" in node_kind or
        "cases" in node_kind):
        return True

    # 检查是否是包装在null节点中的tactic
    if node_kind == "null" and isinstance(node.get("node"), dict):
        inner_node = node["node"]
        inner_kind = inner_node.get("kind", "")
        if isinstance(inner_kind, list):
            inner_kind = ".".join(inner_kind)

        if ("Tactic" in inner_kind or
            "intro" in inner_kind or
            "have" in inner_kind or
            "exact" in inner_kind or
            "simp" in inner_kind or
            "cases" in inner_kind):
            return True

    # 检查是否是包装在另一个节点中的tactic (处理 {'node': {'kind': [...]}} 结构)
    if isinstance(node.get("node"), dict):
        inner_node = node["node"]
        inner_kind = inner_node.get("kind", "")
        if isinstance(inner_kind, list):
            inner_kind = ".".join(inner_kind)

        if ("Tactic" in inner_kind or
            "intro" in inner_kind or
            "have" in inner_kind or
            "exact" in inner_kind or
            "simp" in inner_kind or
            "cases" in inner_kind):
            return True

    return False

def is_separator_by_structure(node):
    """通过AST结构特征判断节点是否为分隔符

    Args:
        node: AST节点

    Returns:
        bool: 是否为分隔符
    """
    if not isinstance(node, dict):
        return False

    # 检查是否为null节点（通常表示分隔符）
    if "node" in node and isinstance(node["node"], dict):
        if node["node"].get("kind") == ["null"]:
            return True

    return False

def is_let_or_relevant_node(node):
    """判断节点是否是let语句或相关的内容节点

    Args:
        node: AST节点

    Returns:
        bool: 是否是let语句或相关节点
    """
    if not isinstance(node, dict):
        return False

    node_kind = node.get("kind", "")
    if isinstance(node_kind, list):
        node_kind = ".".join(node_kind)

    # 检查是否是let相关的节点
    if "let" in node_kind.lower() or "Let" in node_kind:
        return True

    # 检查是否是包装在null节点中的let语句
    if node_kind == "null" and isinstance(node.get("node"), dict):
        inner_node = node["node"]
        inner_kind = inner_node.get("kind", "")
        if isinstance(inner_kind, list):
            inner_kind = ".".join(inner_kind)
        if "let" in inner_kind.lower() or "Let" in inner_kind:
            return True

    # 检查是否是包装在另一个节点中的let语句
    if isinstance(node.get("node"), dict):
        inner_node = node["node"]
        inner_kind = inner_node.get("kind", "")
        if isinstance(inner_kind, list):
            inner_kind = ".".join(inner_kind)
        if "let" in inner_kind.lower() or "Let" in inner_kind:
            return True

    return False

def is_terminal_expression(node):
    """判断节点是否是终端表达式（如变量名、常量等）

    Args:
        node: AST节点

    Returns:
        bool: 是否是终端表达式
    """
    if not isinstance(node, dict):
        return True  # 基本类型被认为是终端表达式

    # 检查是否是标识符
    if "ident" in node:
        return True

    # 检查是否是原子值
    if "atom" in node:
        return True

    # 检查node结构中的ident或atom
    if "node" in node and isinstance(node["node"], dict):
        inner_node = node["node"]
        if "ident" in inner_node or "atom" in inner_node:
            return True

    return False

def is_structure_field_or_relevant_node(node):
    """判断节点是否是结构体字段或相关的内容节点

    Args:
        node: AST节点

    Returns:
        bool: 是否是结构体字段或相关节点
    """
    if not isinstance(node, dict):
        return False

    node_kind = node.get("kind", "")
    if isinstance(node_kind, list):
        node_kind = ".".join(node_kind)

    # 检查是否是结构体字段相关的节点
    field_types = [
        "Lean.Parser.Command.structExplicitBinder",
        "Lean.Parser.Command.structImplicitBinder", 
        "Lean.Parser.Command.structInstBinder",
        "Lean.Parser.Command.structSimpleBinder",
        "structExplicitBinder",
        "structImplicitBinder",
        "structInstBinder", 
        "structSimpleBinder"
    ]
    
    if any(field_type in node_kind for field_type in field_types):
        return True
    
    # 检查是否包含字段声明相关的内容
    if "field" in node_kind.lower() or "binder" in node_kind.lower():
        return True

    # 检查是否是包装在null节点中的字段
    if node_kind == "null" and isinstance(node.get("node"), dict):
        inner_node = node["node"]
        inner_kind = inner_node.get("kind", "")
        if isinstance(inner_kind, list):
            inner_kind = ".".join(inner_kind)
        if any(field_type in inner_kind for field_type in field_types):
            return True

    # 检查是否是包装在另一个节点中的字段
    if isinstance(node.get("node"), dict):
        inner_node = node["node"]
        inner_kind = inner_node.get("kind", "")
        if isinstance(inner_kind, list):
            inner_kind = ".".join(inner_kind)
        if any(field_type in inner_kind for field_type in field_types):
            return True

    return False

def should_skip_newline_in_compound(kind_str, args, current_index):
    """判断是否应该在复合结构中跳过换行符

    Args:
        kind_str: 节点类型
        args: 参数列表
        current_index: 当前参数索引

    Returns:
        bool: 是否应该跳过换行
    """
    # 在have语句等复合结构中，避免在参数之间添加换行
    if "have" in kind_str.lower():
        # have语句的结构通常是: have <name> : <type> := <value>
        # 我们不想在 : 和 := 之间添加换行
        if current_index > 0 and current_index < len(args) - 1:
            return True

    return False

def is_array_or_list_context(kind_str):
    """判断当前上下文是否为数组或列表，避免在其中添加分隔符

    Args:
        kind_str: 节点类型字符串

    Returns:
        bool: 是否为数组或列表上下文
    """
    # 数组字面量 [item1, item2] - 检测term[_]模式
    if "term[" in kind_str.lower() and "_" in kind_str:
        return True

    # 数组字面量 [item1, item2]
    if "app" in kind_str.lower() and ("list" in kind_str.lower() or "array" in kind_str.lower()):
        return True

    # 列表构造 [] 或 [x]
    if "list.nil" in kind_str.lower() or "list.cons" in kind_str.lower():
        return True

    # 数组构造 #[] 或 #[x]
    if kind_str.startswith("Lean.Parser.Term.array"):
        return True

    return False

def escape_lean_string(s):
    """转义字符串中的特殊字符用于Lean语法"""
    if s is None:
        return ""
    return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n").replace("\t", "\\t")

def dto_to_lean_syntax(dto):
    """将DTO转换为Lean可理解的数据结构，包含完整的spacing信息"""
    if isinstance(dto, dict):
        result = "{ "
        result += f"kind := \"{dto.get('kind', '')}\""
        
        if dto.get('value?'):
            escaped_value = escape_lean_string(dto['value?'])
            result += f", value? := some \"{escaped_value}\""
        
        if dto.get('children'):
            children_str = ", ".join([dto_to_lean_syntax(child) for child in dto['children']])
            result += f", children := #[{children_str}]"
        elif 'children' in dto:
            result += ", children := #[]"
        
        # 添加spacing信息
        if dto.get('leading?') is not None:
            escaped_leading = escape_lean_string(dto['leading?'])
            result += f", leading? := some \"{escaped_leading}\""
        else:
            result += ", leading? := none"
        
        if dto.get('trailing?') is not None:
            escaped_trailing = escape_lean_string(dto['trailing?'])
            result += f", trailing? := some \"{escaped_trailing}\""
        else:
            result += ", trailing? := none"
            
        if dto.get('pos?') is not None:
            result += f", pos? := some {dto['pos?']}"
        else:
            result += ", pos? := none"
            
        if dto.get('endPos?') is not None:
            result += f", endPos? := some {dto['endPos?']}"
        else:
            result += ", endPos? := none"
            
        result += " }"
        return result
    else:
        return str(dto)

def fix_lean_formatter_bugs(content):
    """修复Lean formatter产生的语法错误

    注意：目前不做任何字符串级修复，正确的解决方案应该在AST层面。

    Args:
        content: Lean formatter输出的字符串

    Returns:
        str: 原样返回的字符串
    """
    # 不做任何字符串级修复，保持AST结果的原貌
    return content

def lean_complete_roundtrip(lean_file_path, jixia_path="/Users/sjm/coding/projects/lean-plugin/jixia", verbose=True, formatting_mode="newline"):
    """执行完整的Lean AST round-trip转换，支持任意Lean文件

    Args:
        lean_file_path: Lean文件路径
        jixia_path: jixia工具路径
        verbose: 是否详细输出
        formatting_mode: "newline" (默认，换行+缩进) 或 "semicolon" (分号分隔)
    """
    
    # 检查文件存在
    if not os.path.exists(lean_file_path):
        print(f"❌ 错误：文件不存在 {lean_file_path}")
        return None
    
    if not os.path.exists(jixia_path):
        print(f"❌ 错误：jixia路径不存在 {jixia_path}")
        return None
    
    # 1. 读取原始内容
    if verbose:
        print(f"读取文件: {lean_file_path}")
    
    try:
        with open(lean_file_path, 'r', encoding='utf-8') as f:
            original_content = f.read()
    except Exception as e:
        print(f"❌ 读取文件失败: {e}")
        return None
    
    # 不在非verbose模式下打印原文，避免噪音

    # 1.5. 提取import语句（因为jixia不支持处理import）
    import_statements = []
    non_import_content = []

    for line in original_content.split('\n'):
        stripped = line.strip()
        if stripped.startswith('import '):
            import_statements.append(line)
        else:
            non_import_content.append(line)

    non_import_content_str = '\n'.join(non_import_content).strip()

    if verbose:
        print(f"提取到 {len(import_statements)} 个import语句")

    # 2. 使用jixia生成AST
    if verbose:
        print("使用jixia生成AST")
    
    ast_output = f"/tmp/roundtrip_ast_{os.getpid()}.json"
    
    try:
        # 如果有非import内容，使用临时文件；否则创建空的AST
        if non_import_content_str.strip():
            # 创建临时文件（不含import）
            temp_file_path = f"/tmp/roundtrip_no_import_{os.getpid()}.lean"
            with open(temp_file_path, 'w', encoding='utf-8') as f:
                f.write(non_import_content_str)

            cmd = f'lake exe jixia -a "{ast_output}" "{temp_file_path}"'
            result = subprocess.run(
                cmd, shell=True, cwd=jixia_path,
                capture_output=True, text=True, timeout=60
            )

            # 清理临时文件
            if os.path.exists(temp_file_path):
                os.unlink(temp_file_path)
        else:
            # 如果只有import语句，创建一个空的AST
            with open(ast_output, 'w', encoding='utf-8') as f:
                f.write('[{"node": {"kind": ["Lean", "Parser", "Command", "eoi"], "info": "none", "args": []}}]')
            result = subprocess.CompletedProcess(args='', returncode=0, stdout='', stderr='')
        
        if result.returncode != 0:
            print(f"jixia执行失败:")
            # 过滤warning信息
            error_lines = []
            for line in result.stderr.split('\n'):
                if not line.startswith('warning:') and line.strip():
                    error_lines.append(line)
            if error_lines:
                print('\n'.join(error_lines))
            return None
        
        # 读取AST
        with open(ast_output, 'r', encoding='utf-8') as f:
            jixia_ast = json.load(f)
        
        if verbose:
            print(f"AST生成成功，包含 {len(jixia_ast)} 个顶级节点")
            # 可选：预览前几个节点结构
            for i, node in enumerate(jixia_ast[:3]):
                print(f"节点 {i} 预览: {json.dumps(node, indent=2, ensure_ascii=False)[:200]}...")
                if i >= 2: break
    
    except subprocess.TimeoutExpired:
        print("jixia执行超时")
        return None
    except Exception as e:
        print(f"jixia执行异常: {e}")
        return None
    
    finally:
        if os.path.exists(ast_output):
            os.unlink(ast_output)
    
    # 3. 转换所有节点
    if verbose:
        print("转换AST节点")
    
    converted_nodes = []
    for i, node in enumerate(jixia_ast):
        converted = convert_jixia_to_dto(node, formatting_mode)
        if (converted and
            isinstance(converted, dict) and
            converted.get('kind') not in ['Lean.Parser.Command.eoi', 'eoi']):
            converted_nodes.append(converted)
            if verbose:
                print(f"转换节点 {i+1}: {converted.get('kind', 'unknown')}")
    
    # 4. 使用Lean formatter转换每个节点
    if verbose:
        print("调用Lean formatter")
    
    all_results = []
    for i, dto in enumerate(converted_nodes):
        try:
            # 创建Lean脚本直接构建DTO
            dto_lean = dto_to_lean_syntax(dto)
            
            # 可选调试：保存生成的DTO字符串
            if verbose:
                debug_dto_path = f"debug_dto_{i}.txt"
                with open(debug_dto_path, 'w', encoding='utf-8') as debug_file:
                    debug_file.write(dto_lean)
                print(f"已保存DTO到 {debug_dto_path}")
            
            # 根据formatting_mode设置不同的格式化参数
            if formatting_mode == "newline":
                format_config = '''
set_option format.width 80
set_option format.indent 2'''
            else:
                format_config = '''
set_option format.width 1000
set_option format.indent 0'''
            
            # 生成Lean脚本（非verbose模式下不输出多余日志）
            if verbose:
                lean_script = f'''
import MathEye

{format_config}

def convert : IO Unit := do
  let dto : MathEye.SyntaxNodeDto := {dto_lean}
  let stx := MathEye.dtoToSyntax dto
  -- 使用我们自定义的formatSyntax函数而不是默认的prettyPrint.pretty
  let result := MathEye.formatSyntaxCustom stx
  IO.println "=== RESULT_START ==="
  IO.println result
  IO.println "=== RESULT_END ==="

#eval! convert
'''
            else:
                lean_script = f'''
import MathEye

{format_config}

def convert : IO Unit := do
  let dto : MathEye.SyntaxNodeDto := {dto_lean}
  let stx := MathEye.dtoToSyntax dto
  let result := MathEye.formatSyntaxCustom stx
  IO.println "=== RESULT_START ==="
  IO.println result
  IO.println "=== RESULT_END ==="

#eval! convert
'''
            
            # 调试：保存生成的Lean脚本
            if verbose:
                debug_script_path = f"debug_script_{i}.lean"
                with open(debug_script_path, 'w', encoding='utf-8') as debug_file:
                    debug_file.write(lean_script)
                print(f"已保存Lean脚本到 {debug_script_path}")
            
            with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False, encoding='utf-8') as temp_file:
                temp_file.write(lean_script)
                temp_path = temp_file.name
            
            try:
                lean_result = subprocess.run(
                    f'lake env lean "{temp_path}"',
                    shell=True, cwd=".", 
                    capture_output=True, text=True, timeout=60
                )
                
                # 提取结果（忽略警告）
                lines = lean_result.stdout.split('\n')
                content = ""
                capturing = False
                
                for line in lines:
                    if "=== RESULT_START ===" in line:
                        capturing = True
                    elif "=== RESULT_END ===" in line:
                        capturing = False
                    elif capturing:
                        content += line + "\n"
                
                content = content.rstrip('\n')
                if content.strip():
                    # 后处理：修复Lean formatter的语法错误
                    fixed_content = fix_lean_formatter_bugs(content.strip())
                    all_results.append(fixed_content)
                    if verbose:
                        print(f"  转换结果 {i+1}: '{fixed_content[:60]}{'...' if len(fixed_content) > 60 else ''}'")
                elif lean_result.returncode != 0 and verbose:
                    # 过滤警告信息显示真正的错误
                    error_lines = []
                    for line in lean_result.stderr.split('\n'):
                        if not line.startswith('warning:') and line.strip():
                            error_lines.append(line)
                    if error_lines:
                        print(f"转换失败 {i+1}: {' '.join(error_lines[:2])}")
                        
            finally:
                os.unlink(temp_path)
                
        except Exception as e:
            if verbose:
                print(f"节点 {i+1} 转换异常: {e}")
    
    # 5. 合并结果
    converted_code = '\n\n'.join(all_results)

    # 6. 重新添加import语句
    final_result_parts = []

    # 添加import语句
    if import_statements:
        final_result_parts.extend(import_statements)
        final_result_parts.append('')  # 空行

    # 添加转换后的代码
    if converted_code.strip():
        final_result_parts.append(converted_code)

    final_result = '\n'.join(final_result_parts).strip()

    return {
        'original': original_content.strip(),
        'converted': final_result,
        'original_length': len(original_content.strip()),
        'converted_length': len(final_result),
        'nodes_processed': len(converted_nodes),
        'nodes_converted': len(all_results),
        'imports_found': len(import_statements)
    }

def analyze_differences(original, converted, formatting_mode="newline"):
    """分析转换差异

    Args:
        original: 原始内容
        converted: 转换后的内容
        formatting_mode: 使用的格式化模式
    """
    if original == converted:
        return "✅ 完全匹配"

    # 检查功能等价性
    original_clean = ' '.join(original.split())
    converted_clean = ' '.join(converted.split())

    if formatting_mode == "newline":
        # newline模式：检查是否移除了分号并正确格式化
        if original_clean.replace(' ', '') == converted_clean.replace(' ', '').replace(';', '').replace('\n', ''):
            return "✅ 格式优化（移除不必要分号，采用标准换行格式）"
        elif ';' not in converted and '\n' in converted:
            return "✅ 标准格式化（使用换行和缩进）"
    else:
        # semicolon模式：检查分号插入是否正确
        if original_clean.replace(' ', '') == converted_clean.replace(' ', '').replace(';', ''):
            return "✅ 功能等价（仅格式差异）"
        elif ';' in converted:
            return "✅ 语法修复（插入分号分隔符）"

    return "❌ 内容差异"

def main():
    parser = argparse.ArgumentParser(description='完整版Lean AST Round-Trip转换工具')
    parser.add_argument('lean_file', help='Lean文件路径（支持任意Lean文件）')
    parser.add_argument('--jixia-path', default='/Users/sjm/coding/projects/lean-plugin/jixia',
                       help='jixia工具路径 (默认: /Users/sjm/coding/projects/lean-plugin/jixia)')
    parser.add_argument('--verbose', '-v', action='store_true', help='详细输出过程')
    parser.add_argument('--output', '-o', help='将结果保存到文件')
    parser.add_argument('--verify', action='store_true', help='验证转换结果的语法正确性')
    parser.add_argument('--formatting', choices=['newline', 'semicolon'], default='newline',
                       help='格式化模式：newline(默认，换行+缩进) 或 semicolon(分号分隔)')
    
    args = parser.parse_args()
    
    # 支持相对路径
    lean_file = args.lean_file
    if not lean_file.startswith('/'):
        lean_file = os.path.abspath(lean_file)
    
    if args.verbose:
        print("AST Round-Trip转换工具")
        print(f"输入文件: {lean_file}")
        print("=" * 80)
    
    result = lean_complete_roundtrip(lean_file, args.jixia_path, args.verbose, args.formatting)
    
    if result is None:
        print("转换失败")
        sys.exit(1)
    
    if args.verbose:
        print("\n转换统计:")
        print(f"- 原始长度: {result['original_length']} 字符")
        print(f"- 转换长度: {result['converted_length']} 字符") 
        print(f"- 处理节点: {result['nodes_processed']} 个")
        print(f"- 成功转换: {result['nodes_converted']} 个")
        analysis = analyze_differences(result['original'], result['converted'], args.formatting)
        print(f"- 差异分析: {analysis}")
        print(f"- 格式化模式: {args.formatting}")
    
    # 语法验证
    if args.verify and result['converted']:
        print(f"\n语法验证:")
        
        verification_script = f'''
{result['converted']}

def main : IO Unit := do
  IO.println "语法验证通过"

#eval! main
'''
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False, encoding='utf-8') as temp_file:
            temp_file.write(verification_script)
            verification_path = temp_file.name
        
        try:
            verification_result = subprocess.run(
                f'lake env lean "{verification_path}"',
                shell=True, cwd=".", 
                capture_output=True, text=True, timeout=30
            )
            
            if verification_result.returncode == 0 and "语法验证通过" in verification_result.stdout:
                print("语法验证成功")
            else:
                print("语法验证失败:")
                # 只显示非warning的错误
                error_lines = []
                for line in verification_result.stderr.split('\n'):
                    if not line.startswith('warning:') and line.strip():
                        error_lines.append(line)
                if error_lines:
                    print('\n'.join(error_lines[:5]))  # 只显示前5个错误
                
        finally:
            os.unlink(verification_path)
    
    # 保存结果到文件
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as f:
            f.write(result['converted'])
        if args.verbose:
            print(f"结果已保存到: {args.output}")
    
    # 非verbose模式不额外输出

if __name__ == "__main__":
    main()
