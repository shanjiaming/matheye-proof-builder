#!/usr/bin/env python3
"""
简化的Lean代码格式化批量测试脚本
"""
import subprocess
import os
from pathlib import Path

def test_file(file_path, mode):
    """测试单个文件的格式化"""
    print(f"\n🧪 测试: {file_path.name} ({mode}模式)")

    # 测试原始文件编译
    result = subprocess.run(
        f'lake env lean "{file_path}"',
        shell=True,
        cwd=file_path.parent.parent,
        capture_output=True,
        text=True,
        timeout=30
    )

    if result.returncode != 0:
        print(f"❌ 原始文件编译失败")
        return False

    # 格式化文件
    output_file = f"/tmp/test_{file_path.stem}_{mode}.lean"
    try:
        format_result = subprocess.run(
            f'python3 final_roundtrip_tool.py "{file_path}" --formatting {mode} --output "{output_file}"',
            shell=True,
            cwd=file_path.parent.parent,
            capture_output=True,
            text=True,
            timeout=30
        )
    except subprocess.TimeoutExpired:
        print(f"❌ 格式化超时 (10秒)")
        return False

    if format_result.returncode != 0:
        print(f"❌ 格式化失败: {format_result.stderr[:200]}...")
        return False

    # 测试格式化后文件编译
    compile_result = subprocess.run(
        f'lake env lean "{output_file}"',
        shell=True,
        cwd=file_path.parent.parent,
        capture_output=True,
        text=True,
        timeout=30
    )

    if compile_result.returncode != 0:
        print(f"❌ 格式化后编译失败")
        return False

    print(f"✅ {mode}模式测试通过")
    return True

def main():
    print("🚀 通用处理逻辑批量测试")
    print("=" * 50)

    test_dir = Path(__file__).parent
    test_files = [
        "test_01_basic_theorem.lean",
        "test_02_simp_proofs.lean",
        "test_03_cases_proofs.lean",
        "test_04_induction_proofs.lean",
        "test_05_have_exact_proofs.lean",
        "test_06_rewrite_proofs.lean",
        "test_07_def_recursive.lean",
        "test_08_inductive_types.lean",
        "test_09_structures.lean",
        "test_10_namespace_section.lean",
        "test_11_math_proofs.lean",
        "test_12_apply_tactic.lean",
        "test_13_ring_tactic.lean",
        "test_14_linarith_tactic.lean",
        "test_15_norm_num_tactic.lean",
        "test_16_constructor_tactic.lean",
        "test_17_split_tactic.lean",
        "test_18_intro_tactic.lean",
        "test_19_exact_tactic.lean",
        "test_20_mixed_tactics.lean"
    ]

    total_tests = 0
    passed_tests = 0

    for filename in test_files:
        file_path = test_dir / filename
        if not file_path.exists():
            print(f"⚠️  跳过: {filename} (文件不存在)")
            continue

        # 测试newline模式
        if test_file(file_path, "newline"):
            passed_tests += 1
        total_tests += 1

        # 测试semicolon模式
        if test_file(file_path, "semicolon"):
            passed_tests += 1
        total_tests += 1

    print(f"\n{'='*50}")
    print("📊 测试结果统计")
    print(f"总测试数: {total_tests}")
    print(f"通过测试: {passed_tests}")
    print(f"失败测试: {total_tests - passed_tests}")

    success_rate = (passed_tests / total_tests * 100) if total_tests > 0 else 0
    print(f"成功率: {success_rate:.1f}%")
    if passed_tests == total_tests:
        print("\n🎉 所有测试通过！通用处理逻辑完全可用")
        return True
    else:
        print("\n⚠️  有测试失败，需要检查")
        return False

if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
