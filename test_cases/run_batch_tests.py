#!/usr/bin/env python3
"""
Lean代码格式化批量测试脚本
自动测试所有测试用例文件的格式化和编译
"""
import subprocess
import os
import sys
import time
from pathlib import Path

class LeanFormatterTester:
    def __init__(self, project_root):
        self.project_root = Path(project_root)
        self.test_dir = self.project_root / "test_cases"
        self.tool_path = self.project_root / "final_roundtrip_tool.py"

        # 测试用例配置
        self.test_cases = {
            "test_01_basic_theorem.lean": "基础theorem测试",
            "test_02_simp_proofs.lean": "simp证明测试",
            "test_03_cases_proofs.lean": "cases证明测试",
            "test_04_induction_proofs.lean": "induction证明测试",
            "test_05_have_exact_proofs.lean": "have/exact证明测试",
            "test_06_rewrite_proofs.lean": "rewrite证明测试",
            "test_07_def_recursive.lean": "递归定义测试",
            "test_08_inductive_types.lean": "归纳类型测试",
            "test_09_structures.lean": "结构测试",
            "test_10_namespace_section.lean": "命名空间section测试",
            "test_11_math_proofs.lean": "数学证明测试",
            "test_12_apply_tactic.lean": "apply tactic测试",
            "test_13_ring_tactic.lean": "ring tactic测试",
            "test_14_linarith_tactic.lean": "linarith tactic测试",
            "test_15_norm_num_tactic.lean": "norm_num tactic测试",
            "test_16_constructor_tactic.lean": "constructor tactic测试",
            "test_17_split_tactic.lean": "split tactic测试",
            "test_18_intro_tactic.lean": "intro tactic测试",
            "test_19_exact_tactic.lean": "exact tactic测试",
            "test_20_mixed_tactics.lean": "混合tactics测试",
            "simple_tactic.lean": "简单tactic测试",
            "tactic_combinations.lean": "tactic组合测试",
            "inductive_types.lean": "归纳类型定义测试",
            "complex_proofs.lean": "复杂证明测试"
        }

        # 统计信息
        self.stats = {
            "total_tests": 0,
            "passed_tests": 0,
            "failed_tests": 0,
            "compilation_errors": 0,
            "formatting_errors": 0
        }

    def print_header(self, title):
        """打印标题"""
        print(f"\n{'='*60}")
        print(f"🎯 {title}")
        print(f"{'='*60}")

    def print_subheader(self, title):
        """打印子标题"""
        print(f"\n{'-'*50}")
        print(f"📋 {title}")
        print(f"{'-'*50}")

    def run_command(self, cmd, description, timeout=30):
        """运行命令并返回结果"""
        try:
            print(f"🔧 {description}...")
            result = subprocess.run(
                cmd,
                shell=True,
                cwd=self.project_root,
                capture_output=True,
                text=True,
                timeout=timeout
            )
            return result.returncode == 0, result.stdout, result.stderr
        except subprocess.TimeoutExpired:
            print(f"❌ {description} 超时")
            return False, "", "Timeout"
        except Exception as e:
            print(f"❌ {description} 异常: {e}")
            return False, "", str(e)

    def test_original_compilation(self, file_path):
        """测试原始文件的编译"""
        success, stdout, stderr = self.run_command(
            f'lake env lean "{file_path}"',
            f"测试原始文件编译: {file_path.name}"
        )

        if success:
            print("✅ 原始文件编译成功")
            return True
        else:
            print("❌ 原始文件编译失败")
            # 只显示关键错误信息
            error_lines = stderr.split('\n')[:3]
            for line in error_lines:
                if line.strip() and not line.startswith('warning'):
                    print(f"   {line}")
            return False

    def test_formatting(self, file_path, mode):
        """测试文件格式化"""
        output_file = f"/tmp/{file_path.stem}_{mode}_{int(time.time())}.lean"

        success, stdout, stderr = self.run_command(
            f'python3 final_roundtrip_tool.py "{file_path}" --formatting {mode} --output "{output_file}" --verbose',
            f"格式化文件 ({mode}模式)"
        )

        if not success:
            print(f"❌ 格式化失败 ({mode}模式)")
            self.stats["formatting_errors"] += 1
            return False, None

        print(f"✅ 格式化成功 ({mode}模式)")
        return True, output_file

    def test_formatted_compilation(self, formatted_file, mode):
        """测试格式化后文件的编译"""
        success, stdout, stderr = self.run_command(
            f'lake env lean "{formatted_file}"',
            f"测试格式化后文件编译 ({mode}模式)"
        )

        if success:
            print(f"✅ 格式化后文件编译成功 ({mode}模式)")
            return True
        else:
            print(f"❌ 格式化后文件编译失败 ({mode}模式)")
            # 显示错误信息
            error_lines = stderr.split('\n')[:5]
            for line in error_lines:
                if line.strip() and not line.startswith('warning'):
                    print(f"   {line}")
            self.stats["compilation_errors"] += 1
            return False

    def run_single_test(self, file_path, description):
        """运行单个测试用例"""
        self.print_subheader(f"{description} - {file_path.name}")

        if not file_path.exists():
            print(f"⚠️  测试文件不存在: {file_path}")
            return False

        # 1. 测试原始文件编译
        if not self.test_original_compilation(file_path):
            print(f"⚠️  跳过格式化测试，因为原始文件编译失败")
            return False

        test_passed = True

        # 2. 测试newline模式
        format_success, formatted_file = self.test_formatting(file_path, "newline")
        if format_success and formatted_file:
            if self.test_formatted_compilation(formatted_file, "newline"):
                self.stats["passed_tests"] += 1
            else:
                test_passed = False
            self.stats["total_tests"] += 1

        # 3. 测试semicolon模式
        format_success, formatted_file = self.test_formatting(file_path, "semicolon")
        if format_success and formatted_file:
            if self.test_formatted_compilation(formatted_file, "semicolon"):
                self.stats["passed_tests"] += 1
            else:
                test_passed = False
            self.stats["total_tests"] += 1

        return test_passed

    def run_all_tests(self):
        """运行所有测试"""
        self.print_header("Lean代码格式化批量测试")

        print(f"📁 测试目录: {self.test_dir}")
        print(f"🛠️  工具路径: {self.tool_path}")
        print(f"📋 测试用例数量: {len(self.test_cases)}")

        if not self.tool_path.exists():
            print(f"❌ 工具文件不存在: {self.tool_path}")
            return False

        all_passed = True

        for filename, description in self.test_cases.items():
            file_path = self.test_dir / filename
            if not self.run_single_test(file_path, description):
                all_passed = False

        # 打印最终统计
        self.print_header("测试结果统计")

        print(f"📊 总测试数: {self.stats['total_tests']}")
        print(f"✅ 通过测试: {self.stats['passed_tests']}")
        print(f"❌ 失败测试: {self.stats['failed_tests']}")
        print(f"🔧 格式化错误: {self.stats['formatting_errors']}")
        print(f"⚡ 编译错误: {self.stats['compilation_errors']}")

        success_rate = (self.stats['passed_tests'] / self.stats['total_tests'] * 100) if self.stats['total_tests'] > 0 else 0
        print(f"📈 成功率: {success_rate:.1f}%")
        if all_passed and success_rate == 100.0:
            print("\n🎉 所有测试通过！格式化工具运行完美！")
            return True
        else:
            print("\n⚠️  有测试失败，需要检查")
            return False

def main():
    """主函数"""
    project_root = Path(__file__).parent.parent

    if not (project_root / "final_roundtrip_tool.py").exists():
        print(f"❌ 找不到工具文件: {project_root}/final_roundtrip_tool.py")
        sys.exit(1)

    tester = LeanFormatterTester(project_root)
    success = tester.run_all_tests()

    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()
