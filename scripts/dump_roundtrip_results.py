#!/usr/bin/env python3
"""
Dump round-trip outputs for all testcases to a single log file.

For each .lean test in test_cases (excluding generated/debug files), run
final_roundtrip_tool.py in both formatting modes (newline, semicolon), and
append the converted output to test_cases/roundtrip_outputs.log with headers.
Optionally record whether the converted output compiles under `lake env lean`
(enable with --compile).
"""
import subprocess
import argparse
from pathlib import Path
import os
import sys

REPO_ROOT = Path(__file__).resolve().parents[1]
TEST_DIR = REPO_ROOT / 'test_cases'
LOG_FILE = TEST_DIR / 'roundtrip_outputs.log'

def is_test_file(p: Path) -> bool:
    if p.suffix != '.lean':
        return False
    name = p.name
    if name.startswith('out_') or name.startswith('debug_'):
        return False
    return True

def run_roundtrip(src: Path, mode: str, out: Path) -> bool:
    cmd = [
        sys.executable, str(REPO_ROOT / 'final_roundtrip_tool.py'),
        str(src), '--formatting', mode, '--output', str(out)
    ]
    r = subprocess.run(cmd, cwd=REPO_ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        return False
    return True

def compile_lean(p: Path) -> (bool, str):
    r = subprocess.run(
        ['lake', 'env', 'lean', str(p)], cwd=REPO_ROOT,
        capture_output=True, text=True
    )
    if r.returncode == 0:
        return True, ''
    # Extract first non-warning line from stderr or stdout
    lines = (r.stderr or r.stdout).splitlines()
    msg = ''
    for ln in lines:
        if ln.startswith('warning:') or not ln.strip():
            continue
        msg = ln
        break
    return False, msg

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--compile', action='store_true', help='Verify each output with lake env lean')
    args = ap.parse_args()
    tests = sorted([p for p in TEST_DIR.iterdir() if is_test_file(p)])
    if not tests:
        print('No test files found in test_cases', file=sys.stderr)
        sys.exit(1)

    with LOG_FILE.open('w', encoding='utf-8') as log:
        log.write('Round-Trip Outputs Log\n')
        log.write('='*80 + '\n\n')
        for src in tests:
            for mode in ('newline', 'semicolon'):
                out = TEST_DIR / f"out_{src.stem}_{mode}.lean"
                ok = run_roundtrip(src, mode, out)
                if not ok:
                    log.write(f"[FAIL] {src.name} ({mode}) — conversion failed\n\n")
                    continue
                status = ''
                if args.compile:
                    compiled, msg = compile_lean(out)
                    status = f" | Compile: {'OK' if compiled else 'FAIL: ' + msg}"
                log.write(f"File: {src.name} | Mode: {mode}{status}\n")
                log.write('-'*80 + '\n')
                try:
                    content = out.read_text(encoding='utf-8')
                except Exception as e:
                    content = f"<read error: {e}>"
                log.write(content)
                log.write('\n\n')
        log.write('='*80 + '\n')
    print(f"Wrote log: {LOG_FILE}")

if __name__ == '__main__':
    main()
