#!/usr/bin/env bash
set -euo pipefail
# Wrapper to ensure Lean server runs within Lake environment of the repo root
# Usage: this script is used as vscode setting `lean4.executablePath`

REPO_ROOT=$(cd "$(dirname "$0")"/../.. && pwd)
cd "$REPO_ROOT"

# Ensure lake build artifacts are up-to-date (best effort)
if command -v lake >/dev/null 2>&1; then
  lake build MathEye >/dev/null 2>&1 || true
fi

exec lake env lean "$@"

