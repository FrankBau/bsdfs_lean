#!/usr/bin/env bash
# Smoke test: the traces of the Lean executable must equal those of the Python reference implementation.
# Usage: ./smoke_test.sh [--clean]      --clean: rebuild the Lean project from scratch first (about 30 s instead of 2 s)
set -euo pipefail
cd "$(dirname "$0")"                                   # repository root (lean/)

if [[ "${1:-}" == "--clean" ]]; then (cd bsdfs && lake clean); fi

(cd Python && "${PYTHON:-python}" smoke_gen.py)        # writes Python/cases.txt and Python/expected.txt (needs networkx)
(cd bsdfs && lake build)                               # inside bsdfs/, so elan picks bsdfs/lean-toolchain
(cd bsdfs && lake exe bsdfs ../Python/cases.txt) > Python/lean_out.txt
diff --strip-trailing-cr -q Python/lean_out.txt Python/expected.txt && echo "smoke test passed: traces identical"
