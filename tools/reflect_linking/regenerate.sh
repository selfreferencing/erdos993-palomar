#!/bin/bash
# regenerate.sh <repository root> <output root>
# Regenerates the eight reflective families from the ORIGINAL generated families found under
# <repository root>/Erdos993Lean/F4U/Light/Linking/Generated/.  Writes only below
# <output root>/Erdos993Lean/F4U/Light/Reflect/<FAMILY>/ (use the repository root itself to regenerate in place).
# Needs python3 with python-flint.  Core.lean and KernelRfl.lean are hand-written and are not produced here.
set -euo pipefail
REPO="${1:?repository root}"; OUT="${2:?output root}"; HERE="$(cd "$(dirname "$0")" && pwd)"
split_of() { case "$1" in DAG_D_B_01|DAG_H_B_01) echo pair;; *) echo key;; esac; }
for F in DAG_D_A_01 DAG_D_B_01 DAG_E1_A_01 DAG_E1_B_01 DAG_E2_A_01 DAG_E2_B_01 DAG_H_A_01 DAG_H_B_01; do
  python3 "$HERE/gen_family.py" "$F" "$REPO/Erdos993Lean/F4U/Light/Linking/Generated/$F" "$OUT" "$(split_of "$F")" | head -n 1
done
