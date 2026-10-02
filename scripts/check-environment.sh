#!/usr/bin/env bash
# Read-only pin validation. ELAN_HOME/PATH may point to an isolated installation.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lean >/dev/null || { echo 'lean is not on PATH; install the pinned toolchain with elan' >&2; exit 1; }
command -v lake >/dev/null || { echo 'lake is not on PATH' >&2; exit 1; }
expected_lean=$(cat lean-toolchain)
[[ "$expected_lean" == 'leanprover/lean4:v4.33.1' ]]
lean --version
lake --version
lean --version | grep -Fq 'version 4.33.1,'
for pin in \
  'mathlib 0df444a360eaa60ab8c11dca51a86af692955474' \
  'LeanFormalizations dd46c17a2a034d7bfa0df02e7f77834d35592864'; do
  read -r name sha <<< "$pin"
  actual=$(git -C ".lake/packages/$name" rev-parse HEAD)
  [[ "$actual" == "$sha" ]] || { echo "$name revision mismatch: $actual" >&2; exit 1; }
  printf '%s %s\n' "$name" "$actual"
done
lake build Solutions.SmokeTest
