#!/usr/bin/env bash
# Fail closed: successful compilation alone does not remove a project axiom.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Theorems.Thm_StickyKakeya4_sticky_kakeya_four_dimensional \
  Theorems.Thm_StickyKakeya4_common_shading_obstruction
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean verification/AxiomReadback.lean | tee "$log"
python3 - "$log" <<'PY'
import pathlib, re, sys
text = pathlib.Path(sys.argv[1]).read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
reads = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", text, re.S)
if not reads:
    sys.exit('FAIL: no axiom readback was found')
failed = False
for name, raw in reads:
    extra = {x.strip() for x in raw.split(',') if x.strip()} - allowed
    if extra:
        print(f'FAIL: {name}: {", ".join(sorted(extra))}')
        failed = True
if failed:
    sys.exit(1)
print('PASS: all printed proof terms use only standard logical axioms')
PY
