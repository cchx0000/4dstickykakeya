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
expected = {
    'StickyKakeya4.exact_collision_identity',
    'StickyKakeya4.borel_selector_reduction',
    'StickyKakeya4.packing_selector_to_finite_scale_sources',
    'StickyKakeya4.hereditary_finite_scale_to_frostman',
    'StickyKakeya4.selector_closure',
    'StickyKakeya4.sticky_kakeya_four_dimensional',
    'StickyKakeya4.commonShading_union_bound_iff',
    'StickyKakeya4.commonShading_energy_bound_iff',
}
seen = {name for name, _ in reads}
seen.update(re.findall(r"'([^']+)' does not depend on any axioms", text))
missing = expected - seen
if missing:
    sys.exit('FAIL: missing axiom readbacks: ' + ', '.join(sorted(missing)))
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
