# Current milestones: original-paper standard

The final target is unchanged: Definition 1.1 / Theorem 1.2 of the original
manuscript, namely Hausdorff dimension four for the unit front of a compact valid
full-direction marked family with packing-dimension-three unmarked carrier.
No new regularity, routing certificate, or energy bound is a final hypothesis.
See [ORIGINAL_PAPER_TARGETS.md](ORIGINAL_PAPER_TARGETS.md) for exact references.
The earlier eight-item proposal is preserved in `PROVE2ME_TARGETS.md`.

## 1. Exact collision identity

Existing theorem compiled in the pinned environment. It is the algebraic input
for the original residual-content route. A new quantitative collision-time
fiber bound is being developed; its status is tracked separately.

## 2. Contact/Maslov incidence

Existing matrix-pencil/Maslov incidence theorem compiled. This alone does not
construct mass-preserving geometric routing.

## 3. Borel selector and compact ambient front

Original Proposition 3.1 gives a Borel selector inside the compact datum.
Retain the original compact ambient front for weak limits and the final theorem.
The stronger Borel-selector-only target is explicitly archived in
`verification/ARCHIVED_TARGETS.md`; it is not assumed as an axiom.

## 4. Original source measure and residual content

Translate Definition 6.26 with its original source measure, collision-time
window, inverse-secant weight, and diagonal exclusions. Existing finite shaded
sources are not automatically a substitute for this measure-level object.
The residual/Frostman connection remains to be completed.

## 5. Finite occurrence-flow conservation

The scalar forest ledger is compiled. The new measure-valued ledger is compiled
and has standard-only axiom readback. Nodewise equality of measures implies the
terminal root-measure budget and its preservation under a fixed endpoint map.
This is an actual proved implication. Constructing the original geometric
routing forest satisfying that conservation remains open.

## 6. Source-faithful routing and terminal / paid / cross budgets

Original §§8–9 restrict ordered marked edge occurrences, not arbitrary tube
shadings. The new global terminal theorem is compiled and axiom-checked:

- disjoint occurrence restrictions preserve one root endpoint budget
- varying terminal caps imply a global near-diagonal direction band
- root product domination and original direction density give `8 C m T^3`
- `T^3 <= m q` gives `8 C m^2 q`
- a single global reversal allowance changes 8 to 16

The integrated forest theorem derives that terminal budget from nodewise
conservation. Still open: the actual hereditary routing construction,
endpoint-preserving extensions, geometric root/support hypotheses, stopping
schedule, and paid/cross-cap bounds. None is replaced by a hidden capacity field.

## 7. Relative residual / Frostman alternative

Follow Corollary 9.31 and the residual-content criterion, rather than requiring
the false arbitrary-shading universal estimate. Conditional finite-scale
Frostman implications already in the repository do not prove their missing
inputs. A concrete residual collision-time bridge is being checked, but the
finite-energy, slicing, and geometric alternative are still open.

## 8. Original compact marked closure and axiom audit

Use Theorem 9.32's intended residual/Frostman closure and transfer the conclusion
to the original compact front. The current legacy route still uses
`wang_zakharov_published_volume_estimate`. Repairing its API calls and compiling
it does not complete the requested internal proof.

Completion requires both an unchanged final theorem statement and transitive
kernel readback with no project-specific axioms or `sorryAx`. The full build and
that final readback remain separate checks from the successful new lemmas.
