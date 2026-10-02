# Current milestones: original-paper standard

The final target is unchanged: Definition 1.1 / Theorem 1.2 of the original
manuscript, namely Hausdorff dimension four for the unit front of a compact valid
full-direction marked family with packing-dimension-three unmarked carrier.
No new regularity, routing certificate, or energy bound is a final hypothesis.
See [ORIGINAL_PAPER_TARGETS.md](ORIGINAL_PAPER_TARGETS.md) for exact references.
The earlier eight-item proposal is preserved in `PROVE2ME_TARGETS.md`.

## 1. Exact collision identity

Existing theorem compiled in the pinned environment. It is the algebraic input
for the original residual-content route. The quantitative collision-time fiber
bound and its Tonelli integration are
now strictly compiled and axiom-checked; they retain explicit near-direction
and time-window terms.

## 2. Contact/Maslov incidence

Existing matrix-pencil/Maslov incidence theorem compiled. This alone does not
construct mass-preserving geometric routing.

## 3. Borel selector and compact ambient front

Original Proposition 3.1 gives a Borel selector inside the compact datum.
The existing reduction is compiled and has standard-only axiom readback.
Retain the original compact ambient front for weak limits and the final theorem.
The stronger Borel-selector-only target is explicitly archived in
`verification/ARCHIVED_TARGETS.md`; it is not assumed as an axiom.

## 4. Original source measure and residual content

The general weighted residual-content function and its measurability are
checked, retaining collision-time windows, inverse-secant weights, and the
nonzero-secant cutoff. Instantiation on the full original selector/occurrence
construction and its geometric power bound remain open. Existing shaded
sources do not automatically supply this measure-level input.

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
conservation. Checked Markov-kernel lemmas now derive inherited endpoint
preservation and density-root domination for actual probability-label
extensions and disjoint fractional restrictions. The actual old-neighbor
conditional law and degree-density disintegration are now constructed with
standard-Borel kernels. A checked fixed-angle guardrail shows that shrinking
terminal caps alone leaves all unpaid root mass in the cross-cap complement.
Still open: the actual geometric routing kernels and cuts, their conservation
and root/support invariants, stopping schedule, and paid/cross-cap bounds. None is replaced by a hidden capacity field.

## 7. Relative residual / Frostman alternative

Follow Corollary 9.31 and the residual-content criterion, rather than requiring
the false arbitrary-shading universal estimate. Conditional finite-scale
Frostman implications already in the repository do not prove their missing
inputs. The concrete residual collision-time bridge is checked, including its
explicit
near-direction error; finite-energy, slicing, residual power bounds, and the
geometric alternative are still open.

## 8. Original compact marked closure and axiom audit

Use Theorem 9.32's intended residual/Frostman closure and transfer the conclusion
to the original compact front. The current legacy route still uses
`wang_zakharov_published_volume_estimate`. Repairing its API calls and compiling
it does not complete the requested internal proof.

Completion requires both an unchanged final theorem statement and transitive
kernel readback with no project-specific axioms or `sorryAx`. The full
116-module build now passes. The final readback still reports the WZ
project axiom; the unconditional theorem remains incomplete.
