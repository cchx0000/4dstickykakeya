# Prove2Me / 4D Sticky Kakeya verification report

Date: 2026-10-02 UTC. Baseline: `d208ddf4544cbb9ed05e4c848a83b07985b28e26`.

## Executive result

The repository's eight-milestone proposal is not complete. The user has designated the original paper as the final authority; see `ORIGINAL_PAPER_TARGETS.md`. In particular, milestone
6's estimate for **every fractional shading restriction** is too strong: a
common-ball restriction of many distinct radial lines has mass/union ratio equal
to the number of lines. This is a mathematical obstruction, separate from the
repairable Lean API mismatches. The final theorem currently depends on the
project axiom `wang_zakharov_published_volume_estimate`.

No Lean target statement, definition, or project axiom has been silently weakened or removed. The old milestone proposal must be corrected where it does not match the original paper. No server proof has been submitted. The user has explicitly authorized progress commits and pushes to an independent work branch; publication status is recorded separately.

## Environment

- Lean: `leanprover/lean4:v4.33.1`, release commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- LeanFormalizations: `dd46c17a2a034d7bfa0df02e7f77834d35592864`
- Official Prove2Me workspace: commit
  `4bb28221f86306b70b58f8119c4413025d09b302`, skill/API version `0.11.6`
- Public API health response: status `ok`, version `0.11.6`, observed
  `2026-10-02T03:02:07Z`
- Local verification does not require a Prove2Me account. Authenticated mission
  lookup and server verification were not configured: no API credential was
  supplied, generated, stored, or transmitted.

Official setup references:
[Lean setup](https://github.com/prove2me/prove2me_workspace/blob/main/references/lean-setup.md),
[API setup](https://github.com/prove2me/prove2me_workspace/blob/main/references/setup.md).

The workspace layout already matches Prove2Me. A platform submission must match
its target's exact statement and must not import that same target theorem. A
successful local compile is neither platform acceptance nor proof that imported
project axioms are absent.

## Repository milestone audit (not the original paper's statement)

1. Exact collision identity: theorem and solution present; compile/readback
   status is recorded below.
2. Matrix-pencil/Maslov incidence: theorem and solution present.
3. Borel selector reduction: theorem and solution present.
4. Packing selector to sources: current interface constructs a measure supported
   on a **compact ambient front**, not necessarily the Borel selector front as
   requested. Same-radius localization is present, but this support distinction
   matters for milestone 8.
5. Lossless edge-flow accounting: finite forest theorem present. This algebraic
   ledger does not itself construct the geometric payments.
6. Uniform hereditary bound: current `HasUniformMarkedSourceEstimate` contains
   only the union/mass inequality, omitting the requested quadratic energy
   inequality. Its named theorem proves a disjunction with Frostman or an
   unresolved concentration boundary, not the universal estimate. Arbitrary
   shading thinning makes the proposed universal estimate false.
7. Frostman upgrade: valid as a conditional implication from coherent sources
   supported on the desired front plus the uniform estimate. This does not
   establish the missing uniform hypothesis. The solution entry had stale API
   and epsilon bookkeeping, repaired without changing its selector conclusion.
8. Borel selector closure: the current theorem takes a compact ambient family
   and concludes full dimension of its front. The historical proposal instead asks for the selector's own front without compactness. The original-paper audit shows that stronger statement is not the source's explicit closure theorem. The Solution entry now follows the compact-ambient interface needed by the unchanged main theorem; it remains a WZ-dependent legacy proof.

## Common-shading obstruction

### Kernel-checkable finite algebra

`Theorems/Thm_StickyKakeya4_common_shading_obstruction.lean` defines a restriction
which replaces all shadings by the same measurable set `B`, provided `B` lies
inside every original shading. It preserves thickness, actual lines, affine
marks, tree, and weights. Thus it satisfies the **existing**
`IsFractionalSourceRestriction` definition.

For `n > 0`, unit weights, and `0 < volume B < infinity`, its calculation is:

- `F_R = n * 1_B`
- `sourceMass R = n * volume B`
- `sourceUnion R = B`
- `integral F_R^2 = n^2 * volume B`
- both `sourceMass R <= K * volume(sourceUnion R)` and
  `integral F_R^2 <= K * sourceMass R` are equivalent to `n <= K`

This module deliberately does **not** claim to formalize the whole geometric
asymptotic counterexample. It isolates the exact defect in unrestricted thinning.

### Geometric family (mathematical audit, not yet a Lean theorem)

Take the full radial selector
`Gamma = {((theta, 0), 0) : norm theta = 1}`. It is compact, Borel, valid, and
full-direction. Its unmarked carrier is isometric to the unit 3-sphere and has
packing dimension 3. Let `a = 1/10`, `delta = a/m`, and choose the `m^3` directions

`theta(q) = (q,1)/sqrt(1 + norm(q)^2)`,
`q in {0, a/m, ..., a(m-1)/m}^3`.

The chart and its inverse have uniform Lipschitz constants on this fixed box.
Therefore the number of these directions in any radius `r >= delta` ball is at
most `C (r/delta)^3`; carrier covering numbers are at most `C r^-3`, with one
constant independent of `m`. Both satisfy the admissibility bounds with exponent
`3 + epsilon/10`. Set all weights to 1, offsets and affine marks to zero, and
use a forest of singleton carrier cells. Give each root its full closed
delta-neighborhood of the unit segment as shading. Its volume is at least
`(4*pi/3) delta^3`, hence at least `delta^(3 + epsilon/10)` for `delta < 1`.
The total root source mass also stays between positive finite constants
independent of `m`.

Every such tube contains `B(0,delta/2)`. Restrict every shading to that common
ball without changing anything else. The exact finite calculation above gives
`n = m^3 = (a/delta)^3`. Taking output exponent `epsilon = 1`, the proposed
uniform estimate would force `a^3 <= A delta^2` for all sufficiently small
delta, which contradicts fixed finite `A` as `delta` tends to zero.

This counterexample does not contradict the final sticky-Kakeya dimension
claim: the radial front is a four-dimensional ball. Nor does it contradict the
published dense-shading volume theorem. Wang--Zakharov's
[Theorem 1.2](https://arxiv.org/pdf/2609.22035) requires delta^eta-dense shadings;
the common ball has relative tube density on the order of delta and fails that
hypothesis when eta is small. A dense-shading theorem does not supply the
arbitrary-thinning or quadratic-energy estimates requested here.

The original manuscript's precise hereditary object is an ordered edge-occurrence
measure carrying conditional flags (Lemma 8.56, Proposition 9.29, Appendix A),
not arbitrary physical shading deletion. Its closure runs through the relative
residual/Frostman alternative (Corollary 9.31) and the residual criterion
(Theorem 9.32). The displayed tube inequalities are an overstrong repository
translation. This counterexample does **not** refute the manuscript's main theorem.
The authoritative target ledger is being aligned with the actual paper rather
than replacing the main theorem by a weaker result.

## Other no-WZ closure gaps

The source audit now prioritizes the paper's **finite-depth occurrence-tree**
route. The stronger infinite continuation below is a gap in the older proposed
route, not a mandatory prerequisite for every proof of the original theorem.
The aggregate terminal repair is being formalized using root-pair domination
and endpoint support, avoiding the invalid per-node conditional normalization.

- `PrunedCommonHeightAnalyticFourCycleContinuation` has no constructor from the
  finite alternatives elsewhere in the repository, and its tree carries no
  source-mass retention data.
- `arbitrarilyCollapsed` supplies some node and vector for each threshold. It
  does not establish deep, positive-mass collapse along a common surviving branch.
- The vector-centre estimates assume one clustered centre ball and disjoint
  sources. Uniform accounting across moving-centre clusters is still missing.
- The three-packet ledger assumes generation decay and local/root charge
  estimates. Actual-source half-removal is not connected to those assumptions
  by a generation constructor.
- The public routing/Frostman/boundary trichotomy is obtained by case splits;
  axiom-clean readback of that trichotomy cannot eliminate its boundary branch.
- `selector_closure` still invokes the WZ axiom-backed branch.

## Changes made

- Updated the main Solution's call to the existing compact-ambient closure;
  its theorem statement is unchanged. This remains a legacy axiom-dependent route.
- Corrected the obsolete Borel-only selector Solution to the source-faithful compact-ambient auxiliary interface; the final compact marked theorem is unchanged.
- Updated the conditional Frostman Solution to
  `HasCoherentFiniteScaleSources selector selector`, preserving its intended
  selector-front support, and aligned the source exponent with epsilon/10.
- Added the common-shading calculation and exact necessary-coefficient lemmas.
- Added `scripts/check-environment.sh` and a fail-closed
  `scripts/check-axioms.sh`, plus `verification/AxiomReadback.lean`.

## Executed checks

- Lean/Lake version commands: passed
- Official pinned dependency checkout: passed
- Public Prove2Me health: passed
- Shell script syntax and Python script compilation: passed
- `git diff --check`: passed
- Mathlib prebuilt cache: all 8,690 files downloaded and decompressed
- `Solutions.SmokeTest`: passed (2.4 seconds)
- `Definitions.Def_sticky_kakeya4_core`: passed
- `Thm_StickyKakeya4_common_shading_obstruction`: passed
- `Solutions.Sol_StickyKakeya4_hereditary_finite_scale_to_frostman`: passed
- `Thm_StickyKakeya4_exact_collision_identity`: passed
- `Thm_StickyKakeya4_lossless_edge_flow_carleson`: passed
- `Thm_StickyKakeya4_edge_marginal_obstruction`: passed after correcting noncomputable numeric definitions
- Common-shading readback: all 7 declarations use only `propext`, `Classical.choice`, `Quot.sound`
- Edge-marginal readback: all 4 declarations use only those standard logical axioms
- Full 109-module dependency-first build: in progress
- Final theorem readback: pending; no final proof-completion claim

Build and kernel results will be updated after the cache and checks complete.
Source inspection and API health are not substitutes for them.

## Original-paper measure normalization check

The original-paper audit identifies a conditional-kernel normalization step in
Proposition 9.29, equation (453), requiring additional justification. The new
`Thm_StickyKakeya4_edge_marginal_obstruction` module records a two-point finite
probability example: base weights 1/2, edge density 1 only on (0,0), source
marginal mass 1/4, cap mass 1/2, and same-cap edge mass 1/4 > 1/8. It tests only
the generic domination inference, not all geometric hypotheses of the paper.
Its compilation/readback status is recorded with the other checks.

## Progress backup

The first checkpoint is remotely backed up on branch
`prove2me/original-paper-audit-2026-10-02`, commit
`5329da8cf4c53771390c26ef81594ffdf9076bdb`. Later checkpoints refine tests and
proofs on that same independent branch. The original `main` branch is unchanged.
The stronger historical selector signature is preserved explicitly in
`verification/ARCHIVED_TARGETS.md`.
