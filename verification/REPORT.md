# Prove2Me / 4D Sticky Kakeya: verification checkpoints

Date: 2026-10-02 UTC. Original baseline:
`d208ddf4544cbb9ed05e4c848a83b07985b28e26`.

## Root-faithful four-cycle geometry checkpoint

Actual physical contact cycles now yield old-time rigidity without replacing
root errors by an auxiliary scale. With horizontal entries bounded by `M`,
frame determinant at least `Delta > 0`, and all four old collision errors at
most `r_0`, the checked time bound is `24 M^2 r_0 / Delta`. The actual graph
plane is within `6 M^2 r_0 / Delta + 144 M^5 r_0 / Delta^2` of a scalar graph.
A scalar-label cell therefore puts every original edge in one time packet,
and reevaluating those same edges at its center retains the explicit error.
For bounded `M` and `Delta = r_0^d`, `d < 1/6`, this is compatible with the
terminal cap scale `r_0^(2/3)`.

`RootedFourCycle` proves the bipartite C4 lower bound `M^4`, actual rooted
marginal domination by the old graph law, and positive witness density at
almost every old edge. `RootedCycleWitnessKernel` constructs a genuine Markov
extension rooted at the full old occurrence, preserving every original
endpoint, collision time, and flag law. Its cycle edges belong to the original
graph. Diffuse selector laws and a zero diagonal give four distinct vertices.
Conditioning is only asserted to preserve absolute continuity, not a bounded
fresh product density.

All three modules passed strict compilation and axiom readback: 18, 16, and
32 checked declarations respectively. The cumulative checked count is **488**;
all axiom lists are empty or contain only `propext`, `Classical.choice`, and
`Quot.sound`. The full tracked build of `5ac4351` then passed for all **141** committed
modules, **8,848** Lake jobs, exit 0; see
[rigidity-checkpoint-full-build.log](rigidity-checkpoint-full-build.log).
The repeated main axiom gate exited 1 for exactly the two unchanged closure
declarations that retain the preexisting WZ axiom; see
[rigidity-main-axiom-gate.log](rigidity-main-axiom-gate.log).

The remaining step is substantive geometry: producing a mesoscopic
nondegenerate root cycle, or a genuinely paid/Frostman alternative, from the
actual non-paid occurrence. Generic C4 positivity does not supply that
threshold. The fixed smooth two-patch test in
[CONTACT_CYCLE_RIGIDITY_AND_THRESHOLD.md](../docs/CONTACT_CYCLE_RIGIDITY_AND_THRESHOLD.md)
explains why the no-Frostman/weighted rank-loss branch is essential.
The unchanged final theorem still has its preexisting WZ project axiom.

## Actual common-target occurrence kernel checkpoint

The common-target star is now constructed from actual source-cut old measures,
not supplied as an abstract probability certificate. Original selector masses
`q_i = sigma(S_i)` give the target domination and actual index laws. Aggregate
target disintegration samples entire old occurrences, preserving source,
target, collision time, and inherited flags. All three fresh marginals equal
the original aggregate before cuts. On the high-multiplicity set `N >= 24`,
the distinct-source cut retains at least half of the inherited marginal; a
half-mass high branch therefore retains at least one quarter of the old mass.
Post-cut fresh marginals are asserted only to be dominated, not stationary.
Disjoint genuine source cuts imply distinct physical sources.

`SubmeasureRoutingExhaustion` now exhausts a finite occurrence by genuine
positive submeasure outputs, with no uniform fraction, hereditary eligibility,
or rare-event normalization. `NormalizedTargetGrowth` supplies the stationary
index probability and layer-free positive growth alternative. Explicit 3x3
adjugate bounds are also checked for the next physical contact-cycle step.

There are now **422** checked new declaration readbacks (some definitions use
no axioms; every nonempty axiom list is standard-only). Genuine contact-cycle
time/plane rigidity and mesoscopic nondegenerate-or-paid availability remain
separate geometric obligations under active investigation.

## Verified whole-support reversal checkpoint

`QualitativeUnionGrowthTermination` adds 23 standard-only readbacks. It derives
source/target support containment from actual dominated/reversed pair laws,
exhausts the whole positive-density source support, chooses a finite cover of
more than half its selector mass, and proves the two-stage support-growth
contradiction. This is a qualitative internal termination result, not a global
paid or cross-cap estimate. It does not substitute a small edge-mass tail for
large selector-support coverage.

The full tracked build of `ba379c5` passed for all **133** committed modules,
8,840 Lake jobs, exit 0. Evidence:
[vector-checkpoint-full-build.log](vector-checkpoint-full-build.log).
The subsequent qualitative module has its own strict source/readback checks.
There are now **333** checked new declaration readbacks, all standard-only.

## Full vector-family and growth/star checkpoint

The full original Theorem 8.11 analytic escape is now checked in its literal
normalized **open-cap** formulation. `VectorBushFrostman` proves the physical
ball estimate for the entire weighted family with exact cancellation of its
total mass. `CompactFrontLimit` constructs an actual supported weak limit by
Prokhorov and Portmanteau. `VectorBushEscape` combines them to produce a
supported `(d+1)`-Frostman probability and `d+1 <= dimH`.

Family sizes may vary, and their positive total masses may tend to zero. There
is no individual-bush lower mass assumption. The synchronized vector cap
inequality at one common physical `(y,s)` remains the geometric premise; it
has not been inferred from arbitrary separate cap estimates.

The individual-bush theorem now also gives uniform qualitative small-bush
mass decay on a no-Frostman/low-dimension branch, with no rate. Separately,
`FourDistinctSources` and `WeightedGrowthStarSplit` prove the finite product-law
probabilities and the robust target-support-growth/high-multiplicity split.
The high half-branch has a distinct-source success integral at least one
quarter of the original occurrence mass, with the inherited index fixed.
Constructing its actual common-target old-occurrence fibre lift is still
underway; the geometric same-window and later return arguments remain open.

There are now **310** checked new declaration readbacks, all standard-only.
The original core and final theorem file remain byte-identical to baseline.

## Positive occurrence routing checkpoint

Four further checked modules add 53 standard-only declaration readbacks:

- `actual_slope_source_bounds` derives a uniform intercept bound from the
  original compact front and offers a sharpened actual-source construction
- `positive_routing_exhaustion` proves exact countable disjoint exhaustion from
  positive hereditary outputs, transfers it through actual source densities,
  preserves old endpoints/marks, and gives finite truncation at any positive
  absolute tail. It assumes no uniform retained fraction or branch count
- `positive_flag_conditioning` constructs the actual conditioned Markov law on
  the positive-success base, preserves its full original occurrence marginal,
  and reuses the same law on absolutely continuous hereditary restrictions

- `positive_bush_frostman` proves a genuine geometric escape: one sequence of
  shrinking individual physical bushes with a fixed positive mass lower bound
  yields full original-front dimension. Compactness, the exact limiting bush,
  a separated time interval, and supported Frostman measures are all derived

There are now 251 checked new declarations in total. These routing tools do
not establish positivity of a geometric success event or any global paid/cross
estimate. Merely positive aggregate bush-family mass is not the individual
bush hypothesis just proved. A fresh main-theorem audit still exits 1 for the same two WZ-dependent
closures; see [closure-main-axiom-gate.log](closure-main-axiom-gate.log).

## Actual-source analytical closure checkpoint

The original analytic reduction is now proved through genuine front measures:

- `actual_slope_source` constructs a positive finite slope-Lebesgue source,
  a measurable intercept, slopes bounded by one, and a common marked-front
  slab of length `3/8` directly from a compact valid full-direction datum
- `spacetime_collision_energy` gains the extra dimension by a checked `2 rho`
  target-time fibre bound, rather than invoking an unformalized slicing theorem
- `energy_dimension` extracts a positive bounded-potential restriction and
  normalizes it to a Frostman probability with the exact original support
- `original_residual_criterion.compact_full_direction_residual_reduction`
  constructs that actual source and proves that its literal codimension-two
  residual bounds imply `dimH (unitFront ambient) = 4`

The [geometric repair ledger](../docs/GEOMETRIC_REPAIR_LEDGER.md) records
failed resampling bounds, the aggregate union-growth invariant, and the next
concrete bush/Frostman exit.

The geometric residual estimate is still a premise of that last implication.
It has not been derived from packing dimension, and the public main theorem
still retains its original WZ project axiom.

Two further local advances are checked: `separated_bush_fiber` pays all targets
of one physical separated-time packet with the inherited old collision error;
`independent_flag_separation` preserves the full old occurrence law under fresh
independent flags and gives measure-valued discarded/retained bounds. The
[designated-flag research note](../docs/INDEPENDENT_FLAG_CROSSCAP_REROUTING.md)
explains the source-level geometric extension and the unresolved bush-return
summation/termination. The packet-free tube-volume estimate in the earlier
note remains a handwritten result, not a Lean-certified theorem.

The expanded [resumed readback inventory](resumed-axiom-summary.json) gives the
exact declaration list and source hashes: 107 further readbacks, for 198 new
checked declarations in total. All are standard-only. The dependency-aware Lake
rebuild of the analytical closure and two local geometric targets passed:
8,754 jobs, exit 0. See [analytic-closure-build.log](analytic-closure-build.log).
All individual strict source/readback checks above also passed.
The subsequent full tracked-module build at `9c24070` passed for all 124
committed project modules: 8,831 jobs, exit 0. See
[tracked-closure-build.log](tracked-closure-build.log). Active uncommitted
research modules were not part of that snapshot. The older 116-module
snapshot remains below.

## Resumed analytical progress after b7989bcd

The next two modules have strict source builds and standard-only axiom
readbacks, adding 11 declarations to the 91 recorded below:

- `residual_energy`: zero-distance nullity, layer-cake power-tail control,
  finite inverse-distance energy, Tonelli, and almost-everywhere finite fibre
  energy (seven declarations)
- `residual_sublevel_power`: the actual three-dimensional bounded-density
  small-secant estimate, the averaged sublevel exponent `3 - η`, and the
  finite averaged collision energy conclusion of original Theorem 6.27,
  conditional on its geometric residual bound (four declarations)

See [resumed-axiom-summary.json](resumed-axiom-summary.json),
[residual-energy-build.log](residual-energy-build.log),
[residual-energy-axioms.log](residual-energy-axioms.log),
[residual-sublevel-build.log](residual-sublevel-build.log), and
[residual-sublevel-axioms.log](residual-sublevel-axioms.log).
The previous full-build snapshot below concerns the 116-module state at
`b7989bcd`; a later all-module build has not yet been rerun.

The [separated-bush research note](../docs/SEPARATED_BUSH_CROSSCAP_BOUND.md)
proves an elementary all-target local cross-cap estimate on paper and tests
its aggregation on a radial example. It is explicitly not a Lean-certified
result or a solution to the remaining targetwise multiplicity problem.

## Result at the full-build checkpoint b7989bcd

- **Full local project build: passed.** All 116 current Lean modules build;
  the explicit aggregate run completed 8,826 Lake jobs, exit 0
- **Ordinary `lake build`: passed.** The default targets completed 8,825 jobs,
  exit 0, after repairing the library configuration
- **New proofs: 91 declaration readbacks across nine modules use only**
  `propext`, `Classical.choice`, and `Quot.sound`
- **Final unconditional theorem: not complete.** The axiom gate exits 1 because
  both `selector_closure` and `sticky_kakeya_four_dimensional` still use
  `StickyKakeya4.wang_zakharov_published_volume_estimate`
- **No Prove2Me server proof was submitted.** Local verification is complete;
  authenticated platform access and mission synchronization were not configured

The final main theorem and the original core definitions were preserved exactly.
The main Solution's statement is also unchanged. Compilation success is not an
unconditional proof: the missing source-level geometric estimate described below
must be proved before the legacy project axiom can be removed.

Machine-readable results: [final-status.json](final-status.json).

## Environment and source standard

- Lean `leanprover/lean4:v4.33.1`, release commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`
- Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`
- LeanFormalizations `dd46c17a2a034d7bfa0df02e7f77834d35592864`
- Official Prove2Me workspace commit
  `4bb28221f86306b70b58f8119c4413025d09b302`, skill/API version `0.11.6`
- Public API health returned `ok`, version `0.11.6`, at
  `2026-10-02T03:02:07Z`

The original Chenxi Cai manuscript is the final mathematical standard.
[ORIGINAL_PAPER_TARGETS.md](../ORIGINAL_PAPER_TARGETS.md) records the PDF hash,
source links, exact pages/TeX labels, correspondence, and proof gaps.
[CURRENT_MILESTONES.md](../CURRENT_MILESTONES.md) is the current working ledger.
The older proposal remains visible in `PROVE2ME_TARGETS.md`.

Official environment references:
[Lean setup](https://github.com/prove2me/prove2me_workspace/blob/main/references/lean-setup.md)
and [API setup](https://github.com/prove2me/prove2me_workspace/blob/main/references/setup.md).
No credential was supplied, generated, saved, or transmitted. Lack of platform
authentication is separate from the mathematical obstruction; it does not
prevent local proof checking.

## Build and entry-point repairs

1. The Lean libraries previously used default root globs despite having no
   `Definitions.lean`, `Theorems.lean`, or `Solutions.lean`. Aggregate builds
   therefore failed with “some modules have bad imports.” Explicit submodule
   globs fix this, and both Theorems and Solutions are now default targets
2. The main Solution now calls the existing compact-ambient closure with the
   correct arguments. Its statement is unchanged
3. The conditional Frostman Solution now uses
   `HasCoherentFiniteScaleSources selector selector`, preserving its intended
   support, and matches the source exponent `epsilon/10`
4. The obsolete Borel-only selector Solution was aligned with the compact-ambient
   interface appropriate to the unchanged main theorem. The stronger historical
   signature is explicitly retained as unresolved in
   [ARCHIVED_TARGETS.md](ARCHIVED_TARGETS.md)
5. A bounded Linux build helper runs one Lake graph with at most three Lean
   compilers, using the untouched official compiler through temporary sysroot
   links. Cache reuse and subsequent ordinary Lake builds were verified

Pins, core definitions, and the original main theorem file were not changed.
There are existing style/deprecation warnings; there are no compiler errors in
the completed full build.

## Nine new checked modules

The exact declarations and axiom lists are indexed in
[new-axiom-summary.json](new-axiom-summary.json). All nine sources were checked
under the project's strict implicit-variable configuration, either through Lake
or explicit `-DautoImplicit=false` compilation.

- `common_shading_obstruction` — 7 readbacks. For a common finite positive
  shading and unit weights, both proposed overlap bounds force their coefficient
  to be at least the number of lines. This isolates the arbitrary-thinning defect
- `edge_marginal_obstruction` — 4 readbacks. A two-point probability calculation
  shows that bounded joint edge density does not imply domination by its own
  source marginal times the original target probability
- `global_terminal_band` — 11 readbacks. Root endpoint-measure domination and
  direction-ball density yield an aggregate `8 C m T^3` terminal estimate and
  `8 C m^2 q` when `T^3 <= m q`. A global reversal allowance has factor 16;
  moving or overlapping cap centers require no bounded-overlap hypothesis
- `measure_edge_flow` — 6 readbacks. Nodewise equality of measures on a finite
  occurrence forest yields terminal root-measure domination, preserved by one
  fixed endpoint map, and the integrated quadratic terminal estimate
- `markov_endpoint_preservation` — 16 readbacks. Actual Markov probability-label
  extensions preserve old endpoint laws. Fractional restrictions, subsequent
  extensions, different destination label spaces, and disjoint label-dependent
  cuts preserve the original measure budget
- `old_neighbor_disintegration` — 17 readbacks. `condKernel` constructs the actual
  old-neighbor Markov law and equation-(419) disintegration. The source marginal
  is the exact degree-density measure. Its bound is `lambda <= sigma` for a
  probability base, and `(sigma univ) * sigma` for an unnormalized finite base
- `fixed_angle_terminal_vanishing` — 7 readbacks. Below the root's fixed angular
  cutoff, same-band terminals vanish while the complementary-band mass equals
  the entire root mass. Thus terminal shrinking alone cannot pay cross-cap mass
- `sphere_terminal_band` — 5 readbacks. The actual canonical surface probability
  supplies the density estimate: for an unnormalized dominated source and
  `0<T`, `3T<=1`, the bounds are `27 C m T^3` and `27 C m^2 q`. An actual canonical
  restriction example and the finite-forest integration are checked
- `residual_collision_bridge` — 18 readbacks. Exact collision-fiber localization,
  measurability, and Tonelli give the source-faithful estimate

  ```text
  integral_[u,v] mu{norm(beta+s alpha) <= rho} ds
    <= 2 rho Z_rho^[u-d,v+d](mu)
       + max(v-u,0) mu{norm(alpha) <= rho/d}.
  ```

  The near-direction contribution is explicit. The shell version removes it
  under its stated a.e. nonzero-secant and buffer hypotheses

These are proved components. They are not yet substituted for the WZ branch in
the public main theorem, because the required geometric construction and
cross-cap estimate are still absent.

## Exact remaining mathematical obstruction

The original paper's Proposition 9.1 (p. 107) assumes a quadratic relative
cross-cap budget. Proposition 9.29 (pp. 122–123) accounts for old-neighbor exits
but does not itself establish that budget.

The root graph in Proposition 7.76, equation (305), has a fixed lower angular
cutoff. When terminal caps shrink below that cutoff, every unremoved original
edge is cross-cap. The new checked guardrail proves the underlying measure
identity. Conservation and terminal cap shrinking cannot alone make that mass
small.

The separated-polarization results require additional hypotheses not supplied
by separation of direction caps, and retain further routing alternatives. The
source audit identifies no theorem paying the full varying-generation,
old-weighted first-exit measure. A concrete missing target is

```text
sum_v Exit_v(univ) <= C_eta m^2 r^(2-eta),
```

proved for the actual geometric occurrence tree, or a genuinely terminating
replacement rerouting argument controlling those old pairs. Assuming that
numerical bound in a certificate is not a proof of it.

Geometric residual power bounds remain unproved. The finite-energy and
energy-to-front dimension passage are now proved, as described above. The
generic inverse-energy step of the historical
[draft](../drafts/README.md) has since been implemented and strictly verified
in `residual_energy`; the draft itself remains an uncompiled historical text.

This is a blocker to completing the supplied proof, not a disproof of the final
Sticky Kakeya theorem.

## Executed checks and evidence

- [Environment and smoke test](environment.log): passed
- [Full aggregate build](aggregate-build.log): passed, 8,826 jobs, exit 0
- [Default build](default-build.log): passed, 8,825 jobs, exit 0
- [Final theorem/axiom gate](final-axiom-gate.log): failed, exit 1, because the
  two closure declarations retain the WZ project axiom
- [New-declaration axiom summary](new-axiom-summary.json): 91 standard-only
  readbacks; individual full readback logs are linked there
- Core/main file preservation and main Solution statement comparison: passed
- Shell syntax, Python compilation, and whitespace checks: passed

The exact collision, Maslov incidence, Borel selector reduction, source
construction, lossless flow, and conditional Frostman implication were also
read back with only standard logical axioms. This does not prove their missing
geometric inputs or eliminate the final WZ dependency.

## Reproduction and backup

See [REPRODUCING.md](REPRODUCING.md). `scripts/check-axioms.sh` deliberately fails
until the final theorem's transitive project axiom is eliminated.

All source progress is backed up on the independent branch
[prove2me/original-paper-audit-2026-10-02](https://github.com/cchx0000/4dstickykakeya/tree/prove2me/original-paper-audit-2026-10-02).
The original `main` branch is unchanged. No merge or platform proof submission
was performed.
