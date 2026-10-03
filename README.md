# 4D Sticky Kakeya

Lean 4 formalization of a contact--symplectic approach to the four-dimensional
sticky Kakeya problem.

This repository records the current formalization state. It is **not yet an
unconditional, kernel-checked proof of the final four-dimensional theorem**.
The collision/Maslov/selector infrastructure and substantial parts of the
finite-scale and Frostman chain are present, but the current public
`selector_closure` route still imports a Wang--Zakharov volume estimate through
the project axiom
`wang_zakharov_published_volume_estimate`. The intended endpoint is to remove
that dependency by closing the weighted, source-hereditary Carleson branch
internally.

The earlier Prove2Me proposal is preserved in
[PROVE2ME_TARGETS.md](PROVE2ME_TARGETS.md). The source-faithful current targets
and verified progress are recorded in
[CURRENT_MILESTONES.md](CURRENT_MILESTONES.md).

## Source-faithful verification checkpoint (2026-10-02)

The original [Chenxi Cai manuscript](https://cchx0000.github.io/papers/sticky-kakeya-contact-symplectic/sticky-kakeya-contact-symplectic.pdf)
is the final specification. [ORIGINAL_PAPER_TARGETS.md](ORIGINAL_PAPER_TARGETS.md)
records the exact correspondence and remaining proof obligations.
[CURRENT_MILESTONES.md](CURRENT_MILESTONES.md) is the working source-faithful
ledger. In particular,
its occurrence-measure restrictions must not be replaced by arbitrary physical
shading deletion. The compact marked main theorem is unchanged.

New kernel-checked intermediate results include a common-shading obstruction,
a finite conditional-marginal normalization test, and a **global terminal-band
bound**. The latter derives a cubic terminal budget from one original endpoint
pair measure, so terminal caps may move and overlap. These are intermediate
results with explicit hypotheses, not an unconditional completion of the main theorem.
A measure-valued finite forest ledger now derives the terminal root budget from
nodewise conservation and connects it to the global quadratic bound.
The old-neighbor disintegration, Markov restriction calculus, canonical-sphere
specialization, and residual collision/Tonelli bridge now have strict readbacks.

Recent checked geometry now also includes actual bounded-density slope
sources, exact-contact nullity and full weighted residual decay under the
no-Frostman hypothesis, dimension-deficit residual excess, and constructed
Hausdorff-cover routing. The original packing hypothesis supplies a fixed
positive literal source with hereditary vertical support counts; angular
shell extraction and original-carrier proximity are proved as well. A
first-hit phase localization selects a positive dense block without a
number-of-cells loss. These constructions remove source and routing input
premises, but the global weighted transverse charge remains open.

One checked result derives recurrent heavy bushes for
almost every original source/time pair directly from strict front dimension
deficit, with a divergent sum of their source-time masses. This preserves
continuum time information on one fixed actual source. The aggregate
root-time charge needed to contradict it is still open; finite collections
of heavy times cannot replace that information.

The latest filtration repair proves a finite-tree mass-weighted density-growth
budget, allowing mass deletion. Its only additional term is the cumulative
parent-mass-weighted logarithm of duplicated reference-cap capacity. That
term vanishes for true nested reference subpartitions; controlling it for
the actual moving hairbrush route remains open. The eleven new declarations
have strict, standard-only axiom readbacks. See
[the exact repair and remaining interface](docs/FILTRATION_CAPACITY_REPAIR.md).

A constructed least-capacity envelope now weakens the required geometric
control further: it replaces cumulative overlap costs by a hereditary
antichain-capacity bound. Its ten declarations are strictly verified.
[The envelope and witness-pooling note](docs/CAPACITY_ENVELOPE_AND_WITNESS_POOLING.md)
records the remaining geometric comparison. The
[whole-parent heavy-bush restart](docs/WHOLE_PARENT_HEAVY_BUSH_RESTART.md)
is now also strictly verified from the original front dimension deficit:
it fixes one source before all coefficients and cutoffs and retains nearly
all its mass in disjoint actual heavy bushes. Direction-cap contraction
remains a separate geometric obligation. The new
[common-time strengthening](docs/COMMON_TIME_HEAVY_FAMILIES.md) fixes one
actual time before all later requests and retains the almost-everywhere
time statement. Its thirteen declarations are strictly verified.
[The relative-projection audit](docs/RELATIVE_PROJECTION_FILTRATION_AUDIT.md)
records a valid predictable-plane estimate and the still-missing inverse
geometry; its arguments are handwritten, not Lean-certified.

A new [finite incidence core](docs/UNIFORM_INCIDENCE_CORE.md) constructs
quantitatively large actual subsets with all listed local densities comparable
inside the same parent. It preserves positive integer occurrence weights and
has eleven strict standard-only theorem readbacks. This supplies a concrete
regularization step; the subsequent geometric gain remains open.
The [two-time scale test](docs/TWO_TIME_TRANSPORT_SCALE_TEST.md),
[finite-time arithmetic test](docs/FINITE_TIME_ENTROPY_ARITHMETIC_TEST.md), and
[continuum packet audit](docs/CONTINUUM_PACKET_CAPACITY_AUDIT.md) record the
independently checked limitations of proposed shortcuts. These three notes
are handwritten, not Lean-certified.

An actual [Borel triangular-selector escape](docs/TRIANGULAR_BOREL_FROSTMAN_ESCAPE.md)
is now proved end to end: fixed product-reference potentials, a positive
restriction of the original coupled source/time law, supported Frostman
measures, and dimension four. The 31 theorem readbacks have no energy
certificate or new axiom in the endpoint. This covers a genuine special class;
no triangular representation of an arbitrary sticky selector is inferred.
The [native-time one-channel extension](docs/RANK_ONE_NATIVE_TIME_ESCAPE.md)
now proves the same conclusion for `b(a)=c+L a+u f(a1)`, with arbitrary
linear coupling. It derives the rational feedback, a usable original-time
window, and all native potentials internally. The [arbitrary-input theorem](docs/GENERAL_INPUT_RANK_ONE_ESCAPE.md) now
also derives the fixed basis, Haar density, bounded positive source piece,
and literal original support transport for `f(v dot a)`, including `v=0`.
The [external rank-one-output projection interface](docs/RANK_ONE_OUTPUT_GGW_REDUCTION.md)
is a different handwritten applicability result and is not imported as an axiom.

The triangular class now also has a checked
[original heavy-root charge](docs/DIRECT_HEAVY_ROOT_CHARGE.md): for each
`0<beta<3`, the unmodified source/time heavy-event mass has a positive
small-radius power and a finite dyadic sum. The proof derives its uniform
potential bound from the source densities and uses a symmetric-ball
good/bad argument. All 44 new theorem readbacks are standard-only. The
general coupled selector case remains open. A further checked
[original root-moment bound](docs/TRIANGULAR_ORIGINAL_ROOT_MOMENT.md) gives
`integral Z_r^theta <= C r^(3s theta)` for every `0<s<1` and
`0<theta<1/3`, directly on the unmodified triangular source/time law.

A separate [stationary digit-graph argument](docs/STATIONARY_GRID_GRAPH_PROJECTION_ESCAPE.md)
now treats arbitrary coupled full-grid digit maps, using an explicit external
Corso--Shmerkin scale-transfer theorem. Its
[driven extension](docs/DRIVEN_GRID_GRAPH_PROJECTION_ESCAPE.md) and
[finite-state full-front consequence](docs/FINITE_STATE_GRAPH_FRONT_ESCAPE.md)
are handwritten research, not Lean endpoints. The supporting exact
[polynomial small-value estimate](docs/SCALAR_PENCIL_PREFIX_SUBSPACE_OCCUPANCY.md)
is independently formalized (four standard-only declarations). General
selectors have not been shown to admit the required digit structure.

See [verification/REPORT.md](verification/REPORT.md) for executed checks and
[verification/REPRODUCING.md](verification/REPRODUCING.md) for commands. The
latest full default build passed **185 project modules** and **8,894 Lake jobs**,
including the one-source/all-slack and variable-time line-hairbrush constructions.
Its source snapshot is recorded in `verification/hairbrush-escape-default-build.log`.
The additional filtration, envelope, whole-parent, and common-time targets passed
**1,948**, **1,949**, **8,757**, and **8,759 jobs**. The new independent incidence-core target
passed **788 jobs**, the triangular endpoint passed **8,714 jobs**,
the original-charge endpoint passed **8,718 jobs**, and the rank-one/native-time
and actual-moment endpoints passed **8,723 jobs**. The arbitrary-input
rank-one target passed **8,720 jobs**, and the elementary polynomial target
passed **8,706 jobs**; the current **209-module**
checkout has not been rebuilt in full in the restored workspace.
The final-theorem axiom gate in `verification/hairbrush-escape-main-axiom-gate.log`
still fails exactly because the two main
closure declarations use the preexisting WZ project axiom.
`scripts/check-axioms.sh` makes that failure explicit. The original final
statement has not been weakened and no new project axiom has been added.


## Current formalization

The main no-WZ development now includes:

- exact collision identities and Maslov-incidence conversion;
- Borel/measurable selector reduction and finite-scale source extraction;
- a common-height analytic four-cycle packet whose collision time is derived
  from the geometry rather than identified with the affine fibre mark;
- a coherent common-height collision tower, with the noncollapsed infinite
  branch ruled out through the Maslov return tower;
- a public source-point alternative returning either coherent collision-time
  motion or an affine three-packet;
- weighted affine-mark half-removal and a three-packet return Carleson ledger;
- a uniform marked source-hereditary finite-scale interface and the Frostman
  mass-distribution reduction.

The following recently added targets were compiled successfully in the pinned
Colab environment:

- `Thm_StickyKakeya4_collision_time_coherent_motion`
- `Thm_StickyKakeya4_parametrized_source_return_budget`
- `Thm_StickyKakeya4_common_height_collision_tower`

Their theorem readback used only Lean's standard logical axioms
`propext`, `Classical.choice`, and `Quot.sound`. This statement is deliberately
limited to those targets; it is not a claim that the full final theorem is
axiom-free.

## Repository layout

- `Definitions/`: common geometric and measure-theoretic definitions.
- `Theorems/`: theorem statements and the evolving dependency chain.
- `Solutions/`: proof entry points corresponding to the Prove2Me milestones.
- `PROVE2ME_TARGETS.md`: proof architecture, status, and closure criteria.

## Reproducing the Lean environment

The repository pins Lean and both external dependencies:

- Lean `v4.33.1` through `lean-toolchain`;
- `mathlib4` at commit `0df444a360eaa60ab8c11dca51a86af692955474`;
- `LeanFormalizations` at commit
  `dd46c17a2a034d7bfa0df02e7f77834d35592864`.

With `elan` and `lake` available:

```bash
lake update
lake build
```

For a focused check of the active no-WZ front:

```bash
lake build Theorems.Thm_StickyKakeya4_collision_time_coherent_motion
lake build Theorems.Thm_StickyKakeya4_common_height_collision_tower
lake build Theorems.Thm_StickyKakeya4_parametrized_source_return_budget
```

## Author

Chenxi Cai — <Chenxi_Cai@live.com>
