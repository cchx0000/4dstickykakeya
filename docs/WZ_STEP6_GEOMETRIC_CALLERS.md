# Constructed slice, quotient and cubical-source geometry

Verified 2026-10-03 against the original pinned Lean toolchain. The nine
modules below add 153 proved declarations. Strict source checks and a shared
proper-import axiom readback pass; every declaration uses only the standard
logical axioms. The 234-module default build passes 8,943 jobs. The preceding
225-module snapshot also completed its full default build, with 8,934 jobs.

## Actual constructions

- `InjectiveSliceQuantization` constructs the full integer-grid label
  bijection and the physical shear-floor map. It preserves original labels,
  spatial/time coordinates and cardinality, and proves the strict one-mesh
  pairwise coordinate error. No injectivity certificate is assumed.
- `GridQuotientAD` derives the fractional quotient exponent from actual dense
  horizontal grid fibers, full ambient upper/lower counts and integer-division
  covering cells. `GridRichNeighborQuotient` extends this to the requested
  coarse union when rich fibers lie in nearby cells. It counts the actual
  bounded-distance assignment fibers, and uses the full source for the lower
  bound. It does not assume that every original cell itself is rich.
- The three `FiniteVoronoi*` modules construct a maximal separated net, a
  nearest-center partition with disjoint exhaustive populations, and coarse
  AD estimates. The real-exponent version works for every exponent t>=0,
  including zero, with coarse constant 6^t K^2 and cluster lower population
  (rho/delta)^t/(3^t K). These are derived from the original metric AD data.
- `PhysicalRescalingBackboneDensity` keeps the complete original backbone,
  including initially unused rows, using its stated full-backbone density
  inequality. It corrects the scope of the earlier used-label comparison.
- `PaddedRescalingCubicalSource.exists_actual_padded_cubical_source` constructs
  a native finite source on all original rows. It simultaneously derives
  global fine-bin padding, literal coarse-cell axis witnesses, genuine unit
  marked-segment membership, measurable cubical shadings, original-label
  injectivity, fixed slab/window normalization, geometric bin capacity,
  total shading volume and the retained density bound. It keeps a quarter
  of the original incidence set with unchanged row labels and whole selected
  fine-bin fibers. Direction separation, carrier AD and convex Wolff
  assertions are separate geometric tasks; this theorem does not silently
  add them to its conclusion.
- `TwoTubePathCollisionCount` proves the actual two-tube path and paired-path
  counts for a finite incidence relation. The inequalities are cross-multiplied
  natural-number statements, so zero degrees and empty configurations are
  handled directly. The geometric label-image bound remains the explicit
  input to the final collision count, rather than an assumed walk lower bound.

## Scope of the remaining argument

These results discharge specific local construction and counting premises.
They do not yet assemble all AD, direction-coloring and convex Wolff data
into a rescaled admissible configuration, or construct every geometric slice
from an arbitrary original packet. The handwritten adapters are recorded in
[the quantization audit](WZ_SLICE_QUANTIZATION_AD.md),
[the coarse-height union audit](WZ_COARSE_HEIGHT_UNION_AD.md) and
[the exact next-lemma audit](WZ_PROP182_OUTPUT_AND_NEXT_LEMMA.md).

The next source step is Wang--Zakharov Lemma 5.3, followed by slab-Frostman
stopping and slope consistency. The finite column estimate is detailed in
[the alignment audit](WZ_LEMMA53_FINITE_ALIGNMENT.md). A disjoint-fiber
preparation is being checked to make incidence retention imply genuine
original-point retention; that combined repair is not counted among this
checkpoint's Lean proofs. The already proved path count does not bypass
these earlier geometric steps.

The original final theorem is unchanged. A fresh final-axiom check still
fails because `selector_closure` and `sticky_kakeya_four_dimensional` use the
existing `wang_zakharov_published_volume_estimate` axiom. Neither the successful
build nor these local results close that gap. Prove2Me platform execution
also remains unauthenticated; no platform submission is claimed.

## Reproducible evidence

- [Exact commands, hashes and 153 readbacks](../verification/wz-step6-geometric-callers-checkpoint.json)
- [234-module full build](../verification/wz234-default-build.log)
- [234-module source snapshot](../verification/wz234-source-snapshot.json)
- [Shared imported axiom readback](../verification/wz-step6-geometric-callers-axioms.log)
- [Fresh final-axiom gate](../verification/wz225-main-axiom-gate.log)

The cumulative separately recorded standard-only declaration count is 1,550.
Historical checkpoint descriptions retain their original verification scope;
the current machine-readable status points to this full build.
