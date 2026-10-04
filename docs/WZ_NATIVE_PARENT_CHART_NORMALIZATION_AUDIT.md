# Original parent chart and native finite-interface audit

Audit date: 2026-10-04. This note concerns the unchanged native finite input and the original-source parent selector. It does not change the target theorem or claim transformed admissibility.

## Exact paper and current interface

- Paper text `paper-audit/wang-zakharov-2609.22035.txt`, lines 798–810, formula (19) and Definition 3.6: ordinary graph tubes have slope in [-1,1]^(d-1), graph time in the fixed interval [-1,1], and intercept formally in R^(d-1). The dyadic definition uses slope/intercept parameter cells. Thus a universal bounded intercept assumption is not part of every stated tube definition.
- Lines 817–821, Proposition 3.1 explicitly restricts the parameters to [-1,1]^(2(d-1)). Lines 862–892, Definition 3.9 and Observations 3.2–3.3 use exact dyadic ancestors in graph parameter space for AD regularity and its rescaling/thickening closure.
- Lines 3361–3365, Definition 17.1 states the extremal K_d predicate on that tube class. Lines 3494–3506 give (104)–(105); (107)–(109) apply K_d to actual coarse and normalized parent families.
- `Theorems/Thm_StickyKakeya4_wang_zakharov_finite_interface.lean`, definitions `wzCarrierPoint`, `wzCarrierBallCount`, `IsWangZakharovFiniteInput`, `IsWangZakharovNativeFiniteInput`: native AD counts balls in the unmarked perpendicular carrier (unit direction, perpendicular offset). The input also imposes direction separation. It does not impose a uniform bound on affine marks, common absolute height, or spatial support.
- `Theorems/Thm_StickyKakeya4_wz_common_slab.lean:225`, `HasNormalizedWZGraphSlab`, controls direction4 >= 1/2 and a common slab of length >=1/8 at arbitrary absolute height. At line 233, `HasFixedWZGraphNormalization` contains the original unit segments in [a-1,b+1] for those arbitrary endpoints. It does not supply an absolute height bound.

Consequently the current docstring calling this the "literal input to the published graph-tube theorem" is broader than what has been justified. The native extremal predicate remains exactly the current native class; its identification with all paper admissible inputs, including the rescaled class, is unproved.

## Exact chart bound, proved in new staging modules

The actual parent selector uses the original slope v_j/v_4 and the intercept at s=floor(a/mesh)*mesh, divided by four. `NativeOriginalChartMetric.slope_sub_le` proves slope-coordinate variation <=6 times native carrier distance. `shiftedIntercept_sub_le` proves variation <=(3+6|s-offset_k,4|)/4 times native carrier distance. The latter dependence cannot be dropped merely because direction4>=1/2.

For instance, choose two distinct unit directions with positive fourth coordinate and perpendicular offsets zero. Put both marked segment centers at the same very large graph height a by choosing mark_i=a/v_i,4. Their unmarked carrier distance is independent of a, whereas their graph intercept difference at height a is a times their slope difference. They admit a fixed common slab and fixed relative height window. This demonstrates the missing geometric bound; it is not presented as a fully admissible near-extremizer counterexample.

`NativeOriginalParentCount.chartReach` is the actual finite maximum of |s-offset_i,4|. `parent_count` proves

    #parents * delta^eta * (r/delta)^3 <= 729 * n

provided delta<=r<=1, 6*N*r<=1, and ((3+6*chartReach)/4)*N*r<=1. The factor 729 is the exact 3^6 neighboring graph-parameter grid labels. This is an actual original-label double count using the original native carrier AD lower bound.

`NativeCompactChartReach.height_offset_le_of_mark` and `chartReach_le_of_marks` prove: a common original height and |mark_i|<=B imply chartReach<=B+1 for delta<=1. `compact_uniform_chartReach` proves existence of one positive M for every finite source drawn from a fixed compact marked family K, with M chosen before n, D, eta, a, or the dyadic scale. All three modules passed strict official Lean 4.33.1 compilation; imported closure audit is recorded separately when frozen.

The compact source path actually provides such K: `borel_selector_reduction` returns selector subset of the original compact `lines`; `markedCarrierPiece_exists_separated_active_family_with_count` retains original marked lines from that selector. `retainedWZCellSourceAtScales` uses `retainedIndex` as its literal source line. Hence a bound from the original compact marked family survives every such retained finite family, without assuming continuity of the mark as a function of unmarked carrier.

## Fixed dyadic spatial normalization: viable route, not yet proved here

`StickyKakeya4.IsCompact.unitFront` in `Thm_StickyKakeya4_compact_front.lean:27` already makes the original full unit front compact. Compactness also bounds original offsets and affine marks before delta. Choose a fixed dyadic scalar 2^-k small enough that the entire original front lies in a small graph box around zero. Scaling about zero sends every original half-open mesh cell exactly to a half-open cell at mesh 2^-k*mesh, so no grid-center replacement or non-dyadic translation is needed. The scaled physical tube thickness and comparable cubical mesh have exactly the same fixed dyadic ratio.

A similarity alone shortens each marked unit segment to length 2^-k. Therefore it does NOT immediately yield another `FiniteScaleSource` with the same native unit-segment/slab clauses. One must explicitly pad the scaled segment to a genuine unit segment with graph center at height zero, prove containment of the scaled original shadings, and charge the fixed tube-volume/density change. With the scaled source in a sufficiently small box and direction4>=1/2, such padding is geometrically available. It must be constructed rather than identified definitionally with the old source. Convex-Wolff transfer would then use: containment of a padded target tube implies containment of the scaled original tube; inverse dilation scales 4D volume by the fixed factor 2^(4k). Every constant here depends on the original compact family, not delta.

Even after that normalization, native metric-ball AD to exact dyadic-ancestor AD requires a separate genuine argument: boundary parents can have much smaller populations than surrounding balls, and restriction to one parent does not automatically preserve the lower ball counts. Random dyadic padding or a retained regular ancestor hierarchy must carry its actual selection losses. Likewise arbitrary N in the current parent constructor need not be a power of two; paper's exact dyadic rescaling requires an explicit N=2^k witness. The transformed family also needs direction separation at its new thickness, the tube/shading density exponent, actual reindexing of its backbone, and the full CW/AD conclusions before K_d is applied again.

## Completed compact-source count and retention

`NativeCompactCarrierCount.compact_carrier_card_bound` constructs a finite radius-1/2 cover from the original compact K before delta, then applies native radius-one AD in each occupied ball. This proves n <= C_K*delta^(-eta)*(1/delta)^3. It does not assume a global diameter bound or infer one from local AD.

`NativeCompactParentRetention.compact_parent_bound` combines that count, the explicit chart bound, and the actual parent-label double count to prove #parents <= C_K*delta^(-2eta)*N^3 when delta*L_K*N<=1. Both positive C_K and L_K>=6 are fixed before D, eta, the common height, or N. `NativeCompactParentExponent.compact_dense_parent_retention` absorbs the fixed coefficient: for any epsilon>0 it chooses a cutoff before the finite source, and the actual selected parent retains delta^(epsilon+2eta+3nu) of original incidence mass whenever N<=delta^(-nu) and the same intermediate-scale budget holds.

These results apply to finite sources drawn from one fixed compact original marked family. They do not establish that the unrestricted native near-extremizer sequence from `NativeFiniteKakeyaExponent` stays inside such a common compact family. That quantifier distinction is necessary.

## Completed density-preserving original selection and phase connection

`NativeDenseOriginalParent.exists_dense_parent` selects a genuine parent with at least 1/(2*#parents) of original incidence mass and at least half the original average incidence count per original tube on its complete backbone. This removes the parent-count loss from the per-tube density estimate.

`NativeOriginalShadingDensity.source_incidence_density` proves 16*delta^(eta+beta)*n <= delta*#originalIncidences, using actual native shading density, actual common mesh delta/2, and the established unit-tube volume bound. `dense_parent_density` therefore proves delta^(eta+beta)<=P.lam since P.delta=delta/8. The volume-bound cutoff is supplied by `exists_source_density_cutoff`; no source-density profile is assumed.

`NativeDenseSourceRefinement.dense_source_slice_population` consumes this selected parent in the already-proved simultaneous spatial/phase refinement. It returns one E0 contained in the original cubical incidence set, an exact injective chart readback E, unchanged tube labels and cardinality, all whole-heavy-fiber and spatial/phase population fields, and

    delta^(eta+beta)*#tubes(E0) <= refinementLoss*(delta/8)*#E0.

This is the exact aggregate density requested by the Section21 phase worker. For chart heights of mesh delta/8 in the fixed time window, its verified `OriginalHeightVertexDensity` converts this together with its genuine tube-height occupancy cap C and delta*#Z<=32 into lambda_T=delta^(eta+beta)/(4*C*refinementLoss). No height selection or pointwise degree certificate is inserted. The aggregate density theorem and the phase worker's geometric adapters still need to be assembled with the later global configuration's literal I,Z data; the present result does not claim original slice AD powers (130)–(135), quotient fibers, or the final Kakeya conclusion.
