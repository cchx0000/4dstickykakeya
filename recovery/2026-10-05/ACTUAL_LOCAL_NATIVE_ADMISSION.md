# Actual local native admission

Frozen staged module: `Theorems/Thm_StickyKakeya4_native_actual_local_admission.lean`

Main theorem: `NativeActualLocalAdmission.compact_original_scheduled_native_admission`.

The endpoint fixes the target exponent `e > 0`, relative-window exponent `alpha > 0`, and finite menu sizes `d,g` before selecting `zeta,L,eta0,delta0` and before receiving the source. The source is an actual compact native finite input. Its only analytic input assumptions are its original native predicate, compact carrier membership, and the chosen small scale/exponent cutoffs.

Canonical compact regularization is called once through `compact_original_scheduled_parent_density_core`. Its original retained label set `R`, half-cardinality and half-shading retention, retained density, original CW, and all dyadic ancestor populations are returned unchanged. After the old relation menu and relative-window scale schedule are supplied, one literal original incidence set `E` is selected. `IsCore` on that same `E` retains the old relations, original incidence retention, scheduled parent uniformity, average-parent density, and pair-fiber lower bounds.

For every incidence-active scheduled parent, the theorem admits the literal `NativeLocalParentSource.source` indexed by the full original `R`-parent, including labels with empty selected shading. Its shading is constructed from precisely `parentEdges E`, without reselecting labels or incidences. The result is `IsWangZakharovNativeFiniteInput S e` and carrier membership in the fixed compact class.

The proof derives actual AD through exact `wzCarrierBallCount` readback, original ancestor occupancy, and direction packing. It derives CW through exact `wzContainedTubeCount` readback and the actual physical inverse map, for all convex sets including infinite-volume sets. Density uses the verified actual-source density lemma, selected old-parent average density, genuine local mesh, and the geometric cell-fiber capacity. All three scalar budgets are supplied internally by `exists_uniform_source_budget` on the actual retained incidence set; no assumed output profile, density, fiber, or subpower-radix certificate occurs in the source-facing endpoint.

`HasExactTrace` records literal thickness, the full original-label range, exact reindexed incidence image, total shading mass, union volume, and multiplicity of the same source. The endpoint also compares original selected-parent multiplicity with the actual source multiplicity, with coefficient `(125 * 175616 * 16384) * F * Q^2 * delta^(-eta)` and no remaining relative-scale factor.

This is a finite-schedule native-admission theorem. It does not assert full manuscript (113), an all-scale uniform core, or a terminal volume estimate.

Verification: `verification/native_actual_local_admission-attempt05/result.json`.

- Official Lean 4.33.1, strict auto-implicit and warning settings
- Source compile exit 0; separate imported declaration readback exit 0
- All 9 public declarations audited; only `propext`, `Classical.choice`, `Quot.sound`
- Source SHA256: `73b53f1e1efb8fd6f2f187003d9f391c4865ac237233b0a00dce69d0b2293c4c`
- Olean SHA256: `2ddc2422fae8400110d569d56c350ae396ca8090c3b45f7894e8359498c5a454`
- No canonical source edits, commits, or independent Lake build
