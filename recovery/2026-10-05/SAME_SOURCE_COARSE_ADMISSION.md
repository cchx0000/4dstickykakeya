# Same-source coarse upper: audited and strictly verified

The actual full coarse upper now accepts the exact original family R and selected incidence set E from `NativeOriginalParentDensityCore.IsCore`. It does not call a second original-family or incidence-selection constructor.

## Earliest adaptation

`NativeCoarseShadingCapacity.total_incidence_capacity` already supports arbitrary E with every edge on R and in the original shading. `actual_aggregate_shading_transfer`, and consequently `NativeCoarseDyadicShading.original_dyadic_shading_transfer`, were the earliest specializations that hard-coded `retained original R`. The original selection/admission constructors then selected their own R.

The new theorem `NativeSameSourceCoarseSelection.selected_dyadic_shading_transfer` uses the existing arbitrary-E incidence capacity directly. With delta = D.thickness, rho = 1 / 2^m, B = 4096 * 2^(level-m), and the original ancestor upper count at m, it proves

    E.card * (delta/2)^4 <= 43 * delta^(-zeta) * sum_p weight(D,a,level,m,rep,E,p)

The original count retention `(incidences original).card <= F * E.card` gives exact original mass retention on the common mesh, via `original_mass_le_selected`.

## Verified contracts

`same_source_coarse_selection (hzeta : 0 < zeta) (F : Nat) (hF : 0 < F)` fixes a positive cutoff before any D. Under native input, eta <= zeta/16, prescribed original/a/level/R/E, exact common-cell representation, original dyadic thickness, slab condition, R nonempty, E subset retained(original,R), global incidence retention by F, and the original two-sided ancestor law H, it constructs a coarse parent subset at every 6 <= m <= level.

Its conclusions are literal representative directions separated at 64/2^m, actual E-shading mass at least delta^(5*zeta), and actual ancestor populations between delta^(8*zeta) and delta^(-2*zeta) times the dyadic cubic ratio. Neither R nor E is replaced.

`NativeSameSourceCoarseAdmission.same_source_coarse_admission (he : 0 < e) (hw : 0 < window) (F : Nat) (hF : 0 < F)` fixes a positive cutoff. Set zeta = window*e/32. The same prescribed-source premises, eta <= window*e/512, and the two-sided window

    rho <= delta^window
    delta/rho <= delta^window

give an actual source `NativeCoarseCellSource.source h a level m Q rep E hsep` that is native at exponent e, has lines in fixedCompactClass, and satisfies

    ENNReal.ofReal(delta)^(7*zeta) * multiplicity(fullSource h R a level m E)
      <= multiplicity(actual admitted coarse source).

`same_source_full_coarse_upper` chooses the admissible exponent from fixed-compact extremality and proves

    ENNReal.ofReal(delta)^(7*zeta) * multiplicity(fullSource h R a level m E)
      <= ENNReal.ofReal(64/2^m)^(-extremalExponent-epsilon).

All hypotheses before the constructed coarse source concern original native data, original ancestor populations, global selected-incidence retention, or explicit scalar parameters. There is no assumed output density, AD, CW, or output certificate.

## Quantitative losses

- Original selected shading to full coarse shading: 43 * delta^(-zeta)
- Angular color: colorCost * delta^(-zeta), where colorCost = 23328*512^3
- Finite-menu selection: F, fixed before D, with F = NativeOriginalParentDensityCore.factor d g L = 4*(4*(d+2*g))^((d+2*g)*L)
- Additional cutoff: (43*F*colorCost)*delta^zeta <= 1
- Selected color shading mass: delta^(4*zeta)
- Coarse ancestor pruning threshold: delta^(8*zeta)
- Shading deletion budget: pruneCost*(m+1)*delta^(7*zeta), where pruneCost = 746496*64^3*volumeConstant
- Retained shading mass: delta^(5*zeta)
- Native density coefficient: delta^(7*zeta), then transfer to output thickness exponent e
- CW intermediate coefficient: cwCost*delta^(-eta-6*zeta)
- Full coarse to admitted core multiplicity: delta^(7*zeta)

The fixed F increases only the smallness cutoff. No additional exponent and no radix loss enter this global coarse construction.

## Joint-assembly parameter order

Choose the common e from fixed-compact extremality first. Run the local budget primitive with alpha = window/2, so its exposed equality zeta = alpha*e/16 gives precisely window*e/32. The local budget fixes L, eta0 = zeta/16, and its cutoff; then F = factor d g L is fixed. Call the deterministic coarse admission with this e/window/F. Intersect cutoffs. Invoke the compact ancestor regularization and scheduled core exactly once. Use the same R/E for actual local admission and for the deterministic coarse theorem.

The frozen existential local endpoint hides the equality for its chosen zeta; use its budget/core primitives in the joint endpoint, rather than pairing two independent existential outputs. The standalone full-coarse wrapper is useful independently, but the joint endpoint should call the arbitrary-e deterministic admission and then its already-chosen extremal bound.

## Verification

Source: live/Theorems/Thm_StickyKakeya4_native_same_source_coarse_selection.lean
SHA256: 71b93bda1f772186f66a9f0bf5f380206cd7be969419c562d72f508462e0981f
Strict source and imported readback: verification/native_same_source_coarse_selection-attempt02/result.json
Four public declarations. Only propext, Classical.choice, Quot.sound.

Source: live/Theorems/Thm_StickyKakeya4_native_same_source_coarse_admission.lean
SHA256: db6bcd86858eb952d83bc5907179a87040abd14f7ae6554193b943979513190f
Strict source and imported readback: verification/native_same_source_coarse_admission-attempt01/result.json
Two public declarations. Only propext, Classical.choice, Quot.sound.

All six declarations were checked with autoImplicit=false and warningAsError=true. The new files and compiler artifacts are isolated staging outputs. No canonical theorem source, Git commit, or GitHub mutation was made. An already-launched five-module prerequisite staging loop completed while the parent's canonical graph ran; it used the shared compiler-slot cap and changed no canonical sources.

Remaining assembly outside this deliverable: connect the abstract incidence tower to the physical fullSource using actual coarse pair/point labels and original-menu uniformity; combine with the independently owned actual local and relative-parent profile results. This audit does not claim WZ(107)-(113) or the final volume theorem complete.
