# Actual local upper with arbitrary original-scale loss

Frozen staged modules:

- `Theorems/Thm_StickyKakeya4_native_local_transfer_budget.lean`
- `Theorems/Thm_StickyKakeya4_native_actual_local_power_upper.lean`

Main theorem: `NativeActualLocalPowerUpper.compact_original_scheduled_local_power_upper`.

The extremal margin `epsilon > 0`, relative-window exponent `alpha > 0`, desired original-scale loss `theta > 0`, compact original carrier set, and finite menu sizes are fixed before all source-dependent choices.

The canonical fixed-compact upper theorem provides a positive admissibility exponent `eu` and a local cutoff. The construction chooses `e = min eu (theta/alpha)`, invokes the source-derived admission budget at that `e`, and uses its quantitative choices `zeta = alpha*e/16`, `eta0 <= zeta/16`, and `L > 256/(alpha*e)`. They imply `eta0 + 8/L <= theta/2`.

`NativeLocalTransferBudget.exists_parent_transfer_cutoff` uses the proved bound for the radix of the actual retained incidence set. It absorbs the fixed coefficient and the exact finite-menu retention factor before the source is supplied. Consequently the endpoint derives, rather than assumes,

`(125*175616*16384)*F*Q^2*delta^(-eta) <= delta^(-theta)`.

The compact density core is called once. The original `R`, its original cardinality/shading retention and ancestor laws, and one literal `E` for the supplied menu are preserved. Every active full original `R`-parent supplies the same actual local source used throughout:

- Native admissibility at exponent `e`
- Membership in the fixed compact carrier class
- Exact original-label/incidence/mass/union/multiplicity trace
- Canonical fixed-compact multiplicity upper, consumed using native exponent monotonicity from `e` to `eu`
- Original selected-parent geometric multiplicity transfer
- Combined upper `old_parent_multiplicity <= delta^(-theta) * S.thickness^(-extremalExponent-epsilon)`

The endpoint has no output native-input, AD, CW, density, fiber, or radix certificate assumption. The local cutoff is paid through the supplied relative window. All free exponents and cutoffs precede `D`, `R`, `E`, and the selected active parent.

This is the local upper application with arbitrary small original-scale loss, for finite menus. It does not assert an all-scale core, full (113), or a final volume theorem.

Verification:

- `verification/native_local_transfer_budget-attempt02/result.json`: all 3 declarations passed strict source and imported-axiom checks
- `verification/native_actual_local_power_upper-attempt01/result.json`: the endpoint passed strict source and imported-axiom checks
- Only `propext`, `Classical.choice`, `Quot.sound`; no missing declarations or extra axioms
- Transfer-budget source SHA256: `0e84a130d9a38d18b20f6a8dbd45ccbaa37e93d6b52ae64da79cbc86cf68d6d7`
- Power-upper source SHA256: `d8b0bdd9cee163627bd3d5e90ade16d81a064865d13f4a90609a7e8c44d2486f`
- Power-upper olean SHA256: `385c0ce5fa79c17e0bcad99667aee53fb43d9d758820a7e85480d710409203b0`
- Official Lean 4.33.1, shared two-slot cap, one Lean thread per job
- No canonical source edits, commits, or independent Lake graph
