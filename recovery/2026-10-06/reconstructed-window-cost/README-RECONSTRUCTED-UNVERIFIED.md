# RECONSTRUCTED — UNVERIFIED

Recovered on 2026-10-06 from retained conversation patches after the environment reset. No Lean compiler or fresh imported-axiom check has run on these files. No canonical repository or external service was modified.

## Recovered Lean files

1. `Thm_StickyKakeya4_native_window_power_payment.lean`
   - Namespace: `NativeWindowPowerPayment`, seven declarations
   - SHA256: `f5cf08c01be409109f771c72d668ab078f98027272bf61141299619ae9330b38`
   - This exactly matches the recorded historical attempt03 source hash
   - Includes the post21:00 `StickyKakeya4` namespace repair and the final `ring` after `norm_num` in `exists_source_product_cutoff`
   - Historical attempt02 failed only at `2 * (budget / 2) = budget`; attempt03 was queued on Oct5 at21:20:44 and its terminal outcome was not observed before interruption
   - Byte equality is recovery evidence, not fresh proof verification

2. `Thm_StickyKakeya4_native_window_source_constant.lean`
   - Namespace: `NativeWindowSourceConstant`, four declarations
   - SHA256: `fc3636dcf334fc2c5c4ebd9e76d761eb92e8076e5318080851a46fb50b9cc2e1`
   - Reconstructed from the complete creation patch and subsequent patches
   - `windowConstant_pre_loss` was added at21:08; it preserves exactly one coherence multiplier in XY
   - `windowConstant_le_retained` compares the literal variable-height source coefficients with the same retained constant
   - `windowConstant_le_retained_power` keeps the source Lipschitz power explicit
   - `pay_factory_window_and_quotient` uses the actual factory allocation `Lip <= 3*r^(-2*geometryTolerance)`
   - This file was a draft and had never been submitted to Lean before interruption

## Existing dependency: do not recreate unnecessarily

`native_window_constant_algebra` should be restored from backup. Retained context records a two-line attempt02 repair at21:00:46:

- Remove the redundant `ring` after a closing `field_simp`
- Supply `(s:=s)` explicitly to `constant_mono`

The separate patch in this directory preserves only those two changes. Apply it only if the restored source is the old variant:

- Old attempt01 source SHA: `5b10281782b711e40d3aed2d152eb955925f5f64b527e2fe4aed54a8000391fd`
- Repaired attempt02 source SHA: `ad9d71dfa3bfecb878e49f8cfd9bd23eda24084233b7f0db80945fc4db1de9df`
- Historical source check passed at21:24:07; historical olean SHA: `a5e92c78110bad5130c209792747a77efe8448600f6b3bbbb10cc64d986da7ec`
- No fresh verification is claimed

The actual window-definition dependency was historically source-passed with unchanged definitions:

- `native_actual_window_XY_ad`, attempt02
- Source SHA: `8fa908e22b8a487965d3887e74cf3e2c5dbae2dbfe9132c8943cf7a4f4135ee9`
- Namespace `NativeActualWindowXYAD`; required definition `windowConstant`

Other restored imports required by the draft are `native_window_coefficient_comparison`, `native_XY_pre_loss_budget`, and `native_third_XY_fixed_budget` with their existing import closures. No new Lake graph or full cold build was started.

## Exact scalar accounting

For a source Lipschitz bound `Lip <= A*r^(-e)`, the map capacity has degree nine in Lip:

`C^3 <= (2418*A)^9 * r^(-9*e)`

The source reference ratio contributes65536, the change from max8 to max64 contributes512, and the endpoint cover contributes27. Therefore

`coordinateCost A = 65536 * 512 * 27 * (2418*A)^9`.

Using `rho^2 <= 6144*r`, the original-r exponent9e becomes18e at rho. The quotient factor512000 is included only in the final product:

`productCost A e = 512000 * coordinateCost A * 6144^(9*e)`.

The cutoff theorem chooses delta0 before D from `budget,c,A,e`, assuming the existing source scale order `c^3/8 <= a`, `r <= delta^a`. The same source factory can intersect this delta0 with its existing deltaBound without changing L3, D, R, E1, E2 or T.

For the actual factory, A=3 and e=2*geometryTolerance. The geometry tax is18*geometryTolerance at r, or36*geometryTolerance at rho. Retained, sharp-X and fixed-product allowances of epsilon/4 each suffice for the base quotient-Y bound at epsilon when geometryTolerance<=epsilon/144.

The external coherence multiplier remains explicit: assembly confirmed one multiplier M in XY and one M in sharp X, hence M^2 in quotient Y. The window pre-loss lemma preserves this allocation. It does not independently pay M.

## Endpoint recovery scope

No endpoint-union Lean file had been written before interruption. Only the mathematical plan and searches for existing finite-union AD lemmas had begun. The recovered plan is in `endpoint-counting-plan-UNVERIFIED.md`; it is not a recovered proof or a compiled theorem.
