# Fixed finite scale menu and interpolation audit

The implementation is confined to the staged module `Theorems/Thm_StickyKakeya4_native_fixed_size_scale_menu.lean`. Its index type is `Fin (g+1)` with `g` chosen before the source depth. It does not choose or alter an original family `R` or an incidence set `E`.

Strict verification attempt04 passed source compilation and imported-axiom readback for all 24 declarations on 2026-10-05. Both exit codes were zero, the source was unchanged, and no missing names or extra axioms were found. Source SHA256: `9e859a3ed41d26b0a6f74896b16f1c1fa32fed75ab6ff79f666daffb005be404`. The result is recorded in `../verification/native_fixed_size_scale_menu-attempt04/result.json`.

## Finite menu

The raw schedule is `j ↦ floor(j*level/g)`, implemented by natural-number division. For `m ≤ level`, a predecessor is obtained from `j=floor(m*g/level)`. Its depth `c` satisfies both `m-c ≤ level/g+1` in natural numbers and `(m-c:real) ≤ level/g+1` with real division. The latter gives the exact dyadic estimate

`2^(m-c) ≤ 2*delta^(-1/g)` when `delta=2^(-level)`.

For consumers whose premise is a pure fractional depth bound, the module also gives `m-c≤(2/g)*level` under the fixed extra cutoff `delta≤2^(-g)`. This is exactly the premise required by `NativeLocalMenuInterpolation.off_menu_parent_power_absorbed` with `tau=2/g`.

The usable schedule clamps each raw entry to the interval

`[ceil((w/2)*level), floor((1-w/2)*level)]`.

Every entry consequently lies in the relaxed power window. The number of indices stays `g+1`; repeated endpoints are allowed. If `0<w<1/2`, `1/g<w/4`, and `4≤w*level`, each target `w*level≤m≤(1-w)*level` has a raw predecessor already inside that interval, so clamping leaves that witness unchanged. Parameters `g` and a minimum depth `N` can be fixed from `w` alone. The cutoff `delta≤2^(-N)` forces `N≤level`.

## Same-incidence local interpolation

At each menu depth `c`, append the old relation

`(parentLabel_c(e.tube), e.cell) = (parentLabel_c(f.tube), f.cell)`

to the single finite uniformization. On a menu parent incidence set `I`, its degree is exactly the original fine-cell degree in `I`. The resulting `Q^2` comparison, together with `NativeUniformMultiplicityRestriction.subset_weighted_mass_cross` at unit weights, gives

`mu(J) ≤ Q^2 mu(I)` for every genuine subset `J⊆I`.

The finer parent at any depth `m≥c` is such a subset by `NativeDyadicParentCells.parent_ancestor_eq`. If its local scale is `epsilon_m=r*epsilon_c`, where `r=2^(m-c)`, transferring a menu upper bound loses `Q^2*r^(kappa+loss)`. Since `0≤kappa≤3`, the dyadic gap can be paid by an arbitrarily small original-scale power when `g` is sufficiently large. No off-menu native admission is asserted or needed for this inequality.

## Physical coarse interpolation

Let `C_t` be the actual projected coarse pair image of the same original `E` at depth `t`, and `X_t` its spatial-cell support. For `c≤m`, let `r=2^(m-c)`. Both representatives lie in one original `c`-parent. The existing `same_parent_front_error` shows their front points differ by at most `1/(64*2^c)` per coordinate, which is `1/2048` of the coarse cube mesh. Heights agree exactly.

Therefore the actual coarse index differs from the coordinatewise integer quotient of the actual fine index by at most one in each of three spatial coordinates, with identical quotient height. A fixed fine pair has at most 27 coarse pairs over it. A fixed coarse spatial index has at most `27*r^4` fine spatial indices over it. Thus

`|C_c|≤27|C_m|`, `|X_m|≤27*r^4|X_c|`, and `mu(C_c)≤729*r^4*mu(C_m)`.

These are genuine image-of-fiber counts, not an assertion that projected labels factor exactly through one another. The reusable assembly lemma `NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images` is designed for precisely this situation. Transferring a lower power `rho_c^(-kappa)` to `rho_m^(-kappa)` loses at most `r^(4+kappa)≤r^7`; retaining a factor `epsilon_c^loss` adds another `r^loss`.

The existing `NativeSameSourceCoarseAdmission.same_source_coarse_admission` already applies at every depth in its window after `R`, `E`, and the fixed retention constant are supplied. Its full physical coarse upper bound does not require off-menu uniformity or a new selection of `E`.

## Boundary strategy, not yet a proved all-scale endpoint

For local upper bounds near the fine endpoint, the literal inequality `mu(E_p)≤#R_p`, followed by original direction packing, gives `mu(E_p)≤5832*(rho/delta)^3`. If `rho/delta≤delta^(-w)`, the cost is at most `5832*delta^(-3w)`.

Near the coarse endpoint, partition a coarse original parent into parents at the first admitted menu depth. Summing incidence counts and comparing each conditional support with the full parent support gives `mu(I)≤sum_q mu(I_q)`. The number of descendants is bounded by `delta^(-2*zeta)*r^3` using the unchanged original all-dyadic population law, or by `r^6` from the six literal dyadic parameter coordinates alone. Either loss is a small power when the endpoint window width is small.

For full coarse shadows near the coarse endpoint, nonempty `E` gives `mu(C)≥1`. This already yields the needed lower power with loss at most `delta^(3*w)`. The forward physical comparison above transports upper bounds from the first admitted menu.

Near the fine endpoint, the forward physical comparison transports lower bounds from the last admitted menu. For the reverse upper comparison, a fixed coarse pair has at most `r^6` descendant parent labels and at most `27*r^4` possible fine spatial labels. Consequently the crude reverse count is `|C_m|≤27*r^10|C_c|`; combined with `|X_c|≤27|X_m|` it gives `mu(C_m)≤729*r^10*mu(C_c)`. This requires formalizing the finite descendant-label count and the reverse physical count; it is not presently claimed as an available Lean theorem.

This module and audit establish only the finite-menu quantifier mechanism and identify the remaining geometric/counting obligations. They do not assert manuscript equation (113), all-scale uniform coarse shading, or the final volume theorem.

In particular, uniform individual coarse shading mass is separate from average multiplicity interpolation. A finer off-menu child can retain very little of its menu ancestor's incidence set while siblings retain most of it. Menu point-degree uniformity therefore does not by itself imply comparable shading-row counts for every off-menu child. An all-scale version of the individual shading clause requires an additional argument; it must not be inferred from the global physical multiplicity comparisons.
