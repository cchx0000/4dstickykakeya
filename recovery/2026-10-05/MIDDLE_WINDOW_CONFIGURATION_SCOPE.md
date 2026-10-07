# One-core middle-window interpolation

Status: both modules are verified and frozen. The successor module passed strict source and imported-axiom checks for all seven declarations (attempt03) with no extra axioms or missing names. Its source SHA256 is `573e819fa985b3e7c2051d182ba1e579d9a5d91eaf3be71e7a08145d3f3ef4bd`. The complete middle-window module passed strict source compilation and imported-axiom readback for all nine declarations on attempt03, finishing 2026-10-05 at 07:03:17 UTC. Both exit codes were zero, no extra axioms or missing names were found, and the source was unchanged. Its source SHA256 is `b00409a1d82400abe842efcfa1829f0d2fb0dd0c2fa10ea04af00b462b4f1bf1`; its olean SHA256 is `7d02c82ffa09e115ae54d019f02e73215697d16b61d493021a451aaed357a97f`. The frozen fixed-size scale-menu module is unchanged.

## Successor and conditional lower bounds

`NativeScaleMenuSuccessor.exists_successor` chooses the next raw depth using `floor(m*g/level)+1`, with `m=level` handled separately. Its gap is at most `level/g`, including real division. Clipping toward an interval containing `m` preserves successorship and only decreases that gap. Thus the same fixed `Fin (g+1)` schedule supplies both predecessor and successor depths for every target in its middle window.

`partition_multiplicity_lower` proves a finite union inequality. If every occupied conditional incidence set has multiplicity at least `A≥0`, then the entire incidence set has multiplicity at least `A`. Incidence cardinalities partition exactly, and the sum of child support cardinalities is at least the support cardinality of their union. Child spatial supports may overlap arbitrarily.

`nested_parentEdges_eq` verifies that every occupied finer dyadic child inside an original parent is the complete original `E`-fiber at that finer label. No incidence or tube label is replaced.

Combining these gives `off_menu_parent_power_lower`: a successor menu lower bound `delta^b*epsilon_d^(-s)` yields `delta^(b+t*s)*epsilon_m^(-s)` when `d≥m` and `d-m≤t*level`. No point-uniformity or off-menu native-admission premise is used in this lower transfer.

## Deterministic middle-window bounds

`NativeMiddleWindowBalance.middle_old_parent_bounds` uses the predecessor for the upper bound and the successor for the lower bound. The upper incurs the stored point-degree factor `Q^2` and at most `(2/g)*kappa` of scale loss; the lower incurs at most `(1/g)*kappa`.

`middle_coarse_lower` uses the actual physical cube comparison `mu(C_c)≤729*r^4*mu(C_m)`. Its scalar consumer pays `729≤delta^(-b)` and `r≤delta^(-2/g)`, producing lower exponent `2*b+(2/g)*(4+kappa)`. The all-scale coarse upper comes directly from the previously proved same-source coarse admission theorem.

## Genuine-source endpoint

`exists_middle_configuration` first fixes

- `w0=min(window,tau/1000)`
- seed tolerance `b=tau/8`
- the finite count `g+1` from the frozen menu theorem
- the balanced-source parameters and all scale cutoffs

Only then is a genuine fixed-compact near-extremizer requested. Its original family `R` and source data are retained in `HasOriginalBackbone`, including the complete original all-dyadic population law. A single call to the finite balanced-core endpoint supplies `E` and all scheduled native/balanced conclusions. The caller's fixed old relation menu explicitly includes equality of `(menu parent, original fine cell)`.

The source-facing statement exposes `zeta≤tau/2048`, `eta<tau/64`, the fixed-grid inequality `1/g<min(window,tau/1000)/4`, `g≤level`, and equality of its returned schedule with `canonicalSchedule`. Later consumers can therefore use the actual clipped-menu witnesses directly.

The final `HasMiddleScale` conclusion gives, for every integer depth `window*level≤m≤(1-window)*level`, the two-sided powers `delta^±tau*rho_m^(-kappa)` for the full physical coarse shadow and `delta^±tau*epsilon_m^(-kappa)` for every active original parent incidence set. Here `rho_m=64/2^m`, `epsilon_m=2^m*delta/64`, and their product is exactly `delta`.

The source-facing endpoint preserves the exact `IsCore` and the scheduled actual local-source statements. It does not assert native admissibility for off-menu local sources. It also does not establish individual off-menu coarse shading uniformity, endpoint-window extensions, or the relative two-scale geometric comparison needed for full manuscript equation (113).
