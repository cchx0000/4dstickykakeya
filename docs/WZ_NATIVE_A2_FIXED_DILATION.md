# Native A.2 fixed dilation and original A.1 input adapter

This checkpoint extends the frozen 48-proof native A.2 chain without modifying any of its sixteen source modules.

## Closed endpoint

`NativeA1InitialRadialGraph.exists_original_eta_dilated_radial_threshold` proves: for fixed `0<t<=2`, `0<eps1<1/8`, `eps2>0`, and fixed `C>=1`, there is a positive threshold `d(t,eps1,eps2,C)`. For every `0<delta<=d`, `eta<=chi`, and `0<chi<=t*eps1/12`, take a nonempty finite original `P` in `[-1,1]^2` with:

- Original Euclidean radius-r ball counts at most `delta^(-eta)*r^t*|P|` for every original center and every `delta<=r<=1`
- Original physical unit-tube counts at full width `delta^eps1` at most `delta^eps2*|P|`

It constructs `G subset P x P` such that

- `|G| >= (1-delta^min(t*eps1/2,eps2/2))*|P|^2`
- Every retained pair is distinct
- The actual original-point count in the physical `C*delta^(4*eps1)` neighborhood of its genuine affine pair line is strictly less than `delta^chi*|P|`

The original `eta`-Frostman profile is weakened to `chi` by a proved real-power comparison. No intermediate ball-cap, geometric containment, representative-family, incidence, graph, or weakened-profile certificate is supplied.

## Fixed-dilation bookkeeping

Keep `theta=delta^eps1`, `rho=theta^2`, determinant cutoff `theta/8`, and richness `delta^chi`. Replace the original strip halfwidth by `w=2*C*theta^4`. The constructed representative strips then have width `22*C*theta^2`, and their transverse query radius is `R=704*C*theta`.

The original profile overlap condition is unchanged: `8*delta^(2*t*eps1-3*chi)<=1`. The original two-ends strip condition follows from `theta<=1/(1408*C)`. The bad-pair bound is

`16*(704*C)^2*delta^(t*eps1-3*chi) + 4*delta^eps2 + 4*delta^(t-chi)`.

For its power absorption, the only changed condition is

`delta^(t*eps1/4)<=1/(48*(704*C)^2)`.

All profile radii are formally proved to lie in the original interval `[delta,1]`. The fixed dilation therefore changes the sufficiently-small-delta threshold, not the graph-density exponent or admissible chi interval. The threshold is uniform in both eta and chi subject to the stated inequalities.

## New modules

- `NativeA2DilatedParameters.lean`: 4 proofs; geometric query bounds, exact transverse exponent, power absorption, positive threshold
- `NativeA2DilatedCaller.lean`: 2 proofs; actual fixed-dilation graph and chi-uniform existential threshold
- `NativeA1InitialRadialGraph.lean`: 1 proof; original eta-Frostman adapter

Source and independent imported validation are recorded in the [phase/bin checkpoint](../verification/wz-phase-bins-checkpoint.json). These seven proofs extend the previously checked 48-proof radial chain without modifying it.

## Exact scope

This provides the initial graph and fixed dilation used at source (213)-(214), printed p108 of https://arxiv.org/pdf/2609.22035. It does not supply the subsequent radial multiscale comparison, annulus estimates, Theorem A.3's Furstenberg gain, the full Theorem A.1, or the final sticky Kakeya theorem. The arbitrary-positive-eps1 extension of standalone Lemma A.2 remains outside the stated native range.
