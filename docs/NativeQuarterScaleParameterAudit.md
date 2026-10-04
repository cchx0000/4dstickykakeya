# Native quarter-scale parameters and dyadic BSG interface

The frozen parameter batch is `original_native_parameters.manifest.json`: two modules, fourteen public proofs, strict Lean 4.33.1 and a proper-import audit using only propext, Classical.choice, and Quot.sound. Earlier source-population, angular, and actual-ABC batches are linked in that manifest. This note records the quantitative caller obligations; it does not assert the final Lemma 21.1 or Theorem 21.2.

## Literal source scale

Lemma 21.1, equation (167), assumes original affine nonconcentration for rho in [delta^(1/4), delta^mu]. At 0 < delta < 1, the quarter endpoint belongs to this interval when mu <= 1/4. The printed opening states only mu > 0. The actual Proposition 17.4 proof explicitly uses rho = delta^(1/4) and mu = 1/4, so that native caller supports this specialization. A general arbitrary-mu theorem must retain the interval-membership premise; for mu > 1/4 the printed interval is empty.

## Original tube width and representative error

Write s = epsilon0 and r = delta^(1/4). The actual coarse representative error e must satisfy e <= delta^(-g) r. Scheduled-bin and normalization factors are charged in g. The positive gap g + 2s < 1/4, followed by the constructed delta cutoff, yields e <= delta^(2s)/8.

Use original cross-tube width w0 = delta^(2s) and near-vertical splitting parameter delta^s. Fine points charged to a coarse representative lie in the widened original tube of width w0 + 2e. If the effective slope normalization Lip <= delta^(-ell), with ell < 3s/4, the proved strict inequality is

    Lip * r * ((delta^(2s) + 2e) / delta^s) < r^(1+s).

This is the literal strict physical width required by (167). If the working geometric radius differs from the original quarter block, Lip here must include that ratio; the original source radius on the right is not silently enlarged. Both the representative and affine inequalities have explicit positive cutoffs.

## Projection budget

The finite projection reciprocal-area cost requires another width gap. The checked choice is

    r0 = delta^s, w0 = delta^(2s), w = delta^(4s).

For close-pair and line fractions <= delta^u and parameter mesh <= delta^s, where 0 < u <= s, the scalar projection condition holds once delta^(u/4) <= 1/396, with theta = delta^(u/4). The choice u = min(s/4, epsilonSource/16) respects the independent original avoidance exponent epsilonSource; no comparability with s is presumed. Original fiber/density losses must first be absorbed using their actual proved exponent envelopes.

For fixed original loss coefficients Cgrain, Clip, and Ccost, the checked eta region has

    Cgrain*eta + 2s < 1/4,
    Clip*eta < 3s/4,
    Ccost*eta <= u/2.

It is nonempty whenever 0 < s < 1/8 and u > 0. The finite parameter grid and dyadic spatial scale menu are constructed, with menu size at most log(2/rho)/log(2) + 2. Absorbing these logarithms and the remaining source losses into delta powers is still part of full original-configuration assembly.

## Uniform angular exponent

The common source Phi is the exact Definition 17.2(4) alphabet. Its original separation and unit interval box imply |Phi| <= 4/q. Its AD lower mass then gives kappa < 2 whenever K*q <= 1/8. Consequently the balanced finer-mesh angular cost is at most 16*K^2*(q/(2*mesh))^2 when q/(2*mesh) >= 1. This supplies uniformity in the original exponent instead of assuming kappa <= 1 from terminology.

On the nontrivial branch kappa > zeta, only the upper Frostman exponent is weakened to the fixed positive exponent zeta/2. The original cardinality lower bound, with exponent kappa, remains unchanged. This avoids a uniformity assumption on the analytic cutoff over varying original kappa.

## Dyadic mesh and actual BSG data

The separately frozen `native_dyadic_abc.manifest.json` batch contains four modules and sixteen public proofs, each strictly compiled and properly import-audited. Its dyadic interface chooses a projection mesh rho in [t/2,t), where t is the actual normalized spatial mesh. Once t <= 2^(-n0), the dyadic index is at least the analytic cutoff n0. Balanced normalization gives mesh rho/8 = 2^(-(m+3)). Original KT1 profiles transfer to every finer mesh with the same absolute constant. The original B mass parameter loses at most a factor two, and the actual endpoint-error/mesh ratio gains at most a factor two.

The constructed `NativePlanarABCInput.Data` already contains actual sets and graph, unit-box bounds, separation, and actual occupied floor-grid output cover. Its planarCells grid is definitionally the vector BSG caller's roundPoint grid. The adapter preserves the order in which the BSG constants K and n0 are chosen before the density, cover constant, and all source sets.

With projection loss L, original graph density beta, and original normalized endpoint error E, the adapter receives density beta/L and cover constant (L/beta)*(4E/rho+8)^2. Thus the BSG source parameter beta_out^2/M_out is exactly beta^3/[L^3*(4E/rho+8)^2]. The vector caller further divides by 392*H^2, with H the original B-times-C fiber level count.

`OriginalEuclideanAffineAvoidance` uses the literal length sqrt(v1^2+v2^2), proves it is at most twice the native product norm, and derives the unchanged-original-set sup-norm avoidance law at half the source threshold. Its quarter-scale adapter charges 2*Lip into the effective Lip bound and feeds the native affine tube cap. Thus the source Euclidean metric is not silently identified with the native product metric.

## Final native mesh and fixed-exponent data

The third frozen batch is `native_quarter_abc_parameters.manifest.json`: two modules and nine public proofs. Across the three new parameter/interface manifests there are eight modules and thirty-nine public proofs; all are strictly compiled and properly import-audited.

`NativeQuarterBalancedMesh.exists_balanced_quarter_dyadic` takes the ACTUAL common normalization 1 <= S0 <= delta^(-g). If delta^(1/4-g) <= 1/16 and the quarter scale is below the already chosen analytic cutoff, it selects a dyadic projection mesh rho with

    quarterScale/(2*S0) <= rho < quarterScale/S0,
    mesh = rho/8 = 2^(-n), n >= n0,
    delta^(1/2) <= mesh <= delta^(1/4).

These exact inequalities give native strip exponent 32*s after delta^(4*s) <= 1/8, line fraction exponent u/4 from the already charged fraction delta^(u/8), and both power conversions

    mesh^(4*a) <= delta^a,
    delta^(-a) <= mesh^(-4*a), for a >= 0.

An original B mass lower bound lambda <= quarterScale*|B| becomes lambda/(2*S0) <= rho*|B| on the same B. Thus choosing physical height bins of width quarterScale^2 and substituting the proved upstream coarse-height mass gives the exact lower population needed by the actual planar constructor after common scaling and dyadic rounding.

`NativePlanarABCFixedExponent.actual_angular_constant_ge_one` derives angularK >= 1 from the actual nonempty unit-box C population itself. `exists_zeta_exponent_data` then weakens the upper Frostman exponent to zeta/2 on every radius at or above the actual mesh, including radii above one. It returns exactly the same A, B, C, and G, so every original cardinality lower bound and every original graph/cover witness remains available. No separate C regularity premise is added.

## Remaining closure

The source native configuration must still provide the numerical envelopes for original phase KT constants, original graph density, original B lower population, normalization and scheduled-scale ratios, and original affine avoidance fractions. The checked constructors give their exact finite dependencies; a desired projected density or cover is never an input. The deep ABC expansion after the vector BSG reduction and the final source-cardinality contradiction remain separate work.
