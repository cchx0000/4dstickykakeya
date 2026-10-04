# Native A.3 small-shading engine audit

2026-10-04. This is a dependency and implementation audit, not a new Lean gain theorem.

The 13 annular/source-caller declarations remain frozen in
`WZ_NATIVE_A1_ANNULAR_MANIFEST.json`. Their eight source and olean hashes were
rechecked against the manifest. The separate five radial-class declarations
also match `WZ_NATIVE_RADIAL_CLASS_PRUNING_MANIFEST.json`. No frozen module was
changed for this audit.

## Exact next deep assertion

For mesh d, let Q be a nonempty planar d-grid carrier, E a separated set of
slopes, and 0<s<=sigma<=2. Require normalized sigma-Frostman counts for Q,
local occupied-cell counts at every pair of scales bounded by
K(R/r)^sigma, and normalized s-Frostman counts for E. For each
v<min((s+sigma)/2,1), the needed theorem chooses positive epsilon and d0
before Q,E,d. If K<=d^(-epsilon) and d<=d0, at least half the directions
must have at least d^(-v) occupied projected d-cells for **every** subset
Q' of size at least d^epsilon |Q|. Fixed chart and cell constants can be
absorbed by choosing a strict exponent margin.

This is the finite regular-projection input at OS (5.34), obtained from
Corollary 4.9/5.32. Its application must allow different dense Q_theta for
different theta. The regularity assumption includes the two-scale local
cover bound; original normalized point Frostman alone does not supply it.
[Primary source: OS v4, pp. 25–26 and 51](https://arxiv.org/pdf/2301.10199v4).

## What the actual Lean engines supply

The following statements were read in the current repository. The paths
below are relative to `4dstickykakeya/Theorems`.

| Existing declaration | Actual input and result | Consequence for this task |
| --- | --- | --- |
| `TwoTubePathCollisionCount.square_card_le_image_mul_collisions`, `Thm_StickyKakeya4_two_tube_path_collision_count.lean:175` | Exact finite source labels and a label map; Cauchy–Schwarz gives squared source size <= image size times collisions | Already supplies the finite small-image-to-energy counting step. Reproving it is unnecessary |
| `ActualPlanarRoundedEnergy.original_planar_near_energy`, `Thm_StickyKakeya4_actual_planar_rounded_energy.lean:104` | Actual bounded-mesh separated planar sources; coordinate near-sum energy is at most 49 times integer additive energy | Converts genuine approximate collisions into the integer engine; it assumes no growth conclusion |
| `PlanarOriginalDyadicBSG.original_planar_dyadic_bsg`, `Thm_StickyKakeya4_planar_original_dyadic_bsg.lean:203` | Literal original Euclidean near-sum energy and bounded separated original sources; constructs original subsets and bounds all their rounded iterated sum-differences | A real additive-combinatorial tool, but its output is an upper sumset bound. It does not force any slope to expand |
| `AsymmetricDyadicAbsorption.original_real_dyadic_bsg`, `Thm_StickyKakeya4_asymmetric_dyadic_absorption.lean:278` | Original separated real sources, dyadic mesh, actual near-difference energy; polynomial retention and small iterated rounded sumsets | More directly relevant than planar BSG to scalar A+cB reductions, after coefficient and mesh bookkeeping |
| `LabelledRealEnergyBin.exists_real_energy_preserving_bin`, `Thm_StickyKakeya4_labelled_real_energy_bin.lean:73` | A separated original A and arbitrary original labels W carrying values v; retains a whole actual value-fiber bin with original mass and integer energy | Handles collisions of the scaled values cB without identifying away the original B labels |
| `FiniteKaufmanProjection.finite_kaufman_projection`, `Thm_StickyKakeya4_finite_kaufman_projection.lean:163` | Point and slope Frostman laws with the **same** exponent t<=1; retains most slopes and most points, with a robust projected t-Frostman law | Weakening a sigma-carrier and an s-slope set to exponent s gives only s. When s<sigma/2 this falls below the required square-root exponent before any positive gain |
| `NativeOriginalPlanarCW.planar_original_CW_concentration`, `Thm_StickyKakeya4_native_original_planar_cw.lean:48` | Original four-dimensional convex-Wolff law, carrier lower counts, and actual incidence data; returns an upper concentration bound | These hypotheses are not the one-scale cap and sparse planar shading hypotheses of A.3, and the conclusion is not union expansion |
| `FinitePlaneProjectionGrid.exists_large_projected_image`, `Thm_StickyKakeya4_finite_plane_projection_selection.lean:68` | Original three-dimensional KT1 point counts and a complete explicit two-parameter projection family | Selecting from all grid projections cannot select from the prescribed sparse one-parameter slope family E |

The currently proved BSG route can therefore support a future geometric
proof, but cannot finish the regular-projection assertion just by substituting
its inputs. Small images yield energy and structured subsets; a separate
argument must contradict those subsets using simultaneous nonconcentration
in the carrier and direction sources.

One precise independent adapter still constructible from these engines is
the scalar restricted-graph BSG interface: G is an actual subset of A x B,
its actual rounded a+c*b image is small, and the output consists of literal
subsets of A and B. For c<1, cB need not remain d-separated. A valid adapter
must retain its original labels, select whole scaled-value fibers, or change
to a mesh comparable to c*d and account for the resulting covering loss.
Simply invoking the separated-source theorem at mesh d is invalid. This
adapter is additive infrastructure; proving it alone would leave the exact
deep assertion above open.

## Where the geometric gain enters the literature route

The relevant chain is OS regular projection -> ABC expansion -> its
Proposition 3.7 -> radial thin-tube improvement. The last step uses OSW
Lemma 2.8, whose proof invokes a genuine Furstenberg gain, OSW Theorem 2.7.
That theorem gives a positive power beyond the elementary double-counting
bound for thick incidences. It is not a consequence of the A.2 weak radial
graph or of asymmetric BSG already implemented here.
[OSW, pp. 9–12](https://arxiv.org/pdf/2209.00348).

The implementable next deep engine can be chosen as either the stated
robust regular-projection theorem, or a genuine finite thick-incidence gain
strong enough to prove the radial self-improvement and then ABC. Neither
was located among the current proved repository declarations. An assumed
projection lower bound, assumed low collision energy, or assumed tube-union
gain would only move the missing theorem into a premise.

## A weaker route may avoid the separate Fu–Ren input

OS Corollary 5.50 supplies the exponent

    Gamma(s,sigma) = sigma/2 + s(2-sigma)/(2(2-s)).

Its proof precedes the use of Fu–Ren. The remaining non-additive ingredients
are regular projection and the actual multiscale incidence factorization
(OS Corollary 5.37).
[OS v4, pp. 52–57](https://arxiv.org/pdf/2301.10199v4).

Here is an independent numerical comparison explaining why this weaker
route is relevant, without treating the comparison as a proved incidence
theorem. Set

    target(s,sigma) = sigma/2 + (s/4) min(sigma,2-sigma).

For 0<s<=1 and s<=sigma<2, subtraction gives

    Gamma-target = s(4-4sigma+s*sigma)/(4(2-s))  if sigma<=1,
    Gamma-target = s^2(2-sigma)/(4(2-s))          if sigma>=1.

Both are strictly positive. For 0<sigma<=s, the elementary exponent sigma
is larger than target. Thus a proof of the weaker local geometric estimate,
together with genuine multiscale factorization and controlled errors, is
enough for this proposed route. The comparison is not formalized as a new
Lean theorem because it does not discharge a geometric input.

There is also a useful exact bookkeeping observation. Normalize a
nondecreasing 2-Lipschitz branching function beta to [0,1], beta(0)=0,
beta(1)=t, and put A=1-t/2. Suppose piecewise chord slopes sigma_j are
ordered and B is an actual chord breakpoint where they cross 1. Then

    sum_j length_j min(sigma_j,2-sigma_j)
      = 2(beta(B)+A-B) >= beta(A).

For B<=A, use beta(A)<=beta(B)+2(A-B). For B>=A, the endpoint bound
beta(1)-beta(B)<=2(1-B) gives beta(B)>=2(B-A), and monotonicity gives
beta(B)>=beta(A). These two inequalities imply the claimed lower bound.
Consequently, a critical-scale lower bound beta(A)>=u would contribute
su/4 in the idealized local estimate before losses. This calculation uses
the value of the **actual** branching function at B, not an unjustified
value for a convex minorant at A. Discarded intervals, profile tolerances,
and a uniform positive choice of parameters still require an actual
multiscale proof.

## No three-dimensional shortcut

WZ's proof of Theorem 1.1 uses Proposition 6.5. Its non-affine analysis uses
Theorem 13.5, which invokes radial Theorem 13.2. Appendix A.1 proves 13.2
using A.3. Feeding WZ's resulting three-dimensional theorem back into A.3
would therefore be circular. Remark 13.3 concerns independence of a
constant from the two-ends exponent; it does not remove that dependency.
[WZ](https://arxiv.org/pdf/2609.22035).

Local source checks: `paper-audit/wang-zakharov-2609.22035.txt` lines
1342, 2657–2669, 2747, 2951–2956, 5717–5726, and 5910–5912.
The repository's final published volume estimate is still explicitly
assumed in `Thm_StickyKakeya4_cover_adapted_wang_zakharov_closure.lean`;
the volume-to-covering interface does not independently prove it.

## Integration boundary

Keep the annular endpoint and the parent's actual shading-cell selection
work as independent proved reductions. They preserve original point mass,
physical neighborhoods, and literal occupied cells. The first deep missing
result identified here remains the robust sparse-direction projection
gain, together with the configuration factorization needed to use it.
Full A.1 and A.3 are not established by this audit.
