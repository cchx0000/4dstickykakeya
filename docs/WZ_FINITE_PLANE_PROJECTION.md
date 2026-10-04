# Concrete finite spatial projection: verified checkpoint

Canonical source files and complete verification evidence are checked into this repository. External publication is tracked separately.

## Main endpoint

`FinitePlaneProjectionGrid.exists_common_separated_original_subsets` in
`FinitePlaneProjectionFinal.lean` selects one member of the explicit family

    L_(u,v)(x,y,z) = (x-u*z, y-v*z),
    u,v in {k/(n+1) : 0 <= k <= n}.

`projectionLinear` is a literal real linear map on the native nested real product;
`projectionLinear_surjective` proves that it is onto R². There are no abstract
projection, projected-distribution, or projected-energy assumptions.

Let rho > 0, let the slope mesh be at most rho, and take J with
2 <= 2^(J+1) rho. Set

    scales = {2^j rho : 0 <= j <= J+1},
    D_A = 1542 K_A |scales|,
    D_B = 1542 K_B |scales|.

The actual number of scales is at most J+2. The theorem constructs original-label
subsets S of A and T of B with the SAME projection and:

* |S| >= |A|/(18 D_A), |T| >= |B|/(18 D_B)
* Different retained labels project to actual points at native sup-norm distance
  strictly greater than 2 rho; no point is moved to a cell center
* For every center c in R² and EVERY radius R >= rho, the number of retained
  projected points in the literal native norm closed ball is <= 50 D_i R/rho
* Every normalized planar affine strip of width w contains at most
  (18 D_B theta)|T| original B representatives

Before the deterministic nine-color separation, the stronger population bound
is 1/(2 D_i), the strip fraction is 2 D_B theta, and base-cell labels are injective.
That endpoint is `exists_common_allscale_original_subsets` in
`FinitePlaneProjectionAllscale.lean`.

## Original hypotheses, explicitly

For BOTH original A and B, the theorem requires actual point-centered spatial
KT1 counts:

    #{k : dist3(p_i,p_k) <= R} <= K_i R/rho   for every R >= rho,

and original sup-norm diameter at most 2. B's coordinates lie in [-1,1].
The B anti-line input consists of original counts:

    #{j : dist3(b_i,b_j) <= r0} <= kappa |B|,
    #{k : crossSize(b_i,b_j,b_k) <= w0 dist3(b_i,b_j)} <= epsilon |B|

for original secants with distance > r0. There are no projected certificates.
The displayed scalar condition is

    3(kappa + epsilon + 128 w/(r0 w0) + 2/(n+1)) <= theta^3.

The final B-strip loss includes the reciprocal population retention factor;
it is not silently discarded.

`relative_native_ball_bound` converts the actual absolute cap and the proved
retention to a relative Frostman cap. If eta <= rho|A| is a lower ORIGINAL
population bound, the separated endpoint gives

    ball_count <= (900 D_A^2/eta) R |S|.

Without an original population lower bound, only the absolute cap is claimed.
The unseparated representative version has coefficient 100 D_A²/eta.

## Original curved graph caller

`originalCrossTube_card_of_height_affine_caps` in
`FinitePlaneProjectionOriginalGraph.lean` derives the original cross-tube premise
from exactly two kinds of original count, for any 0 < eta <= 1:

* Height interval radius w0+2 eta has fraction at most kappa_height
* The original graph deviation tube
  |b_y-a1*b_x-c1| <= w0/eta AND |b_z-a2*b_x-c2| <= w0/eta
  has fraction at most epsilon_affine for every affine graph

Then every nonzero original secant cross tube has fraction at most
max(kappa_height,epsilon_affine). Near-vertical secants give the height interval;
the other secants give the affine graph tube. No global Lipschitz property is
assumed. This is intentional: scheduled dyadic oscillation alone does not give a
global Lipschitz bound across dyadic boundaries.

For the source Lemma 21.1(167) caller, the original height-family reduction must still supply the
normalized original affine cap on the actual retained height family, including
coarse representative/fiber retention and error enlargement. A strict source
inequality must be applied with adequate width slack to imply this closed-tube
cap. This projection package does not assert that those caller facts follow
from cardinality alone.

## Whole-height-fiber transport

`FinitePlaneProjectionPerturbation.lean` proves the exact sup-norm estimate

    crossSize(p,q,s) <= crossSize(p,q,s') + 2 dist3(p,q) e

whenever dist3(s,s') <= e. `originalCrossTube_transport` is the literal original
Finset membership implication at width w+2e. It keeps the same ORIGINAL secant
endpoints and charges each original fine label; it does not thicken an affine
graph by an uncontrolled slope factor.

For physical coarse height-bin width sigma with normalized representative
error e=sigma/rho_physical, the correct fine original tube width is w+2e. Thus
the preceding curved-graph bridge must be applied at height radius
w+2e+2eta and affine graph width (w+2e)/eta. Coarse/fine population transfer remains
the whole-fiber counting theorem for the actual height family.

## Proof path and constants

The finite slope grid has pair collision probability <=64 r²/d∞². Original KT1
ball caps summed over geometric annuli give averaged collision energy
<=257 K |A| at base scale, with no annular logarithm. At each larger scale r the
bound is <=257 K(r/rho)|A|.

Summing energies weighted by rho/r over the finite dyadic scale set introduces
only its cardinality. Three simultaneous finite average bounds select one
parameter for A energy, B energy, and B projected small triangles. Removing all
heavy cells at every scale leaves at least half the original labels. One actual
label per surviving base cell gives population 1/(2D), and 25 neighboring cells
plus dyadic radius comparison give the all-radius cap 50D R/rho. A fixed nine-color
partition of the integer cells gives actual >2rho separation.

For original B triples, the cross-tube and close-pair exclusions bound the number
of degenerate original triples by (kappa+epsilon)|B|³. Nondegenerate triangles
have projected small-area probability <=8r/A+2 mesh. Three points in a projected
strip have area <=16w; taking the cube root and transferring to the actual
retained family gives the claimed line fraction.

## Verification

All 105 public theorem and lemma declarations have strict source checks and
a fresh combined imported axiom audit. The
[readback](../verification/WZFiniteProjectionReadback.lean),
[axiom log](../verification/wz-finite-projection-axioms.log), and
[checkpoint](../verification/wz-finite-projection-checkpoint.json) record the
canonical source hashes and full build. Definitions are not counted as proofs.

## Graph-retention boundary

The population endpoint alone does not preserve an arbitrary sparse incidence graph: independent vertex thinning may remove its edges. The Section21 graph caller therefore additionally needs density-dependent heavy-cell thresholds, edge-mass pruning, and graph-weighted quotient/color selection. Those are not assumed or claimed by this checkpoint.
