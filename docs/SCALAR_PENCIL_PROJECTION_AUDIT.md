# Scalar-pencil projection audit and a low-moment endpoint

Date: 2026-10-02. Status: primary-source and handwritten mathematical audit.
Nothing in this note is a new Lean axiom, a proved geometric closing estimate,
or a change to the original main theorem. The original compact marked front
remains the support required for every escape. This note complements
`ROOTED_TIME_RECURRENCE_FRONTIER.md`.

## 1. The actual projection problem

Normalize one fixed positive source once, so that `sigma` is a probability,
`sigma <= D volume`, its slopes are bounded, and

    mu = (a -> (a,b(a)))_# sigma,
    Q(a,b) = a,
    P_t(a,b) = b+t a,
    mu_t = (P_t)_# mu.

The source and intercept do not change with scale. A positive-length interval
`J` is contained in the common marked slab. A packing pretrim gives upper
phase covering exponent `3+zeta` and can give the local reference-mass bounds
already recorded in the project.

The actual front deficit forces full source-time limsup of

    E_r(beta) = {(a,t): mu_t(B(P_t(a,b(a)),r)) >= r^beta},
    beta < 3.

The root probability `P_r(beta)=(sigma x dt)(E_r(beta))` is the quantity which
must be paid. A theorem only about cardinalities of newly selected supports
must still be transferred to this probability with its original weights.

## 2. Exact linear algebra: why the generic projection theorem stops short

For a linear subspace `W <= R^3_a x R^3_b`, put

    k = dim W,    R(W) = generic rank(P_t restricted to W).

The generic rank is attained away from finitely many roots of nonzero minors.
For two distinct generic parameters `s,t`, the map

    w -> (P_s(w),P_t(w))

is injective: its two outputs recover `a` by subtraction and then `b`.
Consequently `k <= 2 R(W)` and

    R(W) >= ceil(k/2).                                   (2.1)

This is sharp. For `k=2j` take `W=U x U` with `dim U=j`; for `k=2j+1`
add one horizontal coordinate outside `U`. The generic image dimensions are
respectively `j` and `j+1`. In particular the unrestricted three-dimensional
input profile is only two.

There is a stronger observation for horizontally nondegenerate planes.
If `dim W=3` and `Q|W` has rank three, write `W={(a,La)}`. Then

    det(P_t|W) = det(L+t I)

in horizontal coordinates. This is a monic cubic, so it is not identically
zero. More generally `R(W) >= rank(Q|W)` by taking a nonzero maximal minor of
the horizontal matrix as the leading coefficient of the corresponding pencil
minor. Thus every fixed plane on which the pencil generically has rank less
than three also has horizontal rank less than three.

These elementary assertions agree with the scalar-block example immediately
after Conjecture 1.6 in [Du, Restricted Marstrand's projection theorem for
general families of linear subspaces](https://arxiv.org/html/2510.16671v1#S1).
That paper's Theorem 1.7 concerns polynomial families of two-planes in four
space satisfying maximal generic rank on **every** input subspace. It yields
an improvement above one, not a full-dimensional theorem for this six-to-three
pencil. The present pencil fails its all-subspace condition already on the
three-plane used below.

### The fixed Schubert obstruction

The row space of `P_t` is

    V_t = {(t u,u):u in R^3}.

Let

    W_0 = span{(e1,0),(0,e1),(e2,0)}.

Then `(t e1,e1)` is a nonzero vector in `V_t intersect W_0` for **every** t.
Therefore the entire parameter distribution lies in one proper Schubert
cycle. Restricting to any positive-measure set of times does not remove this
obstruction.

[He, Orthogonal projections of discretized sets, Theorem 1, assumption (3)](https://arxiv.org/html/1710.00795v2#S1.SS1)
requires the projector distribution to assign at most
`delta^(-epsilon) rho^kappa` mass to every complementary-plane Schubert
neighborhood. Here the mass of the neighborhood of `W_0` is one at every
radius. He’s analytic-family Corollary 5 likewise requires escape from each
such cycle. The theorem therefore cannot be invoked directly. Even its
six-to-three numerical conclusion is a gain above half the input exponent,
not the desired exponent three.

The sum-product input appearing in the same paper, Theorem 8, also requires
the matrix family to move every proper invariant subspace quantitatively.
The matrices `t I` preserve every subspace, so this hypothesis does not become
valid merely by writing the pencil as a family of scalar dilations.

## 3. What horizontal density really excludes

The actual source has more structure than an arbitrary dimension-three phase
set. If `W` is any affine subspace whose horizontal projection has dimension
`d`, bounded slope support and horizontal density give

    mu(N_r(W)) <= C D r^(3-d),        0<r<1.              (3.1)

Indeed the horizontal projection of `N_r(W)` is inside the r-neighborhood of
the affine d-plane `Q(W)`; intersecting with the bounded slope ball has
three-volume at most `C r^(3-d)`. This proof does not use phase packing.

There is a useful local version. If `C_R` is a phase ball of radius R with

    mu(C_R) >= c R^(3+zeta),

then for `r<=R`,

    mu(C_R intersect N_r(W))/mu(C_R)
       <= C (D/c) (r/R)^(3-d) R^(-zeta).                 (3.2)

The numerator is at most `C D r^(3-d) R^d` by projecting `C_R` first.
Thus genuine concentration of this **same normalized reference component**
near a plane with `d<3` is excluded whenever the right side is small.
This is stronger than an unlocalized plane bound and does not divide by an
old occurrence success probability.

But it does not apply uniformly to arbitrary conditional heavy-bush laws.
For a bush B of source mass m, the unconditional bound supplies only

    (mu restricted to B)(N_r(W))/m <= C D r^(3-d)/m.      (3.3)

At the available lower bound `m>=r^beta`, this can be vacuous. Replacing B by
a reference component in (3.2) would change the conditional law unless an
actual comparison is proved.

Nor can one sum (3.1) over freely changing plane labels without a ledger.
For example, take `b=0` and uniform slopes in `[0,1]^3`. Translates of the
fixed plane `W_0` at `a3=j r` have individual r-neighborhood mass `O(r)`, but
`O(r^(-1))` of them cover the entire source. This is one fixed, minimally
packed phase graph. It is a countertest to a free union bound, not to the
front theorem; its front has dimension four.

Because (3.1), the phase-ball upper bound `mu(B_r)<=C D r^3`, and graphness
all follow from an arbitrary bounded-density slope selector, a purported
full-three-dimensional projection theorem using **only** these inputs would
already give the ordinary four-dimensional Kakeya dimension conclusion.
Any shortcut peculiar to the sticky problem must use the minimal upper
packing/entropy assumption in an essential additional step.

## 4. A genuinely weaker projector hypothesis exists, but its exponent is too low

[Bénard–He, Effective equidistribution of random walks on simple homogeneous
spaces, Theorem 4.1](https://arxiv.org/html/2511.13512v3#S4)
replaces avoidance of all Schubert cycles by quantitative avoidance of
constraining pencils: neighborhoods where some input subspace W projects to
less than `(k/d) dim W`. Its exceptional-set conclusion is

    N_delta(pi_L A') >= rho^D N_delta(A)^(k/d)

for sufficiently large subsets outside a small set of projectors, with
explicit restrictions on `rho,delta,epsilon,kappa,D`. This is a real
relaxation of He’s hypothesis. For ambient dimension six and output dimension
three, however, its retained exponent is one half. It does not use (3.1) to
upgrade that exponent to three. Section 1.2 explicitly distinguishes this
subcritical result from a general supercritical theorem.

Thus this newer result prevents the overstatement that *every* usable
projection theorem needs full Schubert escape. It does not provide the
source-sensitive full-dimensional conclusion required here. No iteration
from its one-half exponent to three has been proved for the actual source.

## 5. What the convolution inverse theorem does and does not produce

[Shmerkin, Inverse theorems for discretized sums and Lq norms of convolutions
in Rd, Theorem 1.2](https://arxiv.org/html/2308.09846v3#S1)
starts from `||lambda*nu||_q >= 2^(-epsilon m)||lambda||_q` for independent
convolution, `m=SL`. For each tolerance delta one first chooses a sufficiently
large block length L, then epsilon depending on L, and finally sufficiently
large S. It selects regular subsets with losses `2^(-delta m)`. The first
factor has local saturation; the second has local concentration on
`k_s`-planes. These planes may depend on the local cube. Remark 1.4 does not
assert a uniform identification of their orientations.

The same paper's Theorem 3.3 gives a related unconditional fact: components
of a measure concentrate on certain subspaces while components of a fixed
convolution power saturate those subspaces. The convolution order depends on
the tolerance and block length.

For the actual phase law the following two missing inputs are distinct:

1. Same-source `b(A)+t A` is not the independent convolution
   `law(b(A))*law(t A)`. For `b(a)=-t0 a`, the former is a point mass at
   `t=t0`, while the latter is a full-dimensional convolution when `t0!=0`.
   A convolution hypothesis cannot be read off from heaviness of the former
   by replacing the correlated pair with its marginals.
2. Applying the unconditional convolution-power statement in phase space
   does not keep its saturated measure on the original graph. Estimate (3.2)
   may exclude low horizontal rank for a genuinely concentrated original
   component, but the convolution power can spread into dimension above
   three. Packing dimension three of `supp mu` does not bound the packing
   dimension or entropy of `supp(mu^{*k})` by three. For an explicit
   smooth example, let `b(a)=(a1^2,a2^2,a3^2)` on a cube. The sum map
   `(a,a') -> (a+a',b(a)+b(a'))` has nonzero six-dimensional Jacobian
   wherever each `ai!=ai'`: each coordinate block has determinant
   `2(ai'-ai)`. Thus the self-convolution has a full six-dimensional
   portion even though the original phase graph is smooth and dimension
   three.

Hence this inverse theorem does contain a concentration output of the type
that (3.2) could use, but the necessary small-growth/correlation transfer has
not been derived from the original source and the actual heavy root-times.
Its retained-mass losses and parameter order would also have to be paid
before applying it at every fine scale.

A two-projection BSG attempt has an explicit numerical problem. After a
regularization in which the phase set has order `r^(-3)` cells and its two
separated physical projections each have order `r^(-beta)` cells, its image
is a subset of their Cartesian product of density only

    r^(-3) / r^(-2 beta) = r^(2 beta-3).

Near beta three this is a polynomially small density. A generic polynomial
loss in that density is therefore a power of the physical scale, not a
subpower or logarithmic loss. Such an extraction does not preserve the
root-time mass required by the recurrence argument. This computation is
conditional on that regularized configuration; heaviness alone is not being
used to assert a global projection-cover bound.

A macroscopic block can legitimately turn actual saturation involving a
vertical direction into a linear vertical entropy cost. But it helps only
after a source-faithful inverse output with controlled retained source and
time mass. It does not manufacture the independent-convolution hypothesis,
and no such output has been obtained here.

## 6. Average entropy alone is weaker than the required local conclusion

Even proving

    H_n(mu_t)/n -> 3

for almost every t would not by itself establish lower local dimension three,
a supported Frostman measure, or summability of the heavy events. Global
entropy can miss small moving exceptional pieces which recur at almost every
point. Local entropy averages could be useful, but need their genuine
pointwise conclusions with source/time exceptional sets controlled.

For an explicit measure-theoretic warning, form an independent sequence of
binary blocks of lengths `L_j` with `L_j/(L_1+...+L_(j-1)) -> infinity`.
For each `j>=2`, choose the all-zero block with probability `1/j`; otherwise
choose a uniform binary block. At every precision the Shannon entropy divided
by the number of bits tends to one: the entropy deficit in block j is at most
`L_j/j+1`, and the same estimate applies to any initial part of that block.
But almost every sequence chooses infinitely many of the special zero blocks.
At their endpoints, the cylinder mass is at least a polynomial-in-j factor
times `2^(-(L_1+...+L_(j-1)))`. Thus lower local dimension is zero.
The same construction using uniform `3 L_j`-bit good blocks,
grouped into three spatial coordinates and sharing one bad-block decision,
has entropy dimension three and lower local dimension zero. This is an
abstract measure countertest to the entropy implication,
not a claimed counterexample with all of the sticky-front hypotheses.

## 7. A lower-moment sufficient endpoint, with the actual root weights

There is a source-faithful sufficient target weaker than the quadratic energy
route. Fix `0<theta<1/3` and let `Q_r` be a cubic grid in spatial three-space,
with cube side r. Write

    p_Q(t) = mu_t(Q),
    S_r(theta) = integral_J sum_Q p_Q(t)^(1+theta) dt.

A bound

    S_r(theta) <= C r^((3-eta)theta)                     (7.1)

for some `eta<3-beta` gives a summable charge for `E_r(beta)`.
Here (7.1) is a target, not a theorem asserted from packing.

To verify the implication, for each cube Q let `s_Q(t)` be the sum of the
masses of its bounded number M of neighboring cubes, enough to contain every
radius-r ball centered in Q. Every heavy center in Q has `s_Q>=r^beta`.
Therefore

    P_r(beta)
       <= r^(-beta theta) integral_J sum_Q p_Q s_Q^theta dt
       <= M^theta r^(-beta theta) S_r(theta)
       <= C M^theta r^((3-beta-eta)theta).               (7.2)

The middle inequality follows from Holder on the sequence of cube masses and
`||s||_(1+theta) <= M ||p||_(1+theta)`. All cubes are in one fixed physical
spatial grid; no source or time is resampled. The positive exponent makes
(7.2) summable along dyadic r and contradicts the verified full limsup.
Fixed radius conventions only change M and fixed constants.

### Why the range theta below one third is natural

For the radial test `b(a)=-t0 a`, uniform slopes in a cube give

    sum_Q p_Q(t)^(1+theta)
       <= C min{1,(r/|t-t0|)^(3 theta)}.

If `3 theta<1`, integrating over a bounded interval yields
`S_r(theta)<=C_theta r^(3 theta)`. Thus (7.1) holds in this model even with
eta zero. At the quadratic value theta one, an interval containing t0 instead
has a moment of order r, rather than r cubed. The low-moment endpoint can
therefore handle a genuine supported-front escape configuration that the
unconditional quadratic residual estimate cannot handle.

An individual-bush estimate cannot simply be summed over the constructed
source-disjoint family. If there are N components and `p_Q=sum_j p_(j,Q)`,
convexity gives only

    sum_Q p_Q^(1+theta)
       <= N^theta sum_j sum_Q p_(j,Q)^(1+theta).

Source disjointness does not make the projected spatial supports disjoint.
The verified count can be as large as a constant times `1/(r M)` for old
graph mass M. Near the target regime `M` of order `r^2`, the factor `N^theta`
can cancel the entire `r^(3 theta)` gain. A target/time overlap or correlated
decoupling estimate is therefore still needed for this summation; no such
estimate is asserted here.

What remains is to prove (7.1), or another estimate implying (7.2), from the
fixed sticky source. Neither the projector results nor the convolution
inverse theorem checked above currently supplies it. In particular, the
rank calculation and anisotropic plane bounds do not constitute that proof.
The original final theorem and its unchanged project-axiom dependency remain
exactly as recorded by the verification gate.
