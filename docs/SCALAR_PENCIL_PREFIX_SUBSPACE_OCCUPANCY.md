# Scalar-pencil prefix occupancy in every subspace

Date: 2026-10-03. **Handwritten mathematical proof and independent audit.**
The full prefix-occupancy statement is not a Lean theorem. Its exact
polynomial sublevel-measure input is now independently formalized in
`Theorems/Thm_StickyKakeya4_polynomial_sublevel_measure.lean` (four strict
standard-only declarations). The remaining elementary counting below does
not invoke an inverse theorem or assert a scale-transfer principle for
arbitrary Borel maps.

## 1. Exact elementary setting and conclusion

Fix an integer `B >= 2`. For every integer `n >= 1`, let

    A_n = B^(-n) {0,1,...,B^n-1}^3.

Let `g_n : A_n -> R^3` be arbitrary maps satisfying

    sup_n sup_(a in A_n) |g_n(a)| <= M < infinity,

where the norm here and below is Euclidean. No compatibility between different
`g_n` is required. Put

    Y_(n,a)(t) = t a + g_n(a),
    nu_(t,n) = B^(-3n) sum_(a in A_n) delta_(Y_(n,a)(t)).

The measure counts source labels with their multiplicities: coincident output
points retain the sum of their source masses.

**Occupancy lemma.** There is a Lebesgue-null set `E subset R` such that, for
each `t outside E`, there is `N(t)` for which the following holds for every
`n >= N(t)`, simultaneously for `k=1,2,3` and every rank-`k` orthogonal
projection `pi : R^3 -> V`:

    (pi nu_(t,n))(Q) <= B^(-kn)

for every cube `Q` in `V` of side `B^(-43n)`. The cube may use any orthonormal
coordinates on `V`, with any translation. In particular the projection and
the cube may depend on `t` and `n`.

Consequently, for every real `p>1`, any partition of `V` into half-open cubes
of that side length satisfies

    sum_Q (pi nu_(t,n))(Q)^p <= B^(-kn(p-1)).          (1)

The same assertions hold for smaller cubes. The exceptional set and the
threshold `N(t)` are independent of `k`, `pi`, the cube partition, and `p`.

## 2. Polynomial sublevel estimate

If a real polynomial `P` has degree exactly `ell >= 1`, leading coefficient
`c != 0`, and `epsilon > 0`, then

    Leb{t in R : |P(t)| < epsilon}
       <= 2 ell (epsilon / |c|)^(1/ell).             (2)

Indeed, factor over the complex numbers as

    P(t) = c product_(j=1)^ell (t-z_j).

If the product of the `ell` distances is less than `epsilon/|c|`, at least
one distance is less than `(epsilon/|c|)^(1/ell)`. A real `t` in that disk
lies in the real interval with that radius centered at `Re(z_j)`. The union
of these `ell` intervals has the stated length. In particular, (2) is global
in `t`; it does not require bounds on the lower polynomial coefficients.

## 3. Simultaneous noncollapse of source-independent tuples

Fix `ell in {1,2,3}` and an ordered tuple

    (a_0,a_1,...,a_ell) in A_n^(ell+1)

whose input differences `u_j=a_j-a_0` are linearly independent. Some
`ell x ell` coordinate minor of the `3 x ell` matrix with columns `u_j`
is nonzero. Choose one such minor once for this tuple. Since its entries
are integer multiples of `B^(-n)`, its determinant has magnitude at least
`B^(-ell n)`.

Apply the same coordinate minor to the output differences

    v_j(t) = Y_(n,a_j)(t)-Y_(n,a_0)(t)
           = t u_j + g_n(a_j)-g_n(a_0).

Its determinant `P(t)` is a polynomial of degree exactly `ell`. Its leading
coefficient is the chosen input determinant, and hence has magnitude at
least `B^(-ell n)`. The corresponding coordinate of the exterior product
`v_1(t) wedge ... wedge v_ell(t)` equals `P(t)`.

Thus the set of times for which this exterior product has norm less than
`B^(-42n)` has length at most

    2 ell B^(n(1-42/ell)).                           (3)

There are at most

    |A_n|^(ell+1) = B^(3n(ell+1))

ordered tuples; restricting to the source-independent ones only reduces
the count. Summing (3) over tuples and then over `ell=1,2,3` gives the
following upper bound for the measure of the level-`n` bad-time set:

    2 B^(-35n) + 4 B^(-11n) + 6 B^(-n).             (4)

This is summable in `n`. The Borel-Cantelli lemma therefore gives a null
set `E` such that, for every `t outside E` and every sufficiently large
`n`, all three of the following assertions hold simultaneously:

    |v_1(t) wedge ... wedge v_ell(t)| >= B^(-42n)     (5)

for every `ell=1,2,3` and every tuple whose `ell` input differences are
linearly independent. No projection or normal has been fixed in this step.

## 4. A projected fine cube forces exact source rank deficiency

Fix `t outside E`, an integer `k in {1,2,3}`, a rank-`k` orthogonal
projection `pi`, and a cube `Q subset V` of side

    r_n = B^(-43n).

Let

    S = {a in A_n : pi Y_(n,a)(t) in Q},
    ell = 4-k.

The kernel `K=ker(pi)` has dimension `3-k=ell-1`. Suppose `S` contains
`ell+1` input points `a_0,...,a_ell` with linearly independent differences.
For their output differences write orthogonally

    v_j = z_j+w_j,  z_j in K,  w_j=pi v_j in V.

Because all projected points lie in the same cube,

    |w_j| <= sqrt(k) r_n <= sqrt(3) r_n.

Also every output difference satisfies

    |v_j| <= L_t := sqrt(3)|t|+2M,

and hence `|z_j| <= L_t`. Since `dim K=ell-1`, the all-`z` term in the
exterior-product expansion vanishes. Every remaining term contains at
least one `w_j`. The triangle inequality and the standard exterior-product
norm bound give, using `r_n<=1`,

    |v_1 wedge ... wedge v_ell|
      <= (L_t+sqrt(3)r_n)^ell - L_t^ell
      <= ell sqrt(3)(L_t+sqrt(3))^(ell-1) r_n
      <= C_t B^(-43n),

where one may take

    C_t = 3 sqrt(3)(L_t+sqrt(3))^2.

For all sufficiently large `n`, uniformly in `k`, `pi`, and `Q`, this is
strictly less than `B^(-42n)`. It contradicts (5). Thus `S` contains no
`ell+1` points with affine input rank `ell`; equivalently,

    dim aff(S) <= ell-1 = 3-k.                       (6)

The equivalence follows simply by choosing a maximal affine-independent
subset of `S` (and is harmless if `S` is empty).

## 5. Exact lattice cardinality and the moment estimate

An affine subspace `H subset R^3` of dimension `m` has some projection onto
`m` of the three standard coordinate axes that is injective on `H`. To see
this, choose a basis matrix for its direction space and a nonzero `m x m`
coordinate minor. For `m=0`, the subspace is a single point.

Each chosen coordinate of a point in `A_n` has only `B^n` possibilities.
Therefore

    |H intersect A_n| <= B^(mn).                    (7)

Applying this with `H=aff(S)` and (6) yields

    |S| <= B^((3-k)n).

Since each source label has weight `B^(-3n)`, the asserted cube-mass bound
follows exactly, including any output coincidences. Finally, the masses
of all cells of a partition sum to one, so

    sum_Q mass(Q)^p
      <= (sup_Q mass(Q))^(p-1) sum_Q mass(Q)
      <= B^(-kn(p-1)).

This proves (1) and the occupancy lemma with all its quantifiers.

## 6. Scope: the elementary bound is not a nonstationary scale transfer

The proof permits arbitrary uniformly bounded `g_n`, including unrelated
choices at different levels. It controls the **finite prefix measures** at
the much finer scale `B^(-43n)`.

It does not, by itself, give full dimension `k` for a limiting measure at
its natural scale `B^(-n)`. Directly dividing (1) by the logarithm of the
fine scale would give only the exponent `k/43`. Passing instead to a
full exponent `k` requires an additional justified scale-transfer result.
In a stationary self-similar model, Corso-Shmerkin Proposition 3.8 is a
candidate for exactly that separate step, under its actual unsaturation
hypothesis. This note does not assume that hypothesis for a general
nonstationary sequence or arbitrary Borel selector.

For the intended stationary model, let each level independently choose
`d in {0,...,B-1}^3` uniformly and set

    A = sum_(j>=1) B^(-j) d_j,
    F = sum_(j>=1) B^(-j) h(d_j)

for a fixed finite digit map `h:{0,...,B-1}^3 -> R^3`. The `n`-prefix of
`A` is a bijective labeling by `A_n`, and its corresponding output prefix
defines a bounded `g_n` of the kind used above. The coordinatewise cyclic
digit model is one special choice of `h`; independence among its three
output coordinates is unnecessary for the elementary occupancy lemma.

## 7. Separate elementary result: full-output prefix exponential separation

This simpler statement also holds for the arbitrary bounded prefix maps
of Section 1 (boundedness is not needed for the separation estimate itself).
For distinct `a,a' in A_n`, at least one coordinate of `a-a'` has magnitude
at least `B^(-n)`. The corresponding coordinate of

    Y_(n,a)(t)-Y_(n,a')(t)

is affine in `t` with slope magnitude at least `B^(-n)`. Hence the set on
which the output difference has sup norm less than `exp(-Cn)` has length
at most `2 B^n exp(-Cn)`. There are at most `B^(6n)` ordered pairs, so the
total bad-time length is at most

    2 B^(7n) exp(-Cn).

For any fixed `C>7 log B`, this is summable. Thus, for almost every `t`, all
distinct source-prefix labels have output separation at least `exp(-Cn)`
for every sufficiently large `n`. This counts symbols with multiplicity,
rather than discarding coincident symbols before checking separation.

For stationary digit coding there is no hidden input-carry problem: a finite
word in the full alphabet `{0,...,B-1}` corresponds uniquely to an integer
between `0` and `B^n-1`. Infinite base-`B` expansion ambiguity occurs only
at the usual countable set of endpoints in each scalar coordinate, hence
on a null subset of the uniform input measure. The output translations are
real finite sums, not a chosen canonical digit expansion; output carries
do not alter any of the affine difference identities above.

## 8. Separate rational-digit scalar strengthening

Let `eta:{0,...,B-1}->Q` be a rational digit map. Choose an integer `Q>=1`
such that `eta(d)=m_d/Q` with all `m_d` integers. Define the scalar graph
coding by independent uniform input digits:

    A = sum_(j>=1) d_j B^(-j),
    F = sum_(j>=1) eta(d_j) B^(-j).

For a real scalar slope `s`, let `Delta_n(s)` be the minimum absolute
difference between `s A_n+F_n` for distinct input words of length `n`,
retaining word labels. Every such difference has the exact form

    B^(-n)(s p + l/Q),

where `p,l` are integers and `1<=|p|<B^n`. In particular, if `s` is
irrational, no two finite word translations coincide.

**Claim.** For every irrational `s`,

    Delta_n(s) >= B^(-4n)

for infinitely many `n`.

Otherwise for all sufficiently large `n` choose a witnessing pair with
`Delta_n(s)<B^(-4n)` and write

    r_n = -l_n/(Q p_n).

Then

    |s-r_n| < B^(-3n)/|p_n| <= B^(-3n).

If `r_n` and `r_(n+1)` are distinct, their integer numerators give

    |r_n-r_(n+1)| >= 1/(Q |p_n p_(n+1)|)
                     > 1/(Q B^(2n+1)).

But their distances to `s` bound the same difference above by
`B^(-3n)+B^(-3(n+1))`. For sufficiently large `n` this is smaller than the
displayed lower bound. Hence `r_n` is eventually constant; taking the limit
would make `s` rational, a contradiction. This proves the claim.

The conclusion is **subsequence exponential separation**, not an assertion
of all-level exponential separation for every irrational `s`.

If `s` is rational and has no exact word overlap, the same lattice formula
gives exponential separation at every level after absorbing the fixed
denominator. Therefore failure of subsequence exponential separation in
this rational-digit scalar family can occur only at a rational slope
having an exact finite-word overlap. This is a countable set.

## 9. Scalar Lp consequence and the cyclic bad-slope product

The following consequence uses a primary external theorem; it is distinct
from the elementary proofs above. Corso-Shmerkin, *Dynamical self-similarity,
Lq-dimensions and Furstenberg slicing in R^d*, Definition 1.8 and Theorem 1.9:

https://arxiv.org/html/2409.04608v1

For the rational-digit scalar family and irrational `s`, its one-point-base
stationary model has ratio `1/B`, `B` distinct first-level translations,
uniform weights `1/B`, and the subsequence separation just proved. Fix
`p>1`. If its Lp dimension were less than one, the theorem's line-unsaturation
condition in dimension one would hold, since the zero-dimensional
projection has dimension zero. The theorem would then give Lp dimension

    log(B^(1-p)) / ((p-1) log(1/B)) = 1,

a contradiction. Thus its Lp dimension is one for every `p>1`. This invokes
an Lp theorem directly, not an inference from Hausdorff dimension. Existence
of the Lp limit for a stationary one-point-base model is also covered by
Lemma 1.5 of the same paper.

Now take three independent scalar graph codings `(A_i,F_i(A_i))` of this
rational-digit kind and use cyclic indices modulo three, writing the actual
cyclic output as

    X_t = sum_(i=1)^3 [t A_i e_i + F_i(A_i) e_(i-1)].

For any nonzero normal `v=(v_1,v_2,v_3)`,

    v dot X_t = sum_i [t v_i A_i + v_(i-1) F_i(A_i)].

If all coordinates of `v` are nonzero, define

    s_i = t v_i / v_(i-1).

Their product is exactly `t^3`. If `t^3` is irrational, at least one `s_i`
is irrational. That independent summand has full scalar Lp dimension one;
convolution with the other independent summands cannot decrease its Lp
dimension. This last assertion follows from convexity of the grid moment
under translation mixtures and the constant-factor comparison between
translated interval grids.

If some coordinates of `v` vanish, cyclicity of the nonempty proper support
of `v` gives an index `i` with `v_i != 0` and `v_(i-1)=0`. The corresponding
summand is just `t v_i A_i`, a uniform interval law for `t!=0`; the full
scalar convolution consequently has bounded density.

Therefore, for every `t` with `t^3` irrational, **all** nonzero scalar
projections of this rational-digit cyclic law have Lp dimension one for
every `p>1`. The normals may depend on `t`. This scalar conclusion alone
does not imply that every plane projection has dimension two. The uniform
occupancy lemma in Sections 1-5 supplies a different potential route to
the plane question, subject to the separate justified scale-transfer step.
