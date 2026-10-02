# Correlated entropy, phase-sceneries, and a triangular escape

Date: 2026-10-02. Status: handwritten proof-repair audit. No Lean theorem or
axiom is added, and the original final theorem is unchanged. The two elementary
results below are a concrete obstruction to one repair strategy and a genuine
supported-front escape for a coupled class. They do not close the general
rank-loss/root-time branch.

## 1. The local entropy ledger has a release term

Use base-two Shannon entropy. Let A_n and B_n be the level-n dyadic labels of
the horizontal slope and intercept, respectively, and put C_n=(A_n,B_n) and
V_n=H(B_n|A_n). Refinement of both partitions gives the exact identity

    H(B_(n+m) | A_(n+m), C_n)
      = V_(n+m)-V_n + I(A_(n+m); B_n | A_n).             (1)

Indeed, the chain rule first gives

    V_(n+m)
      = H(B_n | A_(n+m))
        + H(B_(n+m) | A_(n+m), B_n),

and H(B_n|A_(n+m))=V_n-I(A_(n+m);B_n|A_n). The additional A_n in C_n
is redundant after conditioning on A_(n+m).

The last term in (1) records future horizontal digits already revealed by the
old vertical label. It is nonnegative and can have order m at essentially
every scale, even if V_n=o(n). Thus a sum of the left side cannot be paid
only by V_N or the packing excess. Even the elementary map b(x)={2x} has
V_n=1 and one bit of both vertical innovation and horizontal release per step.

There is a valid macroscopic estimate. For sigma a probability on a bounded
slope cube with sigma<=D Lebesgue, H(A_(n+m))>=(3(n+m)-log_2 D), whereas
H(A_n)<=3n+O(1). Hence

    H(A_(n+m) | A_n,B_n) >= 3m-V_n-O_D(1).               (2)

Blocks m comparable to epsilon n can therefore see almost full horizontal
entropy when V_n=o(n). This repairs the scale mismatch in the bookkeeping,
but does not prove any scalar-pencil projection/inverse estimate for those
blocks. In particular (2) is an averaged entropy statement, not a uniform
Frostman bound for normalized descendants.

## 2. A sticky source whose phase-sceneries lie in a bad pencil plane

This is an off-diagonal variant of the already-audited sparse digit deletion
example. Set

    n_i=i+ceil(sqrt(i)),
    f(x)=sum_(i>=1) 2^(-i) epsilon_(n_i)(x),

using terminating binary expansions at dyadic rationals. Let a be uniform on
[0,1)^3 and use

    b(a)=(f(a_3),0,0).                                  (3)

The closure G of this graph is compact. Write

    k_N=#{i:n_i<=N},    d_N=N-k_N=O(sqrt(N)).

A horizontal N-cell fixes the first k_N output digits, leaving at most
2^(d_N) possible vertical N-cells. Therefore

    N_(2^-N)(G) <= C 2^(3N+d_N).

The use of closed grid boxes covers the closure as well. G has upper box and
packing dimension exactly three, because its horizontal projection is the
whole cube. Every source subset inherits the same vertical support bound,
which is C_zeta r^(-zeta) for every fixed zeta>0. The same finite independent
bit count gives

    H(C_N)=3N+d_N,    H(A_N)=3N,    V_N=d_N.              (4)

### What a fixed-size phase block sees

Fix m. For all sufficiently large n, n_n>=n+m. Apart from a density-zero
set of n, every position n+1,...,n+m is retained, meaning it belongs to
{n_i}. The exceptional count among n<=N is at most O(m sqrt(N))+O_m(1).
For a nonexceptional n, the phase label C_n fixes the first n bits of a_3
and the first n output bits f(a_3). The latter disclose all retained input
bits up through n_n. Consequently C_n already determines the first n+m
bits of a_3.

On the other hand, the next m bits of f(a_3) are fresh independent fair bits,
and a_1,a_2 remain independent uniform variables inside their horizontal
n-cells. Thus, for these n, exactly

    H(A_(n+m) | C_n)=2m,
    H(C_(n+m) | C_n)=3m,
    H(B_(n+m) | A_(n+m),C_n)=m,
    I(A_(n+m);B_n|A_n)=m.                              (5)

Here d_(n+m)=d_n, so (5) also directly checks (1).

After rescaling a phase n-cell to unit size, its a_3-coordinate has diameter
at most 2^(-m), while its a_1,a_2,b_1 marginals jointly have exactly uniform
product law. Since the good-scale statement holds for every fixed m with
density tending to one, the limiting phase-component distributions are
supported on translates of Lebesgue measure on

    W=span{(e_1,0),(e_2,0),(0,e_1)}.                    (6)

Centered versions are on the corresponding plane through the origin. Both
the horizontal projection Q and every scalar projection P_t have rank at
most two on W; for t!=0, rank P_t|W=2, and at t=0 its rank is one. The full
scalar pencil therefore sees an actual low-rank tangent plane, not merely
an unrelated hypothetical Schubert cycle.

This is stable under every fixed positive source restriction. If E is the
retained source, p_n=E[1_E|C_n] tends to 1 at almost every source point of E,
since C_n refines A_n and these partitions generate the source sigma-algebra.
Within such a phase cell, the total variation distance between the original
conditional law and its further normalized E-restriction is 1-p_n. It tends
to zero. Thus a fixed packing/reference pretrim cannot restore missing
horizontal dimensions in these fixed-size sceneries.

### The actual projections nevertheless have dimension three

For t!=0,

    P_t(a)=(t a_1+f(a_3), t a_2, t a_3).

This is a triangular Borel shear followed by dilation. Sequential Fubini
integration, first in a_1, then a_2, then a_3, gives

    (P_t)_# sigma <= |t|^(-3) Lebesgue.                  (7)

No differentiability or Lipschitz property of f is used. Every positive time
subinterval separated from zero yields an actual four-dimensional bounded-
density front measure. The usual bounded-chart marked-segment construction
from SPARSE_DIGIT_DELETION_TEST.md applies without change, so this is a literal
compact marked patch with a supported 4-Frostman escape.

Equations (6)-(7) show a full dimension of strict inequality in the CP
projection lower bound: typical ordinary phase tangents have scalar-pencil
image dimension two, while every nonzero-time original projection has
dimension three. A proof based only on these isotropic phase tangents misses
the delayed horizontal information which the actual shear preserves.

## 3. A genuine coupled triangular escape and the low moment

Here is a larger elementary class, stated for an arbitrary probability source
sigma<=D Lebesgue with bounded support. Suppose in one fixed coordinate frame

    b_1(a)=c_1-tau_1 a_1+g_1(a_2,a_3),
    b_2(a)=c_2-tau_2 a_2+g_2(a_3),
    b_3(a)=c_3-tau_3 a_3,                               (8)

where the g_i are arbitrary bounded Borel functions and the tau_i are fixed
real numbers. Extend the g_i measurably outside the source cube if needed.
Whenever t differs from the three tau_i, sequential Fubini on all of R^3
proves

    (P_t)_# sigma <= D product_(i=1)^3 |t-tau_i|^(-1)
                         times Lebesgue.               (9)

One may verify (9) for nonnegative Borel test functions, successively using
x_1=(t-tau_1)a_1+g_1(a_2,a_3)+c_1, then x_2 and x_3. This is a measure
calculation; it assumes no Jacobian theorem for a nonsmooth map.

For a cubic spatial grid of side r, let p_Q(t)=mu_t(Q). Since sum_Q p_Q=1,

    sum_Q p_Q(t)^(1+theta)
      <= [D r^3 product_i |t-tau_i|^(-1)]^theta.         (10)

For 0<theta<1/3, Holder with three factors bounds the integral of the product
in (10) over every bounded interval J by

    product_i (integral_J |t-tau_i|^(-3theta) dt)^(1/3)
      <= C_theta |J|^(1-3theta).

This bound is uniform in the three real tau_i, and includes coincident focus
times. Hence

    integral_J sum_Q p_Q(t)^(1+theta) dt
      <= C_theta D^theta |J|^(1-3theta) r^(3theta).      (11)

Thus the actual low-moment target holds in this coupled class with no exponent
loss and no change to the original source/time law. Away from the finitely
many tau_i, (9) also gives the stronger actual bounded-density/Frostman exit.
A simultaneous fixed invertible coordinate change in both a and b preserves
the scalar pencil and only changes fixed constants.

This escape covers (3) and shows why a pencil-low-rank phase tangent need not
be a bad physical configuration. It does not show that the manuscript's
remaining coupled rank-loss branch has a fixed triangular representation.
No such classification has been proved.

## 4. Primary-source theorem check

The following checks concern applicability, not just matching vocabulary.

* Hochman's [Dynamics on fractals and fractal distributions](https://math.huji.ac.il/~mhochman/preprints/efds.2.pdf),
  Theorems 1.21-1.23, supplies a lower-semicontinuous projection dimension
  function for CP/fractal distributions and a lower bound for original
  projections through tangent distributions. It gives no reverse inequality.
  Section 6.4 explicitly constructs strict inequality. The fixed scalar
  pencil is not made generic in the full Grassmannian by these results.

* Hochman's [higher-dimensional entropy inverse paper](https://math.huji.ac.il/~mhochman/preprints/ssms-multi-d.pdf),
  Theorem 2.14, treats smooth images of product laws, but requires entropy of
  the image to be within a small delta of the average frozen-factor entropy.
  Time is genuinely independent of the phase source, but a strict front
  deficit alone does not verify that premise. Theorem 1.10 for analytic IFS
  parameters separately excludes reducible systems; the scalar homothety
  presentations of digit graphs are reducible. Neither statement supplies
  the missing source-sensitive macroscopic-block estimate.

* Iosevich et al., [On an entropy inequality for quadratic forms and applications](https://arxiv.org/html/2507.15196v2),
  Theorems 1.3-1.4, really does cover some dependent variables. It requires
  conditional or joint scalar Frostman hypotheses and controls a maximum
  involving sums and additional quadratic quantities. These hypotheses and
  outputs do not imply the required coupled three-coordinate scalar-pencil
  estimate. In particular an arbitrary deterministic graph supplies no
  positive conditional Frostman exponent for its intercept given its slope.

## 5. Repair conclusion

The naive fixed-block entropy/CP path is ruled out by a source-faithful example,
including after a fixed positive reference trim. Macroscopic blocks can pay
for the anticipation term, by (2); they still require a new source-sensitive
finite-scale projection/incidence statement. No checked external theorem
provides that statement here.

The triangular escape (8)-(11) is a proved new partial case, not a replacement
hypothesis for the main theorem. A potentially useful geometric classification
would distinguish delayed triangular information from genuinely recurrent
coupled losses, but deriving it from the existing contact/rank-loss geometry
remains open. The audit therefore does not claim the original gap is filled.
