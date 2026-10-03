# Genuine cyclic-product Lq estimates and the remaining inverse premise

Date: 2026-10-03. Handwritten proof and primary-source applicability audit.
No general continuum-time cyclic projection estimate is asserted.

## 1. Why independence now really is available

For the product reference on three scalar graph factors, the cyclic slice law
is the ACTUAL independent convolution of three embedded planar graph measures.
Thus the general same-source objection to replacing correlated marginals by
an independent convolution does not apply to this reference law. An actual
source dominated by the product can subsequently inherit an established
reference upper estimate by domination.

Nevertheless a deficit below dimension3 does not by itself give negligible
flattening when the third factor is added. The explicit example below proves
this using the graph structure and all three genuine independent factors.

## 2. Fixed Ahlfors graph example and exact algebra

Let C be the Bernoulli Cantor measure with base-4 digits {0,1}. Let U,D be
independent vectors of three independent C-coordinates. Put

  A=U+2D,  f(A_i)=U_i-2D_i.

Each A_i is uniform Lebesgue on [0,1]; each f(A_i) is also a uniform scalar
marginal on a translated interval. The scalar graph carrier is Ahlfors1 and
a graph off a null set, as explained in the cyclic chart obstruction note.
Let P(a_1,a_2,a_3)=(a_2,a_3,a_1), and use the genuine cyclic selector

  b(A)=P f(A).

At the actual time t=1,

  X=A+P f(A)=(I+P)U+2(I-P)D.

Since P^3=I,

  (I+P)^(-1)(I-P)=P^2-P.

Hence the fixed invertible output change gives

  Y=(I+P)^(-1)X=U+W,
  W=2(P^2-P)D,
  S=sum_i Y_i=sum_i U_i.                              (1)

W is independent of U and supported in the sum-zero plane.

## 3. Two explicitly computable Lq spectra

For q>1 let Z_q(nu,r) be the sum of q-th powers of the masses of fixed grid
cubes of side r. Fixed invertible linear changes and bounded grid translations
alter Z_q by at most fixed multiplicative constants.

The law of S has independent base-4 digits with weights

  s=(1,3,3,1)/8.

Thus at r=4^(-n), Z_q(S,r)=(sum_j s_j^q)^n. Define

  d_S(q)=-log_4(sum_j s_j^q)/(q-1).

Up to a fixed linear isomorphism of its plane, W is the law of
(D_1-D_3,D_2-D_3). Its digit set is a seven-point hexagonal set: the zero
vector occurs with weight1/4 and six nonzero vectors with weight1/8 each.
These maps have strong separation. Indeed the attractor lies in
[-1/3,1/3]^2, so child bounding squares have side1/6 and their differing
coordinates are separated by1/4. Therefore

  Z_q(W,r) is comparable to (sum_j w_j^q)^n,
  w=(1/4,1/8,1/8,1/8,1/8,1/8,1/8),
  d_W(q)=-log_4(sum_j w_j^q)/(q-1).                    (2)

Constants in these comparisons are independent of n.

## 4. A real conditional-product upper bound on the full moment

Choose linear coordinates (S,Z) on Y, with Z two transverse coordinates.
For each S-grid interval B, condition the U-law on {sum U in B}. The
conditional Z-law is a mixture of translates of the SAME independent W-law.
Convexity of the discrete q-moment and uniform grid-translation comparison
therefore give

  Z_q(X,r) <= C_q Z_q(S,r)Z_q(W,r)
            <= C_q r^[(d_S(q)+d_W(q))(q-1)].            (3)

This is an actual source-faithful use of independence. It is not an assertion
that a general conditional fiber law is bounded by its unconditional marginal.
The independence here is the explicit U versus W independence in (1).

## 5. A complementary full-moment lower bound

The Y-law has a homogeneous ratio-1/4 coding with 56 digit translations:
eight independent U-digit choices and seven W-digit choices. Their weights
are (1/8)w_j. Distinct pairs give distinct translations: a difference between
U-digits has coordinates in {-1,0,1}, while a difference between W-digits has
even integer coordinates; equality forces both differences to vanish.

No separation assertion for the FULL 56-map coding is needed. Each n-cylinder
has diameter O(r) and occupies O(1) r-grid cubes. Convexity under possible
cylinder overlap gives

  Z_q(X,r) >= c_q [8^(1-q) sum_j w_j^q]^n
            =c_q r^[(3/2+d_W(q))(q-1)].                (4)

Thus every lower/upper Lq dimension, when formulated using liminf/limsup, lies
between d_S(q)+d_W(q) and 3/2+d_W(q). No unsupported existence-of-limit claim
is needed.

For q=2 these bounds are

  log_4(512/25)=2.1780719... <= L2 dimension bounds
                           <= 3/2+log_4(32/5)=2.8390359....

As q decreases to1,

  d_S(q) -> [3-(3/4)log_2 3]/2 =0.9056391...,
  d_W(q) -> 11/8 =1.375.

The resulting lower and upper bounds tend to 2.2806391... and 2.875.

## 6. Every two-factor partial convolution has dimension exactly2

At t=1 each of the three embedded graph factors has Z_q comparable to
r^(q-1): horizontal Lebesgue domination gives the cell upper bound, and its
Ahlfors1 carrier gives an O(r^(-1)) support count.

For any two distinct cyclic factors, a two-coordinate output projection is
a Borel shear of two independent uniform variables. It has bounded planar
density. Hence every three-dimensional r-cube of the pair convolution has
mass O(r^2). Conversely its support is a linear image of an Ahlfors2 product
carrier, so occupies O(r^(-2)) grid cubes. Together these imply

  Z_q(pair,r) is comparable to r^[2(q-1)].              (5)

Combining (3) and (5), the q-norm ratio of full to pair convolution is at most

  C_q r^[(d_S(q)+d_W(q)-2)(q-1)/q].                    (6)

The exponent is strictly positive for 1<q<=2: both explicit dimensions are
decreasing in q, and their sum is already greater than2 at q=2. No positivity
claim for every q>1 is made; the same bound can be vacuous for large q.
Yet (4) proves a fixed deficit below full dimension3.

## 7. Exact primary inverse-theorem boundary

Shmerkin, "Inverse theorems for discretized sums and Lq norms of convolutions
in R^d", Theorem1.2, requires

  ||lambda*nu||_q >= 2^(-epsilon m)||lambda||_q,

with epsilon sufficiently small after its block parameters are chosen.
Source: https://arxiv.org/html/2308.09846v3#S1

Its independent-convolution setting is legitimate here. But the explicit
cyclic graph above has a power-sized norm decrease (6), while still showing
a nonzero deficit from dimension3. For epsilon below that fixed decrease,
the premise fails. Consequently a full-dimension deficit cannot simply be
relabelled as this theorem's near-no-growth premise.

A viable continuation needs an additional multiscale dimension-additivity
inverse statement, an extremal reduction producing genuine near-no-growth,
or another estimate using variation of the actual time parameter. It must
also control the selected pieces and time exceptional sets. None of these
additional steps is proved by the current cyclic calculation. The example
uses just one actual time; it neither refutes an almost-everywhere-time
projection theorem nor asserts a low-dimensional full front.
