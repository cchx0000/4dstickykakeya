# Sparse digit deletion: a monotone-parameter Frostman escape

Date: 2026-10-02. This is a handwritten, independently audited local geometric
example, not a Lean-certified theorem and not a counterexample to the original
Sticky Kakeya theorem. Its actual compact marked front has positive
four-dimensional volume. It tests a proposed intermediate dichotomy: minimal
carrier packing dimension need not give either a positive-source Lipschitz
restriction or a fixed-affine, zero-entropy centered image.

The example and its inverse parametrization were proposed during the current
proof investigation. The argument below verifies both the escape and the
limits of that proposed dichotomy. No derivation of this parametrization from
the manuscript's remaining no-Frostman/rank-loss branch is asserted.

## 1. One fixed selector and its compact carrier

Put

    n_i = i + ceil(sqrt(i)),   i >= 1.

These integers are strictly increasing. Their complement in the positive
integers is infinite and has density zero. Also n_i-i tends to infinity.
For x in [0,1), write epsilon_n(x) for its binary digits, using terminating
expansions at dyadic rationals, and define

    f(x) = sum_{i>=1} 2^(-i) epsilon_{n_i}(x).

On U=[0,1)^3, use ordinary three-dimensional Lebesgue measure and set

    b(a_1,a_2,a_3) = (f(a_1),0,0).

The function is bounded and Borel. Let G be the closure in R^3 x R^3 of
its graph. Then G is compact and projects onto [0,1]^3.

At resolution r=2^(-N), put k_N=#{i:n_i<=N}. One input dyadic interval
of length r fixes the first k_N output digits. At most N-k_N additional
output digits affect the output r-cell, so at most 2^(N-k_N) output cells
are possible. The remaining output tail has length at most r. Because

    N-k_N = O(sqrt(N)),

covering all three input coordinates gives

    N_r(G) <= C 2^(3N+O(sqrt(N))).

One can take closed grid boxes: their finite union covers the graph, hence
also its closure. Dyadic-to-arbitrary-radius comparison changes only the
constant. Thus G has upper box dimension at most three. Its projection onto
the direction cube gives the matching lower bound; in particular

    dim_P G = 3.

This is one fixed compact carrier, rather than a changing family of
scale-dependent smooth examples.

## 2. No positive-measure source restriction is Lipschitz

Let A be any positive-measure subset of U. Choose an interior density point
a=(x,u,v) of A with x nondyadic. For each i, let I_i be the binary interval
of depth n_i-1 containing x, and let

    ell_i = |I_i| = 2^(-(n_i-1)).

All retained digits preceding n_i are fixed on I_i. Select points x' in
I_i whose n_i-th input digit differs from that of x. In addition, prescribe
the n_(i+1)-th input digit as follows:

- If the i-th output digit of f(x) is zero, prescribe the next output digit
  of f(x') to be one
- If the i-th output digit of f(x) is one, prescribe the next output digit
  of f(x') to be zero

These two independent bit prescriptions select exactly one quarter of I_i.
For every selected x', including all choices of the later output tail,

    |f(x')-f(x)| >= 2^(-i-1).

The second prescription is important: merely flipping the i-th output digit
would permit cancellation by the subsequent output digits.

Cross this selected set with intervals of length ell_i centered at u and v.
The result has volume ell_i^3/4 and is contained in B(a,2 ell_i). Density of
A at a therefore supplies a' in its intersection with A for all large i.
Consequently

    |b(a')-b(a)| / |a'-a|
      >= 2^(n_i-i-3) -> infinity.

No finite Lipschitz constant can hold on A. This excludes all
positive-measure source restrictions, not just open source subsets.

## 3. Independent inverse coordinates and monotonicity

Let the coordinates y and z be given by the retained and omitted digits,
respectively:

    y = f(x),
    z = sum_{n not in {n_i}} 2^(-n) epsilon_n(x).

Define the zero-insertion map

    g(y) = sum_{i>=1} 2^(-n_i) epsilon_i(y).

Outside a null set of binary-expansion ambiguities,

    x = g(y)+z.

Under Lebesgue measure in x, the variable y is uniform on [0,1], z has its
omitted-digit probability law, and y and z are independent. This follows
first for finite bit cylinders from independence of binary digits and then
for the generated sigma-algebras. The same identity holds for the resulting
product law almost surely.

The map g is increasing. Indeed, at the first differing output digit, the
positive contribution 2^(-n_i) dominates the sum of all later retained-digit
contributions. The omitted-digit set is infinite, so the domination is
strict. The map has jumps at some dyadic arguments; continuity is not being
assumed.

For every s>0, the map

    h_s(y) = y+s g(y)

satisfies

    h_s(y')-h_s(y) >= y'-y     whenever y'>y.

Hence the inverse image of any interval of length L under h_s has Lebesgue
measure at most L. Conditioning on z and translating by s z gives the same
bound for the law of

    f(x)+s x = y+s g(y)+s z.

This is an actual uniform one-dimensional density bound, rather than a
cover-count estimate with a subpower loss.

## 4. Explicit compact marked-line embedding and physical measure

For (a,b) in G, put

    theta(a) = (a,1) / sqrt(1+|a|^2),
    X(a,b)   = (b,0) in R^4.

Take the marked unit interval

    { X(a,b) + t theta(a) : 0 <= t <= 1 }.

Equivalently, in orthogonal-offset/affine-mark coordinates its line offset
and mark are

    p = X - <X,theta> theta,
    z_mark = <X,theta>.

The map from G to these marked data is continuous, and is Lipschitz on the
bounded chart. Its unmarked line map has a Lipschitz inverse on this chart:
recover a from the direction and b from the line's intersection with the
last-coordinate-zero hyperplane. Thus the compact marked datum has an
unmarked carrier of packing dimension exactly three. This construction
covers the indicated direction patch. It is sufficient for the local
structural test here; no claim that this single patch parametrizes the
entire direction sphere is made.

For a in [0,1]^3 one has sqrt(1+|a|^2)<=2. Therefore every marked interval
above contains

    F(a,s) = (b(a)+s a,s),    s in J=[1/4,3/8],

since its unit-speed parameter is t=s sqrt(1+|a|^2)<=3/4.
Let K be the compact unit front of this datum, and let Lambda be the
pushforward of ordinary source Lebesgue measure times normalized Lebesgue
measure on J under F. It is a probability supported literally on K.

Fix s in J. A spatial ball of radius R restricts each of the second and
third spatial coordinates to an interval of length at most 2R. Since those
coordinates are s a_2 and s a_3, their probabilities are at most 2R/s each.
The conditional first-coordinate bound from Section 3 gives probability
at most 2R. Independence of a_2,a_3 from y,z consequently gives

    sigma{a: b(a)+s a in B(w,R)} <= 8 R^3/s^2 <= 128 R^3.

A four-dimensional ball of radius R uses at most 2R of the time interval J.
As |J|=1/8,

    Lambda(B((w,s_0),R)) <= 2048 R^4.

Thus Lambda is an actual endpoint 4-Frostman probability. In fact its
spatial conditional laws have density at most s^(-2), so its spacetime
law is dominated by 128 times four-dimensional Lebesgue measure on
R^3 x J. In particular K has positive four-dimensional volume.

This proves a stronger escape than the zero-entropy-centered-image
argument, even though the original source parametrization has no positive
Lipschitz piece.

## 5. No fixed-affine centered image has zero entropy on a positive source

We first justify the derivative statement needed here. The increasing
function g is differentiable almost everywhere. On any dyadic interval of
length 2^(-i), its oscillation is at most

    sum_{j>i} 2^(-n_j) <= 2^(-n_i).

At a nondyadic point where g is differentiable, the quotient of this
oscillation by the interval length tends to its derivative: differentiability
controls the errors to both endpoints by o(2^(-i)). Since

    2^(i-n_i) -> 0,

we obtain g'(y)=0 almost everywhere. Thus, for every fixed real c,

    h_c(y) := y-c g(y)

has derivative one almost everywhere.

A derivative slogan alone is insufficient for the image assertion, so here
is the required restriction argument. At every point y where h_c'(y)=1,
there is a radius r_y>0 for which

    |h_c(v)-h_c(y)| >= (1/2)|v-y|     if |v-y|<r_y.

Group these points by r_y>=1/m and intersect each group with intervals of
length less than 1/m. These countably many pieces cover almost every y.
On every piece h_c is 1/2-co-Lipschitz. If Y is any positive-measure subset
of [0,1], at least one of these pieces meets Y in positive outer measure.
The inverse map on its image is 2-Lipschitz, so that image has positive
one-dimensional outer measure. For Borel Y the full image h_c(Y) is
analytic and Lebesgue measurable, and therefore has positive Lebesgue
measure. Passing to a positive Borel subset proves the corresponding
assertion for an arbitrary Lebesgue-measurable Y.

Now fix any real 3-by-3 matrix F and any positive-measure source set
A subset U. Pull A back under

    (y,z,u,v) -> (g(y)+z,u,v).

The product-law identity from Section 3 and Fubini yield fixed z,u,v for
which the y-section Y has positive Lebesgue measure. On that section, the
first coordinate of the centered image b(a)-F a is

    y-F_11 g(y)-F_11 z-F_12 u-F_13 v.

By the preceding argument its image has positive one-dimensional measure.
Therefore the first-coordinate projection of

    { b(a)-F a : a in A }

has positive measure. In particular, for small R its covering number is
at least c_(A,F) R^(-1); its upper box dimension is at least one. It cannot
have the subpower covering bound required by a zero-entropy escape.

The conclusion holds for every fixed F and every positive source A. Scalar
centerings b+s_0 a are a special case. A translation of the centered image
does not change the conclusion.

## 6. Consequence for the remaining proof

This example rules out inferring the following local dichotomy from the
packing-three graph condition alone:

    positive-source Lipschitz restriction
    OR fixed-affine zero-entropy centered image on a positive source.

It does not survive a genuine no-Frostman hypothesis: Section 4 constructs
an explicit 4-Frostman probability on its actual compact marked front.
Thus it does not refute the desired nondegenerate-or-paid/Frostman
alternative, the original final theorem, or a strengthened argument that
really uses the no-Frostman branch.

A parameter change with independent coordinates and an expanding projected
map supplies a valid additional sufficient escape. Deriving such a
representation, or a different quantitative paid/Frostman mechanism, from
the actual remaining weighted rank-loss geometry is still open. No new
final-theorem assumption is introduced here.
