# A fixed distributed-bush model without positive-measure classical regularity

Date: 2026-10-02. This is a proved analytic counter-test to a proposed
intermediate implication, not a counterexample to the main theorem. The
model has an explicit four-dimensional Frostman escape. It shows that the
packing estimate and distributed shrinking scalar bushes do not by
themselves force a positive-measure Lipschitz or approximately
differentiable selector restriction.

## 1. The fixed selector

Choose integer sequences

    m_1=4,   n_k=m_k^2,   m_{k+1}=n_k^2.

Thus m_k<n_k<m_{k+1}, n_k-m_k tends to infinity, and both index sets
{m_k} and {n_k} have zero asymptotic density in the positive integers.
For x in [0,1), let epsilon_n(x) be its binary digits, using the terminating
expansion at dyadic rationals. Define

    f(x) = sum_{k>=1} 2^(-m_k) epsilon_{n_k}(x).

This is a bounded Borel function; the series converges uniformly. On
U=[0,1)^3, take ordinary Lebesgue direction measure and the physical selector

    b(a_1,a_2,a_3) = (f(a_1),0,0).

All statements concern this one fixed selector. No parameter-dependent
sequence of smooth selectors is being substituted for it.

## 2. Uniform covering of the closed carrier

Fix an integer N and partition [0,1) into the 2^N half-open dyadic intervals
of length r=2^(-N). On one such interval all input digits through N are
fixed. An output digit with m_k<=N is therefore determined if n_k<=N.
An undetermined output digit relevant at resolution r must satisfy

    m_k <= N < n_k.

There is at most one such k, because n_k<m_{k+1}. It has just two possible
values. The tail from all output positions m_j>N has total size less than
r: its first term is at most r/2 and the later positions are much farther
apart. Consequently, above each input interval the graph is contained in
at most two vertical intervals of length r, hence at most four grid
rectangles of dimensions r by r.

The graph of f is covered by at most 4*2^N closed such rectangles after
replacing the half-open cells by their closures. This finite union is
closed, so it also covers the entire graph closure, including every
extra fiber over a binary boundary. In three directions the same argument,
with the two unrestricted direction coordinates, gives

    N_r(closure{(a,b(a)):a in U}) <= C r^(-3).

Passing from dyadic to arbitrary radii changes C only by a fixed factor.
The carrier is bounded; its closure is compact. Projection onto the
three-dimensional direction cube supplies the matching dimension lower
bound. Thus this is a genuine compact carrier of packing dimension three,
not merely a count of points on a nonclosed selector.

## 3. No positive-measure Lipschitz restriction

Let A be any measurable subset of U with positive three-dimensional
Lebesgue measure. Choose a density point a of A, in the interior of U,
whose first coordinate is not dyadic. Let I_k be the dyadic interval of
length

    ell_k=2^(-(n_k-1))

containing a_1. All input digits preceding n_k are constant on I_k.
The half of I_k whose n_k-th digit differs from that of a_1 has length
ell_k/2. Cross that half with intervals of length ell_k centered at a_2
and a_3. The resulting box lies in a ball of radius 2 ell_k about a and
has volume ell_k^3/2.

By density, its intersection with A has volume at least ell_k^3/4 for all
large k. For every a' in this intersection, all output digits before k
agree with those of a, the k-th one differs, and the remaining output
tail is negligible. In particular,

    |b(a')-b(a)| >= (1/2) 2^(-m_k),
    |a'-a| <= 2 ell_k,
    |b(a')-b(a)| / |a'-a| >= c 2^(n_k-m_k) -> infinity.

No finite Lipschitz constant can hold on A. This is a statement about
arbitrary positive-measure source sets, not only restrictions to intervals
or open sets.

The same calculation excludes a finite approximate derivative on a
positive-measure restriction. For any fixed linear map L, the subtraction
L(a'-a) has norm at most 2||L|| ell_k, negligible compared with 2^(-m_k).
The normalized derivative error therefore stays large on a fixed positive
fraction of the small ball, even after restriction to A. At almost every
point of A the required density-one approximate-linear behavior fails.

## 4. Distributed physical bushes cover all source mass

For a word gamma=(gamma_1,...,gamma_k) in {0,1}^k, put

    H_gamma = {a in U: epsilon_{n_j}(a_1)=gamma_j for 1<=j<=k},
    c_gamma = (sum_{j<=k} 2^(-m_j) gamma_j,0,0).

These are disjoint measurable source sets, each of mass 2^(-k), and their
union is U. They are generally highly disconnected; they are not dyadic
input intervals. The actual selector satisfies

    |b(a)-c_gamma| <= sum_{j>k}2^(-m_j) <= 2*2^(-m_{k+1})
    for a in H_gamma.

Thus they form a genuine physical scalar-bush family at time zero, with
shrinking error, covering total source mass one. Their count 2^k is
subpower in the inverse error, and each individual mass 2^(-k) is larger
than every fixed power of that error for all sufficiently large k.
For an arbitrary intermediate tolerance, choose k so that the displayed
tail is below it; the same finite family remains a valid family of bushes.
This distributed-bush property does not imply the classical regularity
rejected in the preceding section.

## 5. The actual Frostman entropy escape

Let C be the compact set of all sums

    sum_{k>=1} 2^(-m_k) gamma_k,   gamma_k in {0,1}.

It contains the full range of f and its closure. At radius 2^(-N), only
#{k:m_k<=N} output digits matter, so

    N_R(C) <= C_eta R^(-eta)   for every eta>0 and 0<R<1.

This follows directly from #{k:m_k<=N}=o(N), with the finitely many small
N absorbed into C_eta. In particular C has upper box dimension zero.

Choose a fixed compact time interval J separated from zero, within an
available marked interval after a fixed affine rescaling if necessary.
For a projection ball B(y,R) and s in J,

    b(a)+s a in B(y,R)

places a in the R/|s|-neighborhood of (y-C e_1)/s. Covering C by the
preceding R-intervals therefore puts its preimage in at most
C_eta R^(-eta) direction balls of radius O_J(R). Since the direction
measure is Lebesgue,

    sigma{a: b(a)+s a in B(y,R)} <= C_{eta,J} R^(3-eta).

Push forward sigma times normalized Lebesgue measure on J under
(a,s) -> (b(a)+s a,s). A four-dimensional R-ball uses only O(R) time
length, so the resulting genuine front measure obeys

    Lambda(B((y,s),R)) <= C_{eta,J} R^(4-eta).

Its support is contained in the compact front of the closed carrier.
This proves the full-dimensional Frostman conclusion for the model
without a Lipschitz selector piece or an approximate derivative.

One can also check the normalized directions of each color bush directly.
For a dyadic first-coordinate interval of length 2^(-N), a compatible
color law assigns mass exactly

    2^(-N + #{j<=k:n_j<=N}).

The exponent count is o(N), uniformly in k. Including the other two
coordinates yields uniform (3-eta)-Frostman bounds for these color laws.
Thus this model exits through the manuscript's genuine direction-Frostman
alternative rather than surviving its no-Frostman branch.

## 6. What the original remaining branch does not yet supply

A sufficient entropy escape on one fixed positive source S is a common
Reeb time s_0 and a uniform all-radii bound

    N_R({b(a)+s_0 a:a in S}) <= C_eta R^(-eta)

for every eta>0. The preceding covering argument then applies outside s_0.
This is a proved sufficient geometric condition, not an added hypothesis
of the final theorem.

The original `prop:v081-maximal-bush-family` gives a count N<=C M^(-3).
At a power-small fine edge mass M=r^chi, this is a polynomial count, not
a subpower one. Its family mass is bounded below by a multiple of M, not
by a fixed positive constant independent of scale. The checked qualitative
source/submeasure exhaustions do not bound their numbers of pieces.
Moreover, counts at isolated tolerances on changing source sets are not
a uniform cover estimate for the image of one fixed source; varying bush
times cannot silently be replaced by one synchronized time either.

No derivation of the sufficient entropy condition from the manuscript's
remaining no-Frostman/rank-loss branch has been found here. The fixed
countermodel rules out a classical-differentiability shortcut under the
listed distributed-bush facts, while exhibiting the stronger entropy
property that correctly pays this particular nonregular example.
