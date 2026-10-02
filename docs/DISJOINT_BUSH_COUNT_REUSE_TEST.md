# Improved disjoint-bush counts: an exact countertest and a time-bin deduction

Date: 2026-10-02. Status: independently audited handwritten mathematics, not a
new Lean theorem or a completion of Sticky Kakeya.

The quantitative source resolution is genuine progress. This note tests a
specific next inference: its mass floor, improved count, disjointness, and exact
old-root conservation do **not**, even together with strong reference packing
and qualitative residual decay, give a universal aggregate quadratic payment.
The example below has a genuine four-dimensional compact marked front. It does
not satisfy the theorem's strict front dimension deficit, and it does not
exclude a better strategically timed cover or an eventual Frostman escape.

Sections 1--6 give one fixed explicit selector, rather than selectors changing
with the fine scale. Section 7 proves an actual improvement for collision-time
bins and identifies exactly what still needs to be summed or paid.

## 1. A fixed binary selector

For x in [0,1), use the terminating binary expansion at dyadic rationals and set

    O(x) = sum_{k>=1} 2^(-(2k-1)) epsilon_(2k-1)(x),
    E(x) = sum_{k>=1} 2^(-2k) epsilon_(2k)(x).

Then x=O(x)+E(x). Under Lebesgue measure the odd and even digits are independent,
so O and E are independent Cantor variables. Their ranges are

    C_O = {sum_{k>=1} 2*4^(-k) omega_k : omega_k in {0,1}},
    C_E = {sum_{k>=1}   4^(-k) epsilon_k : epsilon_k in {0,1}}.

Both natural Cantor laws are Ahlfors 1/2-regular. Use the construction separately
in three coordinates, put t_*=1/4, and define

    a = x-(1/2,1/2,1/2),
    b(a) = -t_* O(x),
    mu = normalized Lebesgue measure on [-1/2,1/2)^3.

Here the cube has volume one, so mu has density one. It is one fixed source and
one bounded Borel selector. Its actual physical projections satisfy

    Pi_s(a) = (s-t_*) O(x) + s E(x) - (s/2,s/2,s/2).       (1)

The slope norm is at most sqrt(3)/2. Thus the unit segment starting at (b(a),0)
in direction (a,1)/sqrt(1+|a|^2) contains every height in [0,1/2]. All collision
and escape times used below lie in that original common marked slab.

Take the compact closure G of the phase graph. Its marked-line embedding is
continuous on G, so its compact marked front contains the literal trajectories
above. This is a local compact marked patch. No full-direction extension is added
or used in the argument.

## 2. The strongest reference packing properties hold

The phase point (a,b) is an invertible affine image of the six Cantor variables
(O_1,E_1,O_2,E_2,O_3,E_3): recover O from b, and then E from a. The product Cantor
law is Ahlfors 3-regular. Its affine image is the phase pushforward of mu, has
support exactly G, and is again Ahlfors 3-regular. Consequently

    N_delta(G) <= C delta^(-3),
    phase_mu(B(z,delta)) >= c delta^3  for z in G, 0<delta<=1.

In particular the compact carrier has packing dimension three, with uniform
original reference lower masses stronger than c delta^(3+zeta).

There is also a uniform O(1) vertical support count. A dyadic direction cube of
side 2^(-N) fixes the input digits through N. All remaining output O-digits have
size O(2^(-N)). Its phase graph lies in O(1) phase balls at that radius. A
direction ball of comparable radius meets only O(1) such dyadic cubes. Taking
closed boxes covers the closure as well, including the extra boundary fibers.
The estimate passes to every source subset by inclusion.

This is therefore not a failure of reference pruning, lower reference masses,
vertical branching, or bounded direction density.

## 3. Disjoint physical bushes and a genuine excessive old graph

Let n>=3 and set r=4^(-n). Fixing the first n odd digits in each coordinate
gives disjoint measurable color classes H_gamma. They partition the source,
and

    mu(H_gamma) = 2^(-3n) = r^(3/2),
    number of colors = 2^(3n) = r^(-3/2).

The remaining O-tail in each coordinate is between zero and (2/3)r. Thus every
color is a physical time-zero bush of error at most sqrt(3)r/6 < r. Its probe
can be the actual source point with the specified odd prefix and every
remaining digit zero. No probe replaces an old target.

Let S be the fixed source sector whose first three odd digits are 111 in every
coordinate, and T the target sector whose first three odd digits are 000 in
every coordinate. Then

    mu(S)=mu(T)=2^(-9).

Define the old directed graph density

    h_r(a,a') = h_0 1_S(a) 1_T(a')
                      1_{first n even digits agree in all coordinates},

where h_0>0 is one fixed sufficiently small constant. Its ordered graph measure
is Gamma_r=h_r (mu x mu), with coefficient-one product domination.

On its support, the even-tail difference has norm at most sqrt(3)r/3. Equation
(1), at the actual old time t_*, gives

    |Pi_(t_*)(a)-Pi_(t_*)(a')| <= sqrt(3)r/12 < r/4.       (2)

The three fixed odd-prefix digits also give, coordinatewise,

    O_source - O_target >= 31/48.

For r<=1/64, the small even-tail difference therefore leaves

    1 < |a-a'| < 2.                                      (3)

For example each coordinate difference is at least 31/48-r/3, and the maximum
is at most 2/3+r/3; their Euclidean norms give (3). Thus this is the genuine
unit angular shell, not a diagonal graph.

The residual margin in (2) leaves a whole time interval of length comparable
to r around t_* inside the marked slab, on which the collision error is at
most r. Choosing h_0 small makes h_r dominated by the actual fixed-angle
inverse-time-normalized collision kernel. If the old time is a measured mark,
use normalized Lebesgue measure on this interval; an artificial atomic time
law is unnecessary. The closest collision time also differs from t_* by
O(r), so it stays separated from all new time-zero bush centers.

Independence of the odd and even digits gives the exact mass and degree
identities

    M_r = Gamma_r(univ) = h_0 2^(-18) r^(3/2),
    degree_r(a) = h_0 2^(-9) r^(3/2)  for a in S,
    degree_r(a) = 0                  for a outside S.     (4)

Use just the odd-color bushes contained in S. They are disjoint, have count
2^(-9)r^(-3/2), and their union is exactly S. Their literal source restrictions
sum to Gamma_r. Every old target, angular separation, collision residual, and
old time survives, with zero root tail.

For every fixed 0<eta<2, all sufficiently fine r satisfy

    M_r >= r^(2-eta/4),
    mu(H_gamma) >= r M_r/C,
    mu(H_gamma) >= r^(3-eta/8),
    number of bushes <= C/(r M_r),
    number of bushes <= r^(-3+eta/8),
    mu <= r^(-eta/8) volume.

Fixed constants are absorbed by choosing r smaller, exactly as in the actual
power-absorption step. The captured root mass is the whole M_r, in particular
at least r^(2-eta/8). Every requested fixed relative-tail variant is satisfied
because its actual tail is zero.

Yet, for any delta<1/2,

    M_r/r^(2-delta) = h_0 2^(-18) r^(delta-1/2) -> infinity.  (5)

In particular (5) fails the intended aggregate exponent delta=eta/8. The
improved cover data cannot alone pay these original separated-time roots.

There is a useful selection-independent statement, without claiming anything
about all possible geometric strategies. By the degree identity (4), any
measurable source restriction A retaining at least M_r/2 must satisfy

    mu(A)>=2^(-10).                                      (6)

So no alternative choice of a half-mass source union can make that union
polynomially small in r. This does not preclude a different cover that exits
through a real Frostman argument.

## 4. Null exact collisions, qualitative decay, and hereditary excess

Every exact point bush has zero source mass. In one coordinate, (1) is a sum
of two independent Cantor variables with coefficients s-t_* and s. These
coefficients cannot both vanish. A nonzero multiple of a nonatomic variable,
plus an independent variable, is nonatomic. A singleton physical point
therefore has zero preimage mass at every time.

The full exact-collision relation has zero product mass as well. For a pair
of independent source points write Delta O and Delta E in one coordinate.
They are independent nonatomic variables. Except on the null event
Delta O+Delta E=0, its collision time is

    T = t_* Delta O/(Delta O+Delta E).

This law has no atoms. At T=t_* the equality requires Delta E=0. At any other
fixed time, conditioning on Delta E requires Delta O to equal one specified
value. Both events have probability zero. The coordinate collision times are
independent, so the probability that even the first two agree is zero. An
actual three-dimensional exact collision requires all three to agree.

Since the source has bounded density in three dimensions, |a-a'|^(-1) is an
integrable product envelope. Dominated convergence proves full weighted
residual vanishing, including the usual time-normalized physical kernel
bounded by a constant times this inverse secant. Thus neither positive exact
bushes nor failure of qualitative residual decay explains (5).

The example also has excessive residual scales on every positive source
restriction, with a shell allowed to depend on that restriction. Let A have
mass m>0. There are r^(-3/2) even-prefix cells E_e, each of measure r^(3/2).
Cauchy--Schwarz gives

    sum_e mu(A intersect E_e)^2 >= m^2 r^(3/2).            (7)

All these same-even-prefix pairs have the physical residual bound (2). For a
fixed source, same-prefix pairing costs exactly r^(3/2) in the target even
variables. The odd-vector law is 3/2-Frostman and independent of them. Hence
pairs in (7) with |a-a'|<=tau have total mass at most

    C m r^(3/2) (tau+C r)^(3/2).                          (8)

Dropping the target restriction A only increases (8), so there is no
conditional-density assumption. Choose a fixed tau=tau_A>0 small enough,
and then r small enough, to make (8) at most half of (7). This leaves actual
fixed-angle mass at least (m^2/2)r^(3/2). A finite angular dyadic split selects
one fixed shell along a subsequence. Its shell and constants can depend on A;
claiming the unit shell for every arbitrarily small A would be false.

Thus even hereditary excessive scales, together with the other listed
properties, do not replace the actual strict dimension-deficit hypothesis.

## 5. A direct supported Frostman escape

For completeness, the four-dimensional front exit can be proved without
assuming a generic projection theorem or making a moving-support inference.
Let lambda be the natural law of one pair (O,E). It is Ahlfors 1-regular, so
its q-energy is finite for every 0<q<1. Let lambda_s be its pushforward under

    (O,E) -> (s-t_*)O+sE-s/2.

For a fixed nonzero difference z=(Delta O,Delta E), one has, on any fixed
bounded interval containing the marked slab,

    integral |(s-t_*)Delta O+s Delta E|^(-q) ds
        <= C_q |z|^(-q).                                (9)

To verify (9), write the affine function as s v-t_*u, where u=Delta O and
v=Delta O+Delta E. The linear map z -> (u,v) is invertible. If |v| is a small
fixed fraction of |u|, the affine function is uniformly bounded below by a
constant times |u| on the integration interval. Otherwise |v| is comparable
to |z| and integrate the shifted singularity |s-c|^(-q), which is integrable
because q<1. Tonelli therefore gives finite q-energy of lambda_s for almost
every s in J=[1/8,3/8].

Let U_q lambda_s(y) be its q-potential, and restrict lambda_s to

    B_(s,N)={y: U_q lambda_s(y)<=N}.

The restricted measure has ball bound N(2R)^q: if a ball meets B_(s,N), use a
point in that intersection to bound the mass by its potential. These are
measurable kernels in s. For some finite N the measure

    nu_N = integral_J delta_s x (lambda_s restricted B_(s,N))^3 ds

has positive mass, since the restrictions increase to full mass for almost
every s. Every four-dimensional ball of radius R has nu_N-mass at most

    2R [N(2R)^q]^3.

The support is literally in the compact marked front of the one fixed G.
Normalize nu_N to obtain a (1+3q)-Frostman probability. Letting q tend to one
proves that this front has Hausdorff dimension four. No endpoint exponent-4
Frostman bound or positive four-dimensional volume is asserted here.

This actual escape is why the example is a test of an intermediate inference,
not a counterexample to Sticky Kakeya or to a correct paid-or-Frostman theorem.

## 6. A strategically timed cover really can be different

The example does not say its time-zero cover is the only useful one. Fixing
the first n **even** digits instead gives bushes at time t_*. Every old source
and target of one graph edge lies in the same such bush, with error O(r).
There are again r^(-3/2) colors, each of mass r^(3/2). These are genuine common
physical bushes containing the original unit-angle source/target pairs.

Thus the old graph already admits a perfectly coherent, one-time-bin cover.
That alone neither puts its directions in a shrinking cap nor proves a
quadratic bound: (3)--(5) remain true. It can instead be used with the explicit
Frostman escape of Section 5. Under a genuine no-Frostman hypothesis, the
proof must exclude or charge the corresponding structure by an additional
argument using that hypothesis.

## 7. A genuine fixed-time-bin source resolution

Here is a positive deduction applicable to the actual old graph, independent
of the countertest. Fix 0<theta<1; omit zero-mass bins and use only positive
masses in denominators. Let sigma be a probability source, Gamma<=sigma x sigma,
and suppose its actual old pair labels satisfy

    old residual <=r,       |a-a'|<=2,
    |old time-t_k|<=r/2.

The triangle inequality gives, for Gamma-almost every pair,

    |Pi_(t_k)(a)-Pi_(t_k)(a')|<=2r.                       (10)

For any measurable source remainder T, product domination and (10) imply

    Gamma(T x univ)
      <= integral sigma(T intersect Bush(t_k,p,2r)) d sigma(p).  (11)

This is fixed-time averaging, not the time-averaged bound with an extra
factor r. If the remaining bin mass is greater than theta M_k, where M_k
is that bin's original mass, (11) supplies a source bush piece of mass at
least theta M_k/2. Finite maximality as in the existing source-cover proof
therefore yields disjoint source pieces with

    piece mass >=theta M_k/2,
    number <=2/(theta M_k),
    discarded bin root mass <=theta M_k.

The old targets remain unchanged. Moreover, if B_i lies in the 2r-bush about
probe p_i at t_k, (10) puts every target assigned through Gamma|_(B_i x univ)
in the 4r-bush about that same probe. Both physical endpoints really lie in
one enlarged bush. All old pair weights and marks are retained, and the kept
and tail measures sum exactly to the original bin measure.

For K bins covering a fixed time interval, give every bin the same absolute
root-tail budget theta M/K, where M is the total original mass. Discard bins
below that budget and use (11) on the others, with piece threshold

    a=theta M/(2K).

The exact total root tail is at most theta M, and the total number of pieces
is bounded by

    2K^2/(theta M).                                      (12)

For bins of width r in a fixed window, K=O(1/r), so (12) is O(1/(r^2 M)).
This proves the source-faithful, two-sided common-bush reformulation and its
extra time-bin counting cost.

Disjointness here is within each bin. If a selected source piece is removed
from every other bin, its other-time edges are either lost or no longer
known to have both endpoints in the same new bush. Keeping all bins preserves
root mass but permits the source to reappear with different time labels.
The packing count by itself has not supplied a bound for this occurrence
multiplicity. The binary example shows a still more basic limitation: even
K=1 and full two-sided coherence do not imply a direction-cap gain or the
quadratic payment without a genuine Frostman/no-Frostman argument.

### A sharp two-time persistence bound

Suppose a common source set of mass Q is covered by N_1 bushes of error C_0 r
at time s and N_2 bushes of the same error at time t, with |t-s|>=g>0. If the
direction density is at most D, every intersection of one bush from each
family lies in a direction ball of radius 2C_0 r/g: subtract their two
physical-center equations. Consequently

    Q <= C D N_1 N_2 (r/g)^3.                             (13)

The binary example saturates this estimate at fixed g=t_*: the full odd and
even covers have N_1=N_2=r^(-3/2), and each pairwise intersection has source
mass exactly r^3. Those intersections are the usual full-digit dyadic cubes.

Substituting only N_i<=C/(rM) into (13), at fixed g, gives

    M^2 <= C D r/Q.

For Q bounded below this has the square-root threshold. It cannot contradict
the actual final excessive regime M approximately r^2. Thus even a genuine
two-time persistence estimate has a concrete, attained quantitative limit;
it is not the missing aggregate quadratic charge.

## 8. Result and boundary

The independent audits found no error in the binary construction, the exact
mass/degree identities, null-collision argument, hereditary excess, or the
supported Frostman escape. An earlier, separately audited construction using
nonscalar affine perturbations of smooth plateau arrays has the same finite
cover obstruction, but the binary example additionally has constant required
source mass and hereditary excess; it avoids any interpolation assumptions.

No claim is made that the example realizes every additional low-reuse or
conditional polarization-flag condition of the manuscript. Those are separate
hypotheses if a proposed inference actually uses them.

No final theorem, existing axiom, or Lean source is changed by this note.
The proved fixed-time-bin deduction is a real way to remove separated-time
routing while retaining the original roots. Closing the argument still needs
a quantitative collective use of the actual strict front dimension deficit,
beyond count/mass-floor/disjointness and beyond the qualitative consequences
or hereditary excess isolated here.
