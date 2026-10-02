# Separated-time bushes: all-target estimates and the aggregation obstruction

Date: 2026-10-02. Status: proved elementary geometric/measure estimates, not a
closure of the original manuscript or an unconditional Lean theorem. This note
is independent of the currently checked Lean modules.

## 1. Scope and original source

The manuscript's Lemma 9.11
(`lem:v081-separated-old-time-fiber-cap`) bounds the source fiber over a fixed
old target by a direction cap. Corollary 9.12
(`cor:v081-separated-fiber-cap-aggregation`) estimates only the part whose old
target also lies in the enlarged source cap, then labels the complement a cross
cap graph.

For one physical bush, the fiber estimate actually controls **all** targets.
There is also a packet-free codimension-two version. The difficulty in the
varying-bush tree is summing these estimates with the original weights. This
note isolates exactly where the summation needs new information.

Throughout, a line is `z=(a,b)` in a bounded chart of R^3 x R^3, and
`Pi_s(z)=b+s a`. Let `sigma` be a finite selector measure of mass `m`, with
its direction pushforward bounded by `D` times three-dimensional Lebesgue
measure. Assume its direction support is contained in `B(0,A)`, with `A>0`.
Let `Gamma` have density `0 <= h <= 1` relative to `sigma x sigma`.
Additional conditional probability flags do not change any statement below:
integrate them out first, keeping the two original endpoints fixed.

## 2. Entire one-bush packet bound

Suppose every source in the support of `Gamma` obeys

    |b+s0 a-c| <= R.

Suppose every retained ordered pair `(z,zeta)` has an actual collision label
`t` satisfying

    |(b-b_zeta)+t(a-a_zeta)| <= r,
    |t-t0| <= delta,
    |t0-s0| >= g > 0.

Then

    Gamma(univ) <= (4 pi/3) D m [(R+r+2 A delta)/g]^3.             (1)

In particular, (1) estimates the cross-cap part too. It does not require the
old target to belong to the source cap.

Proof. Put `e=b+s0 a-c` and `d_zeta=b_zeta+s0 a_zeta-c`. At time `t0`,

    (t0-s0)(a-a_zeta)-d_zeta
      = (b-b_zeta)+t0(a-a_zeta)-e.

The right side has norm at most `r+2 A delta+R`. Thus the entire source fiber
over `zeta` lies in the ball with explicit center

    a_zeta + d_zeta/(t0-s0)

and radius `T=(R+r+2 A delta)/g`. The center is a measurable function of the
old target; no selection of a representative from a fiber is needed. Direction
density bounds the source measure by `D (4 pi/3) T^3`. Since `h<=1`, Tonelli
and integration over the target measure prove (1). QED.

The same conclusion holds for any submeasure dominated by the displayed
product measure and supported on these physical incidences. Source/target
swapping is not used.

## 3. Packet-free codimension-two estimate

Keep the same physical bush and the actual collision-error bound, but replace
the time-packet hypothesis by

    |t-s0| >= g > 0

for every retained pair. Set `epsilon=(R+r)/g`. If `0<epsilon<=A`, then

    Gamma(univ) <= 2 pi D A m epsilon^2.                         (2)

A harmless universal enlargement of the constant is available if closed-set
boundaries or a different chart norm are used. At `epsilon=0`, the same
argument gives zero, by absolute continuity and the nullity of a line.

Proof. The exact identity is

    (t-s0)(a-a_zeta)-d_zeta
      = (b-b_zeta)+t(a-a_zeta)-e.

If `d_zeta` is nonzero, orthogonal projection onto its perpendicular plane
shows that `a` has distance at most `epsilon` from the affine line

    L_zeta = a_zeta + span(d_zeta).

The intersection of its `epsilon`-tube with `B(0,A)` has volume at most
`2 pi A epsilon^2`: use the line direction as one coordinate, whose range
inside the ball has length at most `2A`, and integrate perpendicular disks of
area at most `pi epsilon^2`. If `d_zeta=0`, the exact identity instead gives
`|a-a_zeta|<=epsilon`, whose ball volume is `(4 pi/3)epsilon^3`, at most
`2 pi A epsilon^2` for `epsilon<=A`. Direction density and Tonelli now prove
(2). QED.

Thus a separated-time bush of error `R<=C r` and fixed time gap `g>=g0`
has a genuine `O(D A m r^2)` all-target estimate. Packet subdivision is not
necessary to obtain the codimension two for one bush.

The factor is `m`, not automatically `m^2` or the incoming old-edge source
mass. Freezing a positive coarse mass lets constants depend on that mass, but
cannot erase dependence on arbitrarily small later node masses or the number
of nodes.

## 4. A precise sufficient aggregate hypothesis

Let the first-exit pieces have densities `h_v` relative to the **same**
`sigma x sigma`, with

    0 <= h_v <= 1,       sum_v h_v <= h_root <= 1.

Assume piece `v` is supported on a bush of error `R_v`, center `(c_v,s_v)`,
and old collision labels separated from `s_v` by at least `g_v>0`. Put
`epsilon_v=(R_v+r)/g_v`, with `epsilon_v<=A`.

If there are measurable target envelopes `w_v(zeta)` such that

    h_v(z,zeta) <= w_v(zeta),        0 <= w_v <= 1,

then the proof of (2), with the target factor retained, gives

    sum_v Gamma_v(univ)
      <= 2 pi D A int [sum_v w_v(zeta) epsilon_v^2] d sigma(zeta).   (3)

This is a proved implication. The sum may be countable, by Tonelli.

For example, an actual construction proving

    epsilon_v <= C0 r,
    sum_v w_v(zeta) <= C1 m r^(-eta)  for sigma-a.e. zeta           (4)

would give the requested

    sum_v Gamma_v(univ) <= 2 pi D A C0^2 C1 m^2 r^(2-eta).

A time-packet version uses the cubic radius from (1) instead. One can also
replace the envelope count by a geometric bound on the union of the target's
source-fiber tubes, provided its measure is controlled with the inherited
fractional densities.

**The known forest accounting does not imply (4).** It controls the sum of the
`h_v` at a fixed pair `(z,zeta)`. Taking a supremum or an envelope over the
source before summing is a different operation. Disjoint source pieces may
all have envelope one at the same target. Shrinking their source caps gives
no bound on the number of such pieces.

## 5. An actual physical test of the aggregation step

This example disproves any assertion that bounded direction density,
three-dimensional carrier packing, actual Reeb collisions, disjoint source
bushes, and coefficient-one endpoint-pair accounting by themselves imply a
quadratic bound on the aggregate separated-time cross-cap graph. It is **not**
a counterexample to the full theorem or to a no-Frostman branch with all of
its additional hypotheses.

Take a fixed bounded direction cube `Omega` of positive volume, normalized
Lebesgue direction measure, and the radial selector

    z_a=(a,0),       a in Omega.

All old edges collide exactly at time `t=0`. Choose a fixed angular cutoff
`tau0>0` small enough that

    h_root(a,a') = 1_{|a-a'| >= tau0}

has mass `M0>0`. This is an actual physical collision graph at every positive
root error `r`; inserting the manuscript's time-averaged normalization only
changes its mass by fixed constants on a bounded fixed-angle sub-shell.
The carrier is a smooth three-dimensional set and hence has packing dimension
three.

Fix `s0=1`. Partition `Omega` into half-open cubes `Q` of side `ell`, with
centers `a_Q`, and use source bushes

    H_Q={z_a: a in Q},       c_Q=a_Q.

They are pairwise disjoint and satisfy

    |Pi_1(z_a)-c_Q| = |a-a_Q| <= sqrt(3) ell/2.

Every old time is separated from the new center time by one. Let

    h_Q(a,a')=1_Q(a) h_root(a,a').

Then `sum_Q h_Q=h_root` exactly. If the enlarged source caps have diameter
smaller than `tau0`, every retained old edge is cross-cap. Consequently

    sum_Q Gamma_Q(univ)=M0,

independently of `r` and `ell`. Choosing `ell=r` makes every bush error `O(r)`
and every separated time gap equal to one, so the local quadratic estimate
(2) applies to every piece. Nevertheless the aggregate mass stays constant
while `r^(2-eta)` tends to zero for every `0<eta<2`.

Here the source partition has order `r^-3` pieces, and many of their target
envelopes equal one at each target. Pairwise disjointness of sources therefore
cannot justify (4). The local estimates themselves remain correct and need
not be sharp: in this example each source cube has mass `O(r^3)`.

The radial front contains an open four-dimensional region away from time
zero: `(a,s) -> (s a,s)` has smooth inverse `(x,s) -> (x/s,s)` for `s` bounded
away from zero. Thus a genuine Frostman exit must be available in this model.
This is exactly why the example tests the proposed *aggregation mechanism*
rather than contradicting the original final theorem. Arbitrary conditional
probability marks can be retained, but this observation does not assert that
the model satisfies the special low-reuse, origin-flag, or unpaid-branch laws.

## 6. Consequence for the proof attack

There is now a concrete all-target estimate available on every single
separated-time physical bush. To convert it into the original weighted
first-exit theorem, the construction must supply one of the following:

1. A targetwise weighted multiplicity bound such as (4), proved using the
   actual origin/old-flag laws and the no-Frostman branch;
2. A summable geometric bound on the union of source-fiber lines/tubes, with
   the inherited fractional weights;
3. A proof that an excessive value of the charge in (3) produces a genuine
   paid or Frostman output with a terminating or quantitatively summable
   rerouting, rather than only another smaller source cap.

These are geometric tasks, not consequences of probability normalization.
The same-window first-exit portion is not covered by (1)--(3), since its
separation denominator vanishes; its amplification/common-target mechanism
must be treated separately.

In particular, the source's assignment of every old target outside a new cap
to `M_cross` is broader than the separated-time class proved here. This note
supplies a real local payment and a falsifiable aggregate target, but does
not claim the missing full cross-cap payment has been proved.
