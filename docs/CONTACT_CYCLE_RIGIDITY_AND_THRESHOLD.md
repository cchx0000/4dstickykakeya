# Genuine contact-cycle rigidity and its threshold obligation

Date: 2026-10-02. The elementary rigidity below is a proved geometric input.
It does not assert that every excessive old graph supplies a cycle at the
required determinant threshold, or that the final cross-cap ledger is paid.

## 1. Keep the actual old vertices, times and error

Let the four physical vertices be `(a_i,b_i)`, cyclically indexed by `i=0,1,2,3`.
Put

    alpha_i = a_{i+1}-a_i,
    beta_i  = b_{i+1}-b_i,
    e_i     = beta_i+t_i alpha_i,

where all `t_i` are the actual inherited collision labels and `|e_i|<=r0`.
No closest-time substitution or new fine-scale neighbor is needed. Both
oriented secant sums vanish. Therefore the exact identity is

    sum_{i=0}^2 (t_i-t_3) alpha_i = sum_{i=0}^3 e_i.       (1)

Let `A` have columns `alpha_0,alpha_1,alpha_2`. Its determinant equals the
manuscript's anchored determinant

    det(a_1-a_0,a_2-a_0,a_3-a_0).

Assume `|A_ij|<=M` and `|det A|>=Delta>0`. The actual 3-by-3 adjugate formula
gives

    |adj(A)_ij| <= 2M^2,
    |(A^{-1})_ij| <= 2M^2/Delta.

Since every coordinate on the right of (1) has size at most `4r0`, it follows
that

    |t_i-t_3| <= 24M^2 r0/Delta                       (2)

for every `i`. Pairwise time gaps are at most twice this quantity. A bounded
direction chart gives the required frame bound directly: if `|a_i|<=U`, then
one can take `M=2U`.

The Lean modules `three_matrix_inverse_bounds` and `contact_cycle_rigidity`
prove these facts from actual matrix identities and actual contact errors.
They do not assume an inverse-norm or time-concentration certificate.

## 2. The actual plane is nearly a scalar Lagrangian graph

Let `B` have columns `beta_0,beta_1,beta_2`. Since `A` is invertible, the actual
phase-space span of the three consecutive cycle edges is the graph of

    F = B A^{-1}.

In particular, `F(Au)=Bu` for every frame coefficient vector `u`; this is the
original cycle plane, not a separately assigned canonical label.

At the reference old time `t_3`, every entry of `B+t_3 A` has size at most

    r0 + M (24M^2 r0/Delta).

Thus the checked matrix-product estimate gives

    |(F+t_3 I)_ij|
      <= 6M^2 r0/Delta + 144M^5 r0/Delta^2.          (3)

If `0<Delta<=1`, this is at most

    E = (6M^2+144M^5) r0/Delta^2.

Consequently, if the genuine scalar-slope label `F_00` belongs to a cell of
radius `theta` centered at `c`, then every old time belongs to the single
packet centered at `-c`, with

    |t_i+c| <= theta + (30M^2+144M^5) r0/Delta^2.     (4)

Every inherited edge is still a physical collision at that common packet
center, with explicit error

    r0 + [theta+(30M^2+144M^5)r0/Delta^2] |alpha_i|.  (5)

These are root-error estimates: no occurrence with residual only bounded by
`r0` has silently acquired an auxiliary error `rho<<r0`.

The scalar labels are bounded when the old Reeb window is bounded and the
error in (3) is small, so they can be partitioned by ordinary measurable
interval cells. All cells may be retained. Matrix-cell coherence also implies
(4), since only one diagonal entry is needed.

## 3. Why generic cubic interpolation was too weak

For arbitrary coherent three-planes, four approximate pencil incidences at
`delta`-separated times only give a generic leading-coefficient estimate of
size `O(epsilon delta^{-3})`. Attempting to use old root error
`epsilon=O(r0)` and `delta=o(r0^{2/3})` is not justified by that estimate.

A genuine nondegenerate contact four-cycle has the additional rigidity (1).
It is close to the scalar graph `-tI`, so the direct linear comparison (4)
replaces the generic cubic argument on this branch.

For a fixed bounded chart and `Delta=r0^d`, (3)--(5) have error
`O(r0^{1-2d})`. With `d<1/6` and `theta=o(r0^{2/3})`, this is
`o(r0^{2/3})`, compatible with the original terminal source-cap scale
`T=r0^{2/3+o(1)}`. More generally, at a target `T` of order
`r0^{(2-eta)/3}`, the exponent condition is `d<(1+eta)/6`.

This establishes compatibility **when the actual rooted cycle has the
specified determinant lower bound**. It does not establish availability of
that determinant scale.

## 4. Exact source quantifiers for availability

Original `prop:v050-arbitrary-threshold-maslov-routing` applies to a normalized
physical graph of edge mass `M` for every `r<=c Delta`. It gives a physical
bush **or** determinant-small four-cycle content at least a constant times
`M^4`. It does not discard the determinant-small branch by a volume bound.

Original `cor:v081-k-flag-arbitrary-threshold` explicitly allows

    M=r^{chi+o(1)},   chi<2,   any d in (0,1),   Delta=r^d,
    k>4chi/d,         4chi/k<alpha<d-beta<d.

This is not restricted to a constant-density two-copy bush graph. However,
its proof excludes only the fully coherent rank-loss event by independent
old-flag sampling. Its concluding physical-bush assertion is explicitly
conditional on removing the close-anchor, horizontal-line and transverse
ledgers. Those must be removed by actual root-weighted estimates or by a
valid Frostman escape. A positive packet-thickness gain alone is not the
quadratic cross-cap estimate.

For an unused original occurrence, the physical root graph may be lifted with
fresh genuine old flags while its correlated inherited marks are preserved.
That validates the stated independent-normal comparison. It does not by
itself prove that the other outputs are paid at a chosen large determinant
threshold, or restore their weighted product laws after conditioning.

## 5. A fixed physical selector where the large-threshold cycles are absent

The following tests an unconditional mesoscopic-availability inference. It
is not a counterexample to the sticky Kakeya theorem or to the full non-paid,
no-Frostman branch of the source.

Choose two fixed small slope balls, centered at `0` and `e_1`, with radii much
smaller than the fixed angular cutoff. Let `v=e_2`, so `v` is uniformly
transverse to every secant joining the two balls. On the first patch define

    b(a)=|a|^4 v,

and on the second define

    b(a)=-|a-e_1|^4 v.

Use a fixed bounded-density direction measure on these two patches and a
fixed time window containing zero. The carrier is a smooth three-dimensional
graph. For a cross-patch pair, the vertical difference is

    beta=(|a|^4+|a'-e_1|^4)v.

Uniform transversality makes its perpendicular collision residual comparable
to the positive scalar `|a|^4+|a'-e_1|^4`. Therefore the **actual** fixed-angle
scale-`r` graph is supported on two caps of radius `O(r^{1/4})`. On smaller
constant multiples of these caps its normalized time-averaged collision
weight is bounded below by a positive constant, because the closest time
lies in the fixed window and the collision interval has length comparable
to `r`. Hence its edge mass is comparable to

    r^{3/4} r^{3/4} = r^{3/2}.

Within-patch pairs are excluded by the angular cutoff. Every genuine
four-cycle consequently alternates between the two shrinking caps. In the
anchored determinant, one same-patch difference and the difference of the
two opposite-patch columns are both `O(r^{1/4})`; the remaining column is
bounded. Thus every cycle determinant is `O(r^{1/2})`.

For any `d<1/6`, all cycles are determinant-small at `Delta=r^d` for small
`r`. This remains true even if fresh cycle witnesses use every available
edge of this actual root graph; it is not an artifact of thinning to one
small rectangle.

The example has a genuine four-dimensional front. For this smooth selector,
choose a Reeb time where `Db(a)+sI` is invertible on a positive open patch;
the ordinary inverse function theorem gives an open front region. It is
therefore precisely a model that must leave through a genuine good/Frostman
or already-paid branch. No claim is made that it survives the manuscript's
coarse low-reuse/non-paid preprocessing.

## 6. Canonical packets do not replace paid-cycle witnesses

Every old edge can already be put in a physical target/time packet with
canonical scalar label `L_t` and error `O(r0+cell width)`. Such packetization
is valid and preserves the old pair. It works for arbitrary physical
collision graphs and therefore does not itself provide a new quantitative
gain or termination mechanism.

The old/new transverse comparison in
`lem:v078-old-flag-new-cycle-polarization` uses an actual old
`E_old x E_old` packet and an actual determinant-small new four-cycle packet
`E_new x E_new` at the same endpoint, with their weighted anchor/cycle law.
A scalar Lagrangian `L_t` has full horizontal rank three and supplies no such
horizontal polarization normal or anchor law. Conversely the source proof
of `lem:v081-common-target-source-polarization-cycle` merely carries separated
three-plane labels through another sourcewise route and still permits
physical-bush children. Its noncoherent branch is not made numerically paid
by replacing the labels with canonical `L_t` packets.

The next global task is therefore genuine availability/payment on the
non-paid old-root graph, followed by a summable treatment of its noncoherent
or moving-time physical-bush returns. The checked rigidity resolves the
coherent-cycle scale calculation, but not those remaining tasks.
