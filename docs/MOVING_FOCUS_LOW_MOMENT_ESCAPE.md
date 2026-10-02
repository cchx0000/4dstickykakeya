# Moving-focus low moments with the original source

Date: 2026-10-02. Status: the low-moment and low-center-entropy arguments
in Sections 1--7 are independently checked handwritten proofs. A separate
finite-energy proof of the fixed-center/reference-line escape is now
Lean-certified, as described in Section 9. The exact-null and uniform-decay
consequences in Section 8 also have an original-data implementation.
These are sufficient geometric escape classes, not a proof of the general
Sticky Kakeya theorem or its missing general moment estimate. No new axiom
or final hypothesis is added. The source, selector, physical times, and
supported front remain the original ones throughout.

## 1. Statement on a fixed slope annulus

Fix a finite Borel source `sigma` with

    sigma <= D Lebesgue_3,    sigma(R^3) = m,
    supp sigma subset {a : kappa <= |a| <= R},

where `0 < kappa <= R`. Let `J subset [-T,T]` be an interval, and let
`tau` be an arbitrary measurable function with `|tau| <= U` on this source.
No continuity, differentiability, dimension bound, or condition on the
distribution of `tau` is assumed. First consider

    b(a) = c_0 - tau(a) a,
    Pi_t(a) = c_0 + (t-tau(a)) a,
    mu_t = (Pi_t)_# sigma.

For every `0 < theta < 1/3`, and for a fixed cubic spatial grid of side `r`,

    S_r(sigma) := integral_J sum_Q mu_t(Q)^(1+theta) dt

satisfies, for sufficiently small `r`,

    S_r(sigma)
      <= C [D^theta m r^(3 theta) log(C/r)^theta
             + m^(1+theta) r].                         (1.1)

The factored constant in (1.1) can depend on `theta,kappa,R,T,U`, but not on
`D`, the measurable choice of `tau`, the constant center `c_0`, the scale,
or the source mass `m`. In particular, for a probability source,

    S_r <= C_eta r^((3-eta)theta)  for every eta > 0.    (1.2)

The corollary constant `C_eta` may also depend on `eta` and `D`; for an
unnormalized source it may additionally depend on its total mass. This
distinguishes the constants in a subpower corollary from the explicitly
factored constants in estimates such as (1.1) and (4.3).

The permissible collapse time may vary arbitrarily with the slope. This
strictly removes the common focus-time assumption of the simple radial test.
Packing dimension of the phase carrier is not used in (1.1).

A positive bounded-density source can always be restricted once to a fixed
annulus of positive mass: the origin has zero source mass, and the union of
the annuli `{1/n <= |a| <= R}` exhausts the nonzero slopes. If `b` is bounded
and the center is fixed, the identity above bounds `|tau|` on that annulus.
This restriction is chosen once, before any fine scale.

## 2. Two elementary estimates

### Collision-time length

For distinct slopes `a,a'` and arbitrary intercepts `b,b'`,

    |{t in J : |b'+t a' - b-t a| <= epsilon}|
        <= 2 epsilon / |a'-a|.                         (2.1)

Indeed an affine line traverses a Euclidean ball in an interval of at most
its diameter divided by its speed. The diagonal `a'=a` has zero source mass.

### The two-cap kernel integral

For a root `a` with `0 < |a| <= R`, let `C_delta(a)` be the union of the
angular caps of aperture at most `delta` about **both** `a/|a|` and
`-a/|a|`, intersected with the slope ball of radius `R`. For `0<delta<=1`,

    integral_(C_delta(a)) |a'-a|^(-1) da'
        <= C R^2 delta^2 log(2/delta).                 (2.2)

One may replace the two caps by the larger cylinder of radius `R delta`
around the line `R a`. In cylindrical coordinates relative to that line,
the integral is bounded by

    integral_(|y|<=R delta) integral_(-2R)^(2R)
        (s^2+|y|^2)^(-1/2) ds dy.

The inner integral is at most `C log(2R/|y|)`, and its integral over the
two-dimensional disk is `O(R^2 delta^2 log(2/delta))`. This also proves the
bound with any fixed enlargement of the cap aperture, by changing constants.

## 3. Moving radial-time proof

The constant center cancels from collisions. For the original source define

    B_epsilon(a,t) = sigma{a' :
       |(t-tau(a'))a' - (t-tau(a))a| <= epsilon}.

Fix a root `a`. On the near-focus set

    |t-tau(a)| <= 4 epsilon/kappa,

the time length is at most `8 epsilon/kappa`, and `B_epsilon <= m`. Therefore

    integral_(near focus) B_epsilon(a,t)^theta dt
        <= (8/kappa) epsilon m^theta.                 (3.1)

For the rest, use dyadic bands

    I_h(a) = {t in J : h < |t-tau(a)| <= 2h},
    h >= 4 epsilon/kappa.

Their lengths are at most `2h`. A collision at such a time has root image
`y=(t-tau(a))a` of length at least `kappa h`, and leaf image
`z=(t-tau(a'))a'` within `epsilon` of `y`. Thus `|z| >= |y|-epsilon`, and
the line spanned by `a'` makes angle at most `C epsilon/(kappa h)` with the
line spanned by `a`. Either sign of `t-tau(a')` is allowed: this is exactly
why **both** angular caps are retained.

Consequently all such leaves lie in one root-and-band-dependent set

    C_(C epsilon/(kappa h))(a),

which is independent of the actual time within the band. Using Tonelli,
(2.1), horizontal density, and (2.2),

    integral_(I_h(a)) B_epsilon(a,t) dt
      <= 2 epsilon integral_(cap) |a'-a|^(-1) d sigma(a')
      <= C D epsilon^3 h^(-2) log(C/epsilon).          (3.2)

The constants in the last line include the fixed annulus parameters. The
logarithm can be bounded uniformly as shown because
`h <= H := 1+T+U`. Bands where the displayed aperture is comparable to one
obey the same bound after changing its fixed constant.

Concavity, or Holder with exponents `1/theta` and `1/(1-theta)`, gives

    integral_(I_h(a)) B_epsilon(a,t)^theta dt
      <= |I_h(a)|^(1-theta)
           (integral_(I_h(a)) B_epsilon(a,t) dt)^theta
      <= C D^theta epsilon^(3 theta)
           h^(1-3 theta) log(C/epsilon)^theta.         (3.3)

Since `1-3 theta>0`, the sum of `h^(1-3 theta)` over these dyadic bands up
to `H` is bounded by `C_theta H^(1-3 theta)`, independently of epsilon.
Combining with (3.1) and integrating against the **original root law** gives

    integral_J integral B_epsilon(a,t)^theta d sigma(a) dt
      <= C [D^theta m epsilon^(3 theta) log(C/epsilon)^theta
             + m^(1+theta) epsilon].                 (3.4)

This is valid for every unnormalized source component with the same density
bound and annulus parameters. In particular its first term is linear in the
component mass, not independent of that mass.

For the exact grid transfer, take half-open cubes, so each image belongs to
one cube `Q_t(a)`. Then

    sum_Q mu_t(Q)^(1+theta)
      = integral mu_t(Q_t(a))^theta d sigma(a)
      <= integral B_(sqrt(3)r)(a,t)^theta d sigma(a).

No translated grid or new measure is substituted. Applying (3.4) proves
(1.1). Because `3 theta<1`, the term `r` is bounded by `r^(3 theta)` at
small scales; the logarithm is smaller than every negative power of `r`.
This proves (1.2).

The critical value `theta=1/3` also gives a subpower estimate, with the above
proof yielding `S_r <= C r log(C/r)^(4/3)`: the dyadic band count introduces
one extra logarithm. We do not need that endpoint. For `theta>1/3`, even one
common radial focus has an order-`r` contribution, so the asserted
`r^(3 theta-o(1))` behavior cannot hold in general.

### A fixed reference spacetime line

The same handwritten argument applies if each source trajectory focuses at
its own time on one fixed affine spacetime line. More precisely, suppose

    c(a) = c_0 + tau(a) v,
    b(a) = c_0 + tau(a) v - tau(a) a,

where `v,c_0` are fixed and `tau` is arbitrary measurable and bounded. Set
`a_tilde=a-v`. The fixed affine spacetime change

    (x,t) -> (x-tv-c_0,t)

turns the actual trajectory into

    Pi_t(a)-tv-c_0 = (t-tau(a)) a_tilde.

Translation of the source preserves its density bound and mass. A fixed
positive source can be restricted once to an annulus about `v`, because the
single slope `a=v` is null. Thus (1.1) applies with the translated annulus
parameters. Alternatively, the small-slope argument in Section 5 applies
when its boundedness assumptions hold.

At each fixed time the spatial change is only a translation, so distances
between actual images are unchanged. The cube-to-ball estimate above
therefore gives the moment bound for the original fixed spatial grid too;
there is no need to assert that a time-dependent grid translation preserves
the exact grid moment. The spacetime map is invertible and bi-Lipschitz, and
the result transfers back to the literal original supported front. Notice
that the untransformed center image can be one-dimensional in this example;
the fixed-line extension is not limited to zero-entropy center images in
the initial coordinates.

## 4. A low-entropy image of moving centers

Now suppose, on the same fixed annulus,

    b(a) = c(a) - tau(a) a,

where `c` and `tau` are measurable, `c` has bounded image, and `|tau|<=U`.
Let `N(r)` be the number of cubic `r`-cells needed to cover the literal
center image `c(A)`, where `A` is this fixed source. Equivalently, any
cover by sets of diameter `O(r)` with bounded overlap constants suffices.

Partition the original source into the measurable preimages `A_j` of these
center cells. Put `sigma_j=sigma|A_j`, `m_j=sigma(A_j)`, and let `mu_(j,t)`
be the projection of this restriction by the **actual** map `Pi_t`. Empty
components can be discarded. These are scale-dependent proof partitions,
not scale-dependent choices of the source or selector.

Within one center cell, freezing its center to a constant changes each image
by `O(r)`. More directly, if two actual images are in the same spatial
`r`-cube, then

    |(t-tau(a'))a' - (t-tau(a))a|
      <= |Pi_t(a')-Pi_t(a)| + |c(a')-c(a)|
      <= 2 sqrt(3) r.

Thus the same exact grid transfer bounds the component moment by (3.4)
with collision radius `2 sqrt(3)r`. Uniformly in `j`,

    S_r(sigma_j, actual Pi)
      <= C [D^theta m_j r^(3 theta) log(C/r)^theta
             + m_j^(1+theta) r].                     (4.1)

Writing `M=sum_j m_j`, summation loses **no factor N**:

    sum_j S_r(sigma_j, actual Pi)
      <= C [D^theta M r^(3 theta) log(C/r)^theta
             + M^(1+theta) r],                       (4.2)

since `sum_j m_j^(1+theta) <= M^(1+theta)`. Recombining overlapping spatial
images uses only the explicit convexity cost

    (sum_j p_j)^(1+theta) <= N(r)^theta sum_j p_j^(1+theta).

Therefore

    S_r(sigma, actual Pi)
      <= C N(r)^theta
          [D^theta M r^(3 theta) log(C/r)^theta
             + M^(1+theta) r].                       (4.3)

In particular, if the **one fixed literal center image** has subpower covers,

    for every epsilon>0, N(r) <= C_epsilon r^(-epsilon),

then, for every `eta>0`,

    S_r(sigma, actual Pi) <= C_eta r^((3-eta)theta).    (4.4)

For example use epsilon `eta/2` in the center cover and absorb the logarithm
into `r^(-eta theta/2)`. No source mass is repeatedly discarded.
The constant in (4.4) can depend on the density, total mass, and the relevant
center-cover constants `C_epsilon`, in addition to the fixed geometric
parameters and exponents.

If instead the center image has **packing dimension zero**, one fixed
positive restriction suffices to reach the preceding subpower condition.
For each integer `k>=1`, use a countable cover of the center image by sets
with upper box dimension at most `1/k`. Take their closures (which preserve
covering exponents) to make the preimages measurable. A finite subunion has
source mass at least `M-M 2^(-k-2)`. Intersect these finite subunion preimages
over all `k`. The resulting fixed source has mass at least `3M/4`, and its
center image is contained, for every `k`, in a finite union of upper-box-
dimension-at-most-`1/k` sets. It therefore has upper box dimension zero.
This restriction and the annulus restriction are made once, before scales.

## 5. Optional removal of the annulus

The preceding proof also works without first discarding small slopes when
`|a|<=R` and `|tau(a)a|<=B_0`. For each nonzero root put `rho=|a|`, replace
`kappa` in the near-focus threshold by `rho`, and take

    H_rho = 1+T+B_0/rho.

The logarithm stays uniformly bounded by `log(C/r)`, because
`rho H_rho <= R(1+T)+B_0`. Before integrating roots, (3.4) is replaced by

    integral_J B_r(a,t)^theta dt
      <= C [m^theta r/rho
           + D^theta r^(3 theta) log(C/r)^theta
               rho^(-2 theta) H_rho^(1-3 theta)].     (5.1)

All displayed root weights are integrable against a bounded-density source:

    rho^(-2 theta) H_rho^(1-3 theta)
      <= (1+T)^(1-3 theta) rho^(-2 theta)
           + B_0^(1-3 theta) rho^(theta-1),

and `rho^(-1)`, `rho^(-2 theta)`, and `rho^(theta-1)` are locally integrable
in three dimensions. The root `a=0` is null. This proves the same subpower
conclusion with constants depending on `D,R,T,B_0` and the total mass.

For the center partition the bound `|tau(a)a|<=B_0` is uniform when both
`b` and `c` are bounded. The weighted root integrals in (5.1) add exactly
over the components; the near-focus factor satisfies `m_j^theta<=M^theta`.
Thus the extension still loses only `N(r)^theta`, rather than an additional
linear factor in the number of center cells. The simpler annulus proof
already suffices for a fixed-positive-source escape.

## 6. Supported-front consequence and scope

Assume the fixed source has **positive mass** and the common marked interval
has **positive length**. For a source whose literal marked front is contained
in the original compact front `K`, all the restrictions above are still
supported on `K`. Applying
the root-weighted moment-to-heavy-event inequality in
`SCALAR_PENCIL_PROJECTION_AUDIT.md`, (4.4) gives, whenever `beta<3` and
`eta<3-beta`,

    (sigma x dt){mu_t(B(Pi_t(a),r)) >= r^beta}
      <= C r^((3-beta-eta)theta).

These probabilities are summable on dyadic scales. The rooted recurrence
from a literal front deficit, recorded in
`ROOTED_TIME_RECURRENCE_FRONTIER.md`, then excludes `dim_H K<4`. Equivalently,
the Borel--Cantelli consequence gives the appropriate lower local dimensions
for the actual projected laws and their source-time pushforward. The escape
does not add a separate full-dimensional front.

The new sufficient class allows arbitrary moving focus times and a fixed
subpower-entropy image of focus centers. It covers fractal concentration in
`tau`; such concentration alone is not a counterexample to the low moment.
It does **not** derive low center entropy from phase packing dimension three,
from horizontal density, or from the absence of a Frostman measure. For a
general selector, choosing `tau=0` merely sets `c=b`, whose image need not
have small entropy. No construction of a suitable `c,tau` for general sticky
data has been established here.

### A smooth packing-three graph without zero-entropy centers

The limitation is substantive even before any hypothetical front deficit.
Let `L=diag(1,2,3)` and take `b(a)=La` on a bounded positive-volume slope
set, with compact phase carrier obtained by restricting this linear graph
to a containing compact cube. That carrier is smooth and has packing
dimension three.

There is no positive-volume source restriction `E` and bounded measurable
`tau:E->R` for which

    c(a) = (L+tau(a) I)a

has an image `C=c(E)` of upper box dimension zero. To see this, write the
diagonal entries as `lambda_1=1, lambda_2=2, lambda_3=3`. Away from the three
values `tau=-lambda_i`, the slopes satisfy

    a_i = c_i/(lambda_i+tau),    i=1,2,3.

Partition the bounded time range into countably many regions with a
positive lower bound on all three denominators. On each region this
reconstruction is a Lipschitz map of a subset of `C x [-U,U]`. That product
has upper box dimension at most one, so each such slope image has Hausdorff
dimension at most one.

At `tau=-lambda_j`, the coordinate `a_j` is free within the bounded slope
range, while each other coordinate is determined by
`a_i=c_i/(lambda_i-lambda_j)`. This part is also a Lipschitz image of a subset
of `C` times one bounded interval, hence has Hausdorff dimension at most one.
The full set `E` is a countable union of these pieces and therefore has
Hausdorff dimension at most one, contradicting its positive three-volume.

Since positive bounded-density source mass implies positive three-volume,
the obstruction applies to every positive source restriction. It shows that
phase packing dimension three alone does not force the zero-entropy-center
representation. This does **not** exclude a separate dichotomy using an
additional hypothetical front deficit, nor does it obstruct the moment
estimate for this smooth linear example. The moving-focus class cannot
simply replace all other geometric branches.

## 7. Conditional comparison with finite tube-overlap bounds

This section is a separate elementary reduction, not an invocation or proof
of a Kakeya estimate. It explains the strength of a proposed counterexample
to the unrestricted projected-moment target.

Let an arbitrary bounded selector `b(a)` and bounded-density source be given,
with slopes in a fixed bounded chart and times in `J`. At scale `r`, partition
slopes into cubic `r`-cells `C_i`, of masses `m_i<=D r^3`, and choose their
grid centers `v_i`. Independently choose one intercept `B_i` from the actual
conditional law of `b(a)` on each nonempty cell. Moving a slope to `v_i`
changes its trajectory by at most `T sqrt(3) r` throughout `J`.

For a spatial grid cube `Q` with center `x_Q`, choose a fixed sufficiently
large `K` depending only on the slope chart and time interval. Then

    mu_t(Q) <= sum_i m_i Pr{|B_i+t v_i-x_Q|<=K r}.

For `q=1+theta`, Jensen and `m_i<=D r^3` bound its qth power by

    D^q r^(3q) E[(sum_i 1_{|B_i+t v_i-x_Q|<=K r})^q].

Enlarge `K` by a fixed amount. Every `x` in `Q` then dominates the indicator
at its center with the smaller radius. Integrating over the cube, summing
the grid, and integrating time gives the exact inequality

    S_r <= D^q r^(3theta)
       E integral_(J x R^3)
          (sum_i 1_{|x-B_i-t v_i| <= (K+sqrt(3))r})^q dx dt.   (7.1)

The `v_i` are r-separated and there are `O(r^(-3))` of them. The fields in
(7.1) are ordinary thickened unit-length tube overlaps in a bounded slope
chart; fixed radius and separation constants can be absorbed by a finite
coloring and fixed rescaling.

Consequently a uniform subpower bound on these unweighted tube-overlap
integrals would imply the proposed moment estimate for **every** bounded-
density selector, with no packing assumption. Conversely a polynomial
violation by any one fixed selector would, at its bad scales, produce finite
tube placements violating the corresponding subpower overlap bound. This
does not prove that bound, assert its present literature status, or prove an
equivalence with every formulation of the Kakeya maximal conjecture. It does
show why arbitrary abstract measure concentration is not by itself a valid
counterexample satisfying the selector and horizontal-density constraints.

## 8. Exact reference hairbrushes and uniform qualitative decay

This is a further **handwritten, not Lean-certified** consequence of the
moving-focus escape. It is a necessary condition under a hypothetical
strict front deficit, not a closing power estimate.

Fix one finite source `sigma<=D Lebesgue_3` with bounded slope support and a
Borel selector `b`. Assume its phase graph is contained, up to a source-null
set, in a compact phase carrier `Gamma`. Let `J` be the one common marked
interval, with `|J|>0`, and suppose the literal source-time pushforward

    (a,t) -> (b(a)+t a,t),    (a,t) distributed by sigma x dt|J,

is supported on the original compact front `K`. Assume

    dim_H K < 4.                                        (8.1)

A completed-measurable selector can be replaced by a Borel version on a
source-null set; none of the mass or supported-measure conclusions changes.
No new source is chosen as the transverse error tends to zero.

Let `I` be any fixed **nonempty compact collision-time set**, and let
`T_I=max_{tau in I}|tau|`. It need not be contained in the marked interval
`J`. For phase points `z=(a,b)` and `z_0=(a_0,b_0)`, define

    d_I(z,z_0) = min_(tau in I) |b-b_0+tau(a-a_0)|,
    H_r(z_0) = {a : d_I((a,b(a)),z_0) <= r}.            (8.2)

The minimum exists by compactness of `I`. Each `H_r(z_0)` is measurable.
In particular `H_0(z_0)` is the exact reference hairbrush, allowing each
source line to have its own collision time.

### Every fixed reference has zero exact hairbrush mass

Under (8.1), for **every fixed** `z_0` in phase space,

    sigma(H_0(z_0)) = 0.                                (8.3)

The reference need not itself belong to the selected graph or its carrier.
Suppose instead that this mass were positive. The single slope `a=a_0` is
source-null by horizontal absolute continuity. Away from that slope, the
exact collision time is unique and is the measurable function

    tau(a) = -(b(a)-b_0) dot (a-a_0) / |a-a_0|^2.      (8.4)

On `H_0(z_0)` it belongs to `I` and satisfies

    b(a) = b_0 - tau(a)(a-a_0).                        (8.5)

Exhausting the nonzero translated slopes by annuli supplies one fixed
positive source restriction with `kappa<=|a-a_0|<=R_0`, for suitable fixed
`kappa>0` and finite `R_0`. Its translated source in `v=a-a_0` still has
density at most `D`, and `|tau|<=T_I` uniformly.

The fixed affine spacetime shear

    S_(a_0)(x,t) = (x-t a_0,t)

sends these actual source trajectories to

    (b(a)+t(a-a_0),t) = (b_0+(t-tau(a))v,t).           (8.6)

This is precisely the moving radial-time class proved in Sections 1--3,
with one fixed center `b_0` and arbitrary bounded measurable focus times.
The restricted source-time law remains supported on `S_(a_0)(K)`. The
shear is bi-Lipschitz and that front is compact, so it has the same Hausdorff
dimension as `K`. Section 6 forces its dimension to be four, contradicting
(8.1). This proves (8.3).

Thus positive-mass exact hairbrush escape does not require synchronizing
all source lines to one common collision time. The same fixed source
restriction and its original marked slab suffice. Packing dimension three
is not used in this particular necessary consequence.

### Uniformity over a compact reference range

Let `Z` be any fixed nonempty compact range of reference phase points; it
may in particular equal the original compact carrier `Gamma`. Then

    lim_(r down to 0) sup_(z_0 in Z) sigma(H_r(z_0)) = 0.   (8.7)

Here is the continuity and compactness argument, including its uniformity.
For `z=(a,b)`, `w=(abar,bbar)` and reference points `z_0=(a_0,b_0)`,
`w_0=(abar_0,bbar_0)`, comparison at the same candidate time gives

    |d_I(z,z_0)-d_I(w,w_0)|
      <= |b-bbar| + |b_0-bbar_0|
           + T_I (|a-abar|+|a_0-abar_0|).             (8.8)

Thus `d_I` is jointly continuous; more particularly it is Lipschitz in the
reference, with a modulus independent of the source phase point. The latter
fact is stronger than the uniform continuity supplied by compactness of
`Gamma x Z`.

If (8.7) failed, there would be a positive `epsilon`, scales `r_n` tending
to zero, and references `z_n in Z` with
`sigma(H_(r_n)(z_n))>=epsilon`. Pass to a subsequence with `z_n->z_* in Z`
and put

    delta_n = |b_n-b_*| + T_I |a_n-a_*|.

Equation (8.8) yields the source-set inclusion

    H_(r_n)(z_n) subset H_(r_n+delta_n)(z_*).           (8.9)

Since `r_n+delta_n->0`, finiteness of `sigma` and continuity from above of
the sets `{d_I((a,b(a)),z_*)<=s}` as `s` decreases to zero force the
right-hand masses to tend to `sigma(H_0(z_*))=0`, contradicting epsilon.
This proves (8.7). The source carrier's compactness is compatible with all
the stated original hypotheses; the stronger reference-Lipschitz bound
shows that the final uniformity step itself only needs a finite source and
a compact reference range.

This conclusion is uniform even if the reference point varies with scale.
It establishes only **qualitative** decay for the one fixed source and
collision-time window. No polynomial modulus, comparison with the shrinking
heavy-bush threshold `r^beta`, or summable bound on the actual rooted
heavy-event probabilities is established. In particular, (8.7) is not the
general quantitative closure required by the original argument.


## 9. A finite-energy route after one actual off-focus restriction

The moving-focus escape can also be proved without building a general Renyi
moment API. On a positive annular source choose a fixed `g>0` smaller than
one quarter of the marked-slab length, and retain the actual source/time pairs
with `|t-tau(a)|>=g`. This measurable restriction has positive mass: for
each a it removes at most `2g` of time. It is not a new product source or a
replacement focus time.

For a spacetime pair collision of radius r, bounded slopes reduce its leaf-
time fiber to length at most `2r` and its same-time spatial error to `O(r)`.
At a retained root, the leaf slope lies in a radius-`O(r/(kappa g))` tube
around the original root line, independently of time. The remaining time
fiber contributes `O(r)/|a-a'|`.

The actual weighted tube estimate now has a Lean-checked proof in
`line_tube_inverse_potential`: for every `0<epsilon<1`, unit-supported
`sigma<=volume`, any affine line through the root a, and `0<delta<=1`,

    integral_(line tube of residual width 2delta) |x-a|^(-1) d sigma(x)
       <= 81 (4pi/3) (1+1/epsilon) delta^(2-epsilon).

The infinite value at x=a is retained, and its source mass is proved zero.
A shifted scalar grid gives local tube mass `O(delta^2 s)`, while the cubic
source bound gives `O(s^3)`. Interpolation

    min{s^3,delta^2 s} <= delta^(2-epsilon) s^(1+epsilon)

and quantitative layer cake prove the displayed inverse-potential bound.
Thus the retained actual spacetime law has pair-collision sublevels
`O_epsilon(r^(4-epsilon))`, leading to finite energy at every exponent below
four and a supported Frostman escape by the existing analytical lemmas.

The `moving_focus_energy_escape` and `affine_focus_energy_escape` modules
prove the actual pair-sublevel estimate, finite energies at every exponent
below four, supported Frostman measures, and dimension four on the literal
original support. Their final wrappers allow the given selector to agree
with the representation only almost everywhere. No sublevel/potential bound
is a premise of those final statements, and the measurable focus-time map
need not be bounded.

The `hairbrush_compact_decay` module proves the existential contact relation
closed and its compact-reference measure limit. The
`no_frostman_uniform_hairbrush` module combines this with the actual affine
escape: a front dimension deficit forces exact-null for every reference,
then uniform qualitative maximum-row decay. Its original-data endpoint
constructs one fixed positive source from `IsStickyDatum` before either the
compact reference family or the compact collision window is chosen.
The full general sticky closure remains unproved; the low-entropy-center
extension of Section 4 has not been silently counted as Lean-certified.


## 10. Uniform qualitative decay does not supply a power rate

The necessity of a further geometric argument is already visible on a smooth
packing-three source. On the unit slope ball with ordinary Lebesgue measure,
fix a unit vector e and set

    b(a)=f(|a|)e,    f(s)=exp(-1/s^2) for s>0, f(0)=0.

This graph is smooth, has a bounded Lipschitz constant, and has a compact
packing-three carrier with uniform reference regularity. For every reference
`(a_0,b_0)`, its exact variable-time hairbrush is null. Indeed, contacts with
`t!=0` put a in the fixed affine plane
`a_0+span{b_0,e}`, of dimension at most two. Contacts with `t=0` require
`f(|a|)e=b_0`; strict radial monotonicity makes this a sphere, the origin,
or the empty set, each of three-volume zero.

Thus it satisfies pointwise exact-null and the compact-uniform decay
conclusion of Section 8. But for the reference `(0,0)` and any window
containing zero, its residual-r hairbrush contains the ball

    |a| <= (log(1/r))^(-1/2).

Its mass is at least a fixed multiple of `(log(1/r))^(-3/2)`, larger than
every positive power of r at small scales. No uniform power modulus follows
from exact-null, compactness, bounded direction density, or even smooth
minimal phase packing alone.

The example has a genuine four-dimensional front: at almost every source
point, `det(Db(a)+tI)` is a monic cubic in t, and the smooth spacetime map
is locally nonsingular for almost every time. It therefore does not satisfy
the hypothetical front deficit and does not refute the intended main
alternative. A complete proof must still use that deficit collectively,
or identify an actual escape, instead of upgrading qualitative decay to a
numerical root-weighted budget without a new argument.
