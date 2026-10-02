# Uniform QStick does not bound the transverse reuse ledger

Date: 2026-10-02. Status: handwritten mathematical countertest, not a Lean
proof. This tests the proposed passage from uniform vertical support entropy,
bounded endpoint density, genuine old contact flags, and preserved old edge
mass to a small global selector union. It is **not** a counterexample to the
Sticky Kakeya theorem or to a branch that additionally excludes every
Frostman exit. Its front contains an open set.

## 1. A compact smooth selector with uniform vertical support count

Put

    L = {a in R^3 : 1/10 <= |a| <= 1/8},
    H = {a in R^3 : 1/4 <= |a| <= 1/3},
    b(a) = -|a|^2 a,       z_a = (a,b(a)),

and use Lebesgue measure on L union H. Normalization changes only fixed
constants. The compact phase carrier is a smooth, bi-Lipschitz graph over two
three-dimensional annuli, so its Hausdorff, packing, and upper box dimensions
are all three. Its direction marginal has bounded density.

On the ball |a| <= 1/3 the map b is 1/3-Lipschitz. Consequently, over every
direction ball of radius delta the graph is covered by O(1) phase balls of
radius delta, uniformly in the center and scale. Equivalently its vertical
branch count is O(1), stronger than C delta^(-zeta) for any zeta > 0. This
support assertion passes to every subsequent subset.

An explicit compact marked-line embedding is

    direction theta(a) = (a,1)/sqrt(1+|a|^2),
    initial point X(a) = (b(a),0),
    line segment {X(a)+t theta(a) : 0 <= t <= 1}.

The physical height parametrization is (b(a)+s a,s). Every height in [0,3/4]
occurs in these unit segments, since 1/sqrt(1+|a|^2) >= 3/sqrt(10) > 3/4.
The marked-line carrier is a smooth three-dimensional compact set. No change
of the original unit-segment convention is needed.

## 2. Exact physical polarized four-cycles

Fix r in [1/10,1/8], s in [1/4,1/3], and u,v in S^2 with
|u dot v| <= 1/2. Consider the ordered four-cycle

    p = r u,       y0 = r v,       q = s v,       y = s u.

Here and below a direction point denotes its actual phase point z_a when
contact or phase spans are discussed. For

    S = r^2 + r s + s^2,

the four successive contact times are

    r^2, S, s^2, S.

These are exact contacts: points of one radius meet at height equal to the
square of that radius, and two points on one radial ray meet at height S.
All times lie in (0,1/4). Three of the labels are distinct with a uniform
Vandermonde lower bound. Indeed

    s^2-r^2 >= 3/64,
    S-s^2 = r(r+s) >= 7/200,
    S-r^2 = s(r+s) >= 7/80.

All four contact secants have slope length bounded below by a fixed positive
constant. Thus this is not a diagonal or vanishing-angular-shell example.

The horizontal plane is exactly E = span(u,v). The fixed anchored horizontal
base has area

    |(a_y0-a_p) cross (a_q-a_y0)|
      = r(s-r)|u cross v| >= (1/10)(1/8)(sqrt(3)/2).

The phase affine span has dimension three, even though its horizontal span
has dimension two. To check this directly, use the coordinates
(a_u,a_v,b_u,b_v) on E plus E, and write d=s-r. The three secants based at p
are

    A = (-r, r,  r^3, -r^3),
    B = (-r, s,  r^3, -s^3),
    C = ( d, 0, -d S, 0).

Replace B by B-A. The determinant of the three rows a_u,a_v,b_u is

    r d^2 (S-r^2) = r s (s-r)^2 (r+s) > 0.

It is bounded below on the displayed parameter ranges. Since |u dot v| <=
1/2, passage from these coordinates to Euclidean phase coordinates has
uniformly bounded inverse. The actual phase three-volume therefore has a
fixed positive lower bound. All four phase points lie in E plus E, with zero
affine offset. This is the genuine non-line polarized, full-phase-rank geometry,
not merely an arbitrarily assigned plane or normal.

The repeated fourth label causes no problem: the three-label Vandermonde
hypothesis uses r^2, S, and s^2.

## 3. Positive-mass old packets and the actual conditional occurrence law

The exact four-tuples above are product-null. To avoid treating a singular
family of witnesses as a positive-mass old flag law, fix a small coarse W,
put epsilon=W/10, and restrict anchor radii to

    r in I_L = [7/64,15/128],
    s in I_H = [9/32,5/16].

Keep the belt |u dot v| <= 1/2. Given p=r u and q=s v, define actual selector
packets

    Y1(p,q) = B(su,epsilon),
    Y0(p,q) = B(rv,epsilon).

For sufficiently small W these balls lie in H and L respectively. They have
actual selector mass (4 pi/3) epsilon^3. Every point of Y1 is an O(W)-contact
neighbor of both p and q, using labels S and s^2; every point of Y0 is an
O(W)-contact neighbor of both p and q, using labels r^2 and S.

For example, the derivative of a -> b(a)+t a has norm at most 1/3+1/4 < 1
on the relevant ball and for these labels. Perturbing a contact endpoint by
epsilon therefore changes its contact residual by less than epsilon. The
three-time separation and phase-rank lower bounds persist for every cycle
p,y0',q,y with y0' in Y0 and y in Y1, once W is small enough. Both packets lie
in the O(W) tube around E plus E. The exact center rv is also an actual
selector point, so it can serve as the fixed anchored reference vertex.

Take a symmetric old contact graph h_W equal to a fixed constant c_0>0
on these edges and supported on a slightly enlarged physical residual
relation. One may choose c_0 so that h_W is dominated by the actual
inverse-time-normalized coarse collision kernel: the contact error has a
fixed margin, the edge directions are uniformly separated, and each contact
time has a fixed margin inside the common time slab. Thus a time interval
of length comparable to W is available on every displayed edge. Use one
packet label per permitted anchor pair, take the packet Y=Y0 union Y1, and
set

    w_{p,q}(z) = 1_{Y(p,q)}(z) h_W(p,z) h_W(q,z)
               = c_0^2 1_{Y(p,q)}(z),
    m(p,q) = integral w_{p,q}(y) d sigma(y)
           = 2 c_0^2 (4 pi/3) epsilon^3.

Restrict the old root to L, using the same root-restriction form as the
source. Its packet mass is

    m_L(p,q) = integral_L w_{p,q}(y) d sigma(y) = m(p,q)/2.

The rooted occurrence measure and its physical marginal have the source's
disintegration algebra:

    dLambda(y,p,q)
      = 1_L(y) w_{p,q}(y) d sigma(y) d sigma(p) d sigma(q),
    N_flag(z) = integral m_L(p,q) w_{p,q}(z) d sigma(p) d sigma(q),
    d kappa_z(y,p,q)
      = N_flag(z)^(-1) w_{p,q}(z) dLambda(y,p,q).

We retain the physical occurrence endpoint in the upper annulus. Consequently
every represented tuple (p,y,q,z) has y in Y0 and z in Y1, so its actual
three-time and full-phase-rank geometry is precisely the one checked above.

The anchor integration is restricted to the stated radii and belt. All
measures here are absolutely continuous restrictions of the actual selector
products; no artificial atomic anchor law is substituted. These are genuine
positive-mass contact-supported, sector-coherent subpacket occurrences with the v078/v080 disintegration algebra. We do not
claim they are the manuscript's complete azimuth-sector packets or a
dyadically retained residual/non-bush layer, nor that this restriction retains
a fixed fraction of such a layer.

For clarity, the two balls are compatible with one projective azimuth sector,
not unrelated angular labels. Let P be orthogonal projection onto
(sv-ru)-perp. Since s Pv = r Pu,

    P(su-ru) = (s-r) Pu,
    P(rv-ru) = -r(s-r) Pu/s.

These are opposite nonzero rays, with lengths bounded below uniformly on the
parameter ranges. They therefore determine the same projective ray, and
the W-thickenings fit in one O(W) projective sector. Its representative
plane can be taken to be span(u,v).

On the fixed inner upper annulus

    Omega = {a : 37/128 <= |a| <= 39/128},

one has N_flag(z_a) comparable to epsilon^6. Indeed the condition
|a-su|<epsilon imposes an angular cap of area comparable to epsilon^2 on u
and an interval of length comparable to epsilon on s. The radius r has a
fixed interval of choices; the permitted belt for v has fixed area. Hence
the permitted anchor-pair measure is comparable to epsilon^3, and the
remaining factor m_L(p,q) is comparable to epsilon^3. These constants are
uniform on Omega. In fact the marginal is exactly constant there:

    N_flag(z_a)
      = c_0^4 (2 pi) (integral_{I_L} r^2 dr) Vol(B(0,epsilon))^2.

To see this, the v-belt has area 2 pi, and the change of variables (s,u) to
su sends s^2 ds d area(u) to Lebesgue measure. The entire epsilon-ball about
a lies in the permitted radial range I_H. Hence the normalized physical
occurrence marginal on Omega is exactly normalized Lebesgue measure.

### Conditional normal cap bound

First integrate out the old root y. For fixed p=r u and radius s, neither
the resulting root factor m_L(p,q), nor the upper packet Y1(p,q) and its
incidence with a prescribed upper endpoint z, depends on the azimuth of v.
Under the resulting anchor marginal of kappa_z, v is therefore uniform on
the spherical belt |u dot v| <= 1/2, conditional on p and s. Write

    v = t u + sqrt(1-t^2)(cos(phi)e1 + sin(phi)e2).

The spherical area element is dt dphi. The normal

    n(p,q) = (u cross v)/|u cross v|

is uniform on the unit circle in u-perp. Every projective angular cap of
radius theta meets such a circle in normalized arclength at most C theta,
uniformly in u and in the center of the cap. For geodesic projective distance,
when theta <= pi/2 this follows from

    |n dot n_*| >= cos(theta)
      => |cos(phi-phi_*)| >= cos(theta),

after projecting n_* onto u-perp. There are at most two circular arcs, of
total length at most 4 theta. Equivalent chordal metrics change only C.
Integrating the conditional bound gives

    kappa_z{[n(p,q)] in any cap of radius theta} <= C theta.

Thus every endpoint in Omega carries genuine old flags with uniformly
diffuse normals. Independent samples of these laws preserve all original
physical occurrences and provide transverse old normals with positive
conditional probability. The normals vary with the anchor pair; this does
not license changing the fixed polarization coordinate inside v064.

## 4. Linear fine edge mass cannot fit a vanishing two-sided selector union

Freeze W and the old law from section 3. For every much finer rho>0, restrict
the physical source to Omega with its original Lebesgue measure mu. For

a=s u and a'=t v define

    h_rho(a,a') = 1_{|s-t| <= c rho} 1_{|u dot v| <= 1/2},

where c>0 is a sufficiently small fixed constant. This is an actual physical
collision graph at error rho, with fixed positive angular separation. Use
collision label ell=(s^2+t^2)/2. Then

    (b(a)-b(a')) + ell(a-a')
      = ((t^2-s^2)/2)(s u+t v),

whose norm is at most C|s-t| <= rho. The label stays in a fixed subinterval
of (0,1/4). Choosing c with slack also leaves a collision-time interval of
length comparable to rho, so the usual inverse-time-normalized actual
residual kernel dominates a fixed multiple of h_rho.

Polar coordinates show, uniformly at every a in Omega (including radial
boundary points),

    c1 rho <= integral h_rho(a,a') d mu(a') <= C1 rho.

The angular belt has fixed positive area and the allowed radial interval has
length between c rho and 2c rho. Hence the total old physical edge mass is
M_rho comparable to rho. For arbitrary measurable A,B contained in Omega,

    Gamma_rho(A x B) <= C1 rho min(mu(A),mu(B)).

Consequently, if Gamma_rho(A x B) >= c0 M_rho for fixed c0>0, both mu(A)
and mu(B) are bounded below by a fixed positive constant. They cannot both,
or even individually, be O(rho^nu) for any nu>0. Appending the genuine
conditional old flags from section 3 does not change this calculation.
Assigning every occurrence to its first source cell also preserves the same
edge law and cannot change this obstruction.

This is a sharp limitation on a *generic* two-sided small-union claim from
QStick, bounded density, and genuine diffuse old flags. It does not assert
that a linear fraction of this fine graph belongs to a new determinant-small
non-bush cycle branch. In fact the dominant approximately equal-radius
interactions correctly lead to physical bushes.

## 5. What the exact v046/v053 reuse count does in this example

In the source, r(chi) counts distinct anchored packets whose endpoint sets
meet the graph cell chi. It does not count the vertical branches above the
direction cube. The distinction persists when the branch count is one.

A polar mesh of size W gives the following transparent discrete ledger.
There are order W^(-3) endpoint cells, indexed by upper radius s and direction
u. A cell near su has packets with anchors

    p=r u,       q=s v,

where r has order W^(-1) choices and v has order W^(-2) choices in the belt.
The resulting anchor pairs are distinct. Each corresponding endpoint packet
Y1 has radius O(W), so it meets only O(1) endpoint cells. Therefore, up to
fixed mesh and boundary constants,

    r(chi) comparable to W^(-3),
    K comparable to W^(-3),
    sum_chi r(chi) comparable to W^(-6),
    (sum_chi r(chi))/K comparable to W^(-3).

Every endpoint cell has two incident packets whose planes are uniformly
transverse: choose the azimuths of v a fixed angle apart. The literal v053
bound with thickness w comparable to W and theta bounded below is therefore
of order W^2 W^(-3)=W^(-1). It is valid but vacuous. The actual direction
union has constant positive mass.

Regrouping by geometric packet pairs improves this crude count but does not
produce a small union. For fixed u, two transverse planes span(u,v1) and
span(u,v2) intersect in the radial line R u. The packet pairs along that ray
can be merged. However, order W^(-2) distinct radial directions are needed
to cover the upper annulus. Each resulting transverse intersection tube has
volume of order W^2 in a bounded annulus. Their aggregate is again of order
one, exactly consistent with the occupied direction union. Uniform QStick
places no bound below W^(-2) on this horizontal family of intersection rays.

## 6. Explicit front exit and the remaining obligation

For height h in (1/2,3/4), the physical front map is

    F(a,h) = ((h-|a|^2)a,h).

Its derivative in a has tangential eigenvalues h-|a|^2 and radial eigenvalue
h-3|a|^2. On H both are uniformly positive when h>1/2. Thus F is a local
smooth diffeomorphism on the interior of H times (1/2,3/4). Its image is an
open four-dimensional set in the original unit front. Restricting to a small
compact interior box gives a direct bounded-density four-dimensional
Frostman measure. The example therefore has the required geometric exit.

The missing implication cannot be obtained by replacing the vertical factor
B with O(1) in v053, by first-source-cell disjointness, or by preserving the
old flags. A successful continuation must use the actual no-Frostman
hypothesis, or an additional quantitative property of the retained
non-bush/rank-loss branch, to control the weighted family of varying
transverse intersection tubes or to charge it directly. It must keep the
original edge/occurrence weights and distinguish support entropy from the
mass of a newly normalized restriction. This note proves no such
no-Frostman implication and imposes no extra assumption on the final theorem.
