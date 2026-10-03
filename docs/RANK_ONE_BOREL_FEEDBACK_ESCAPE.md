# A nontriangular escape: one arbitrary Borel feedback channel

Date: 2026-10-03. The general-input statement below is a handwritten proof.
The canonical input `v dot a=a1` now has a separate
[complete Lean proof](RANK_ONE_NATIVE_TIME_ESCAPE.md), including arbitrary
linear coupling and actual-time construction. This is a genuine
special-case extension; it is not a triangularization of a general sticky
selector and does not close the original main theorem.

## Statement

Let sigma be a positive finite bounded-density source on a bounded subset of
R^3 and J an actual time interval of positive length. Suppose the original
intercept has the form

  b(a)=c+L a+u f(v dot a),                               (1)

where c,u,v are fixed real vectors, L is a fixed real 3-by-3 matrix, and f is
an arbitrary Borel scalar function. If the corresponding actual trajectories
on J lie in a compact original front K, then dim_H K=4. More precisely, for
every 0<s<1 an actual positive restriction of sigma x dt|J pushes forward to
a finite front-supported Frostman measure of exponent 3+s.

No regularity or packing assumption on the graph of f is needed. Formula (1)
can contain a genuine feedback cycle and need not be simultaneously triangular
in a fixed coordinate frame. In particular this includes cyclic selectors

  b(a)=(f_1(a_2),f_2(a_3),f_3(a_1))

when any two of the three f_i are affine and the remaining one is arbitrary
Borel. Three arbitrary nonlinear feedback functions are not covered.

## 1. Resolve the fixed linear part using actual time

Put M(t)=L+tI. Its determinant q(t) is a monic cubic, so it vanishes at only
finitely many times. For q(t)!=0, let

  w(t)=M(t)^(-1)u,
  k(t)=v dot w(t).

The original physical map P_t(a)=b(a)+ta satisfies exactly

  M(t)^(-1)(P_t(a)-c)=a+w(t)f(v dot a).                 (2)

The cases u=0 or v=0 reduce immediately to an affine map. Otherwise choose a
fixed invertible matrix S whose first row is v, and write Sa=(z,y), y in R^2.
After the same fixed source-coordinate change and the time-dependent output
change S M(t)^(-1), equation (2) becomes

  (z,y) -> (z+k(t)f(z), y+ell(t)f(z)),                  (3)

where ell(t) consists of the last two coordinates of S w(t). This is an
identity involving the unchanged source and unchanged actual time.
The transformed source remains bounded-density on a bounded box.

## 2. Either a shear, or a nonconstant scalar parameter

The scalar function k is rational:

  k(t)=p(t)/q(t),  p(t)=v dot adj(M(t))u,

where deg p<=2 and q is monic of degree3. If p is identically zero, the first
coordinate in (3) is exactly z. The other two coordinates are translations
by a Borel function of z. Sequential Fubini shows that this shear preserves
three-dimensional Lebesgue measure. On a closed actual subinterval avoiding
the finitely many roots of q, the remaining output linear transformations
and their inverses are uniformly bounded. The actual pushforward source/time
law therefore already supplies a positive supported 4-Frostman measure.

If p is not identically zero, k cannot be constant: k(t)->0 at infinity, and
a nonzero rational function cannot be an identically zero constant. Thus

  tau(t)=1/k(t)=q(t)/p(t)

is nonconstant rational. Its poles, zeros and critical points form a finite
set. Choose a nontrivial closed subinterval J' inside the actual interval J
avoiding those points and the roots of q. On J', M(t)^(-1) is bounded,
|k(t)| is bounded above and below positively, and |tau'(t)| is bounded above
and below positively. In particular tau is bi-Lipschitz and monotone on J'.

## 3. Scalar reference potential on the one nonlinear coordinate

Let mu_z be Lebesgue measure restricted to a bounded interval containing the
transformed z-source. Define

  g_t(z)=z+k(t)f(z),
  V(t,z)=integral |g_t(z)-g_t(z')|^(-s) d mu_z(z').

Since

  g_t(z)-g_t(z')=k(t)[f(z)-f(z')+tau(t)(z-z')],

the change of parameter tau and the scalar translated-interval energy bound
give, uniformly in z!=z',

  integral_(J') |g_t(z)-g_t(z')|^(-s)dt
      <= C |z-z'|^(-s).

Consequently integral_(J' x I_z) V(t,z)dt dz<infinity. Actual bounded-density
source domination implies V(t,v dot a)<infinity for sigma x dt|J'-almost every
root. Choose one N with positive actual mass on G_N={V<=N}. The same cutoff
can retain any prescribed fraction below the actual mass on J'.

As in the triangular potential argument, for every t, center z_0 and radius r,

  mu_z{z: |g_t(z)-z_0|<=r, V(t,z)<=N} <= N(2r)^s.      (4)

The original scalar reference is used inside V; there is no conditioned or
renormalized success law.

## 4. Two free coordinates and actual front support

Restrict the ACTUAL source/time measure to G_N and push it by the ORIGINAL
map (a,t)->(P_t(a),t). At each t in J', the output transform S M(t)^(-1) has a
uniform operator bound. An original radius-r spatial ball therefore imposes
three transformed coordinate conditions of radii at most C r.

For fixed z, the two transverse conditions in (3) each restrict a translated
Lebesgue coordinate to an interval of length at most 2C r. Domination by a
fixed product-box reference and integration in y give a factor (2C r)^2.
The remaining z-coordinate and potential cut are bounded by (4), giving

  restricted actual spatial mass <= C' N r^(2+s).

The height coordinate is still the actual t and contributes at most 2r to
any radius-r spacetime ball. Hence the original pushforward measure obeys

  nu(B((x_0,t_0),r)) <= C'' N r^(3+s).

It has positive finite mass and remains supported on K. Normalizing by its
one total mass is optional and only changes the constant. Letting s->1 proves
the dimension-four conclusion.

## Scope boundary

This proof uses one scalar nonlinear channel to reduce the closed feedback
loop to a nonconstant rational time parameter. With two or three independent
nonlinear channels, the reduction gives a coupled nonlinear system; the same
scalar parameter argument no longer applies. In particular the unrestricted
cyclic Borel class remains a substantive open step of the present attempt.
