# Continuum packet capacity audit

Date: 2026-10-03. Handwritten, read-only research note; not Lean-certified.
The original theorem and its hypotheses are unchanged. None of the tests below
is a counterexample to the full front-dimension-deficit branch.

## 1. Exact annular source/time bound

Let sigma <= D Lebesgue_3 be finite, let b be measurable, and fix an actual
original root a. For T,r>0 define

  M_{T,r}(a,t) = sigma{a': T <= |a'-a| <= 2T,
    |b(a')-b(a)+t(a'-a)| <= r}.

For every measurable time set J,

  integral_J M_{T,r}(a,t) dt <= C D T^2 r.                 (1)

Indeed, for each a' in the annulus, put v=a'-a. The set of real t satisfying
|b(a')-b(a)+tv| <= r is either empty or an interval of length at most
2r/|v| <= 2r/T. Tonelli followed by the volume of the annulus proves (1).
No packing hypothesis, disintegration normalization, or independence of
physical slice marginals is used. Integrating the unchanged original root
measure sigma(da) gives the same bound multiplied by sigma(univ).

Consequently for m>0,

  |{t in J: M_{T,r}(a,t)>=m}| <= C D T^2 r/m
                                      = C (D/q)(r/T),
  q=m/T^3.                                              (2)

Thus T^2 r is a real pair-incidence capacity. It does NOT give a root-time
exceptional-set bound C r/T without controlling the actual cap density q.
With only physical heaviness m>A p r^beta, (2) gives
C D T^2 r^(1-beta)/(A p), which need not tend to zero. The same division by
m appears for an unnormalized finite packet sum: it cannot be removed by
renaming the packet's normalized mass.

## 2. Positive-original-root fold test for packet COUNT

Use one fixed smooth selector

  b(a)=(-a_1^2,0,0)

on a bounded cube, with sigma equal to Lebesgue measure there. Choose roots
in a fixed interior box with a_1=u bounded positively away from zero. For
small T, write t=2u+h with T<=h<=2T. If delta=a'_1-u, then

  P_t(a')-P_t(a)=(delta(h-delta), t(a'_2-a_2), t(a'_3-a_3)).

Restrict to |a'-a|<=3T and take 0<r<cT^2. The root-centered physical r-bush
has two slope clusters, one near delta=0 and one near delta=h. Each has
longitudinal width comparable to r/T and two transverse widths comparable
to r. Hence its original sigma-mass satisfies

  c r^3/T <= m(T,r,a,t) <= C r^3/T.                      (3)

The two positive-mass clusters are separated by distance comparable to T,
so the whole bush has a tight angular radius comparable to T. Choosing h
values spaced by a sufficiently large constant times r/T yields
approximately T^2/r distinct far-cluster packets. Each retains a genuine
root-centered bush witness on a coherent time interval of width comparable
to r/T. The near-root clusters can overlap; no disjoint-source assertion is
made for the full bushes. Annular far clusters are the separate packets.

For beta>5/2 choose

  2<kappa<1/(3-beta),  r=T^kappa.

Then T^2/r tends to infinity by a power, while

  m/r^beta >= c T^[kappa(3-beta)-1] -> infinity.          (4)

Thus a fixed smooth packing-three carrier supplies polynomially many
actual thin heavy packets at every root in a set of positive original
source mass. Arbitrarily large fixed heavy coefficients are attained by
making T smaller. This rules out a bounded/subpower packet-count statement
from packing-three and heaviness alone.

It does NOT rule out a weighted continuum bound: the summed coherent
packet widths are comparable to T, summable over geometric T. Equivalently,
their summed proposed capacities are approximately

  (T^2/r)*(T^2 r)=T^4.

The front is four-dimensional: away from t=0 and t=2a_1, the Jacobian of
(a,t)->(b(a)+ta,t) has determinant (t-2a_1)t^2 != 0 on an open set.
This distinction is essential.

## 3. Tensoring time does not improve the supplied occupancy comparison

A witnessed anisotropic packet has slope width T, physical width r, and
coherent time width h=r/T. Its proposed cap/time reference capacity is

  T^3 h = T^2 r.

Suppose the only available compatible occupied isotropic phase-r reference
ball lower bound is mu(B_r)>=c_zeta r^(3+zeta). Tensoring that actual
reference mass with time over an interval of length h supplies only

  c_zeta r^(3+zeta) h = c_zeta r^(4+zeta)/T.

The ratio of the proposed capacity to this certified lower bound is

  c_zeta^(-1) (T/r)^3 r^(-zeta).                         (5)

The factor h cancels. Formula (5) is the distortion yielded by the existing
occupancy estimate; it is not a claim that every actual packet attains that
worst case. A smaller hereditary packet-capacity envelope would require a
new incidence/packing estimate, rather than just tensoring the established
phase reference with Lebesgue time.

## 4. Current exact frontier

Fresh actual time sampled with a bounded Lebesgue-density kernel after a
source restriction chosen from prior history remains in the fixed good-time
set almost surely. Selecting a later fine bush using that time is valid, but
conditioning on its selected branch may concentrate the time law. Neither
(1), physical heaviness, nor the supplied occupied-cell bound removes that
selection/low-density cost. A source-faithful integrated geometric estimate
using the genuine front deficit is still required.
