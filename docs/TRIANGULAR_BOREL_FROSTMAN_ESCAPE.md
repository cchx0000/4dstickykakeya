# Direct Frostman construction for triangular Borel selectors

Date: 2026-10-03. The dimension-three source case through the full Frostman
and dimension-four endpoint is Lean-checked. The subsequent uniform-potential
and direct original heavy-root power/summability statements are also checked
in [the direct charge development](DIRECT_HEAVY_ROOT_CHARGE.md). The low-moment
corollary, approximation interface, and general-dimension notation below
remain independently audited handwritten arguments.
This special case does not add a hypothesis to, or complete, the original
main theorem. No triangularization from packing-three is claimed.

## Theorem and fixed reference

Let Q=I_1 x ... x I_d be a bounded rectangular box, with mu_i equal to
Lebesgue measure restricted to I_i and mu=mu_1 x ... x mu_d. Let sigma be the
ACTUAL original nonzero finite source with sigma<=D mu for finite D. Suppose,
after at most a fixed simultaneous coordinate permutation,

  b_i(a)=f_i(a_1,...,a_i),

with arbitrary Borel f_i, including arbitrary dependence on the own coordinate.
Let J be an interval of positive finite length, and suppose the original
trajectories (b(a)+ta,t) lie in K for sigma-almost every a and every t in J.
For every 0<s<1 an actual positive restriction of sigma x dt|J pushes forward
to a finite nonzero measure supported on K with

  nu(B(z,r)) <= D 2^(1+ds) N^d r^(1+ds)                 (1)

for some finite N fixed before every center and radius. Therefore

  dim_H K >= d+1.

For d=3 this is the dimension-four conclusion for triangular Borel selectors.
No packing assumption is required in this special case.

The product measure mu is ONLY a dominating reference for upper bounds.
The actual source sigma is never replaced by an independent-coordinate law.

## 1. Scalar potential bound, uniform over arbitrary Borel functions

For an interval I, a Borel g:I->R, and x in I define

  V(t,x)=integral_I |g(x)+tx-g(x')-tx'|^(-s) dx'.

For x!=x', factor out |x-x'| and translate the time variable:

  integral_J |g(x)-g(x')+t(x-x')|^(-s)dt
    <= C_s |J|^(1-s)|x-x'|^(-s).

The diagonal is Lebesgue-product null, and

  integral_I integral_I |x-x'|^(-s)dx dx'
       =2 |I|^(2-s)/[(1-s)(2-s)] < infinity.

Thus Tonelli proves

  integral_J integral_I V(t,x) dx dt < infinity,        (2)

with a constant independent of g. All potentials and integrals here are
extended nonnegative measurable functions; infinity at equality is harmless.

## 2. Predictable reference potentials for all coordinates

For prefix z=a_<i put

  F_i(t,z,x)=f_i(z,x)+tx,
  V_i(t,z,x)=integral_(I_i)
          |F_i(t,z,x)-F_i(t,z,x')|^(-s) d mu_i(x').

Each V_i depends only on t and the first i slope coordinates. Apply (2)
for every prefix. Its constant is uniform over the Borel function
f_i(z,·). Integrating the finite product-reference prefix and tail volumes gives

  integral_(Q x J) V_i(t,a_<=i) d mu(a)dt < infinity.

Since sigma<=D mu, the same integral against the ACTUAL sigma x dt|J is finite.
Hence all d potentials are finite for sigma x dt-almost every root.
No conditional-kernel construction, normalization, or mixture estimate is used.

For N=1,2,... define measurable events

  G_i,N={ (a,t): V_i(t,a_<=i)<=N },
  G_N=intersection_(i=1)^d G_i,N.

G_N increases to a full original source/time measure set. In particular some
fixed N has positive original mass on G_N. In fact any target below the total
original source/time mass can be retained by a sufficiently large N.

## 3. Each restricted reference coordinate has a uniform physical ball bound

For every fixed t,z,y,r>0,

  mu_i{ x: |F_i(t,z,x)-y|<=r, V_i(t,z,x)<=N }
       <= N(2r)^s.                                    (3)

If the set is empty this is immediate. Otherwise choose x_0 in it. Every x
in the set has |F_i(x)-F_i(x_0)|<=2r, so

  V_i(t,z,x_0) >= (2r)^(-s) mu_i(the set).

This proves (3). The potential integrates the original reference coordinate;
no renormalization of a small retained set is involved. The bound holds for
all prefixes and times, not just the almost-everywhere good ones.

## 4. Actual-source upper bound by backward reference integration

Fix t and a spatial center y. By genuine measure domination,

  sigma{a: (a,t) in G_N, |F_i(t,a_<=i)-y_i|<=r for all i}
   <= D integral_Q product_i
       1_{V_i<=N} 1_{|F_i-y_i|<=r} d mu(a).

Under the fixed PRODUCT REFERENCE, integrate the last coordinate first.
All earlier factors are independent of that last coordinate because the
selector and potentials are triangular. Bound that inner integral by (3),
then repeat for each preceding coordinate. This gives

  actual restricted spatial mass <= D N^d (2r)^(ds).   (4)

This is the exact point where triangularity is essential. For a general
selector, an earlier output can depend on a later coordinate; the same
backward integration is then invalid. Source domination by a product is
valid for all selectors, but alone does not give (4).

## 5. One original restriction supplies a full-scale supported Frostman measure

Choose the fixed N with positive original joint mass and set

  Lambda=(sigma x dt|J)|G_N,
  nu=(a,t -> (b(a)+ta,t))_# Lambda.

For a spacetime ball B((y,t_0),r), its height projection has length at most 2r.
At each such height, its spatial coordinates lie in the intervals used in (4).
Integrating the unchanged time variable yields precisely (1).

Lambda and nu have positive finite mass. Dividing nu by its one total mass,
if a probability measure is wanted, changes only the displayed Frostman
constant. The restriction keeps the original source, original trajectories,
and actual time coordinate; its support remains in K. The same N works at
every spatial scale. Let s tend to1 to conclude dim_H K>=d+1.

## Formalization interface and scope

The sufficient formal pieces are measurable reference potentials, scalar
Tonelli estimate (2), potential-to-ball bound (3), finite backward product
integration (4), positivity of one cutoff restriction, and pushforward/time
integration (1). This avoids general regular conditional probabilities,
observed-prefix mixture convexity, cross-Riesz Cauchy-Schwarz, and general
measure fiber-dimension theorems. The remaining general sticky problem is
not reduced to triangularity by anything proved here.

## Quantitative corollary and an explicit approximation interface

The potential integral estimates above are uniform over the triangular
functions. There is a finite C=C(s,Q,J), independent of all f_i, such that

  sum_i integral V_i d(sigma x dt|J) <= D C.

Let p=sigma(Q)>0 and ell=|J|>0. Markov and a union bound show that any integer
N>=2 D C/(p ell) retains at least half the original joint mass in G_N.
Thus both the retained mass and the Frostman constant can be chosen uniformly
for all Borel triangular selectors with the same source domination and box.

If an ACTUAL original selector b satisfies |b(a)-f(a)|<=h on sigma-almost
every source, where f is triangular, perform the same reference cut using f
but push forward the unchanged trajectories of b. A radius-r physical ball
for b lies in the corresponding coordinate intervals of radius r+h for f.
The resulting original-front measure therefore obeys

  nu_h(B((y,t_0),r)) <= 2r D N^d [2(r+h)]^(ds).

For r>=h this is <=C' r^(1+ds), with C' uniform in h and f, and nu_h has mass
at least p ell/2. Consequently a sequence h->0 of such uniform approximations
on the SAME positive original source, with the original compact front retained,
would yield a supported Frostman measure by weak compactness. The assertion
also permits varying dominated sources if their masses stay uniformly positive.
No such triangular approximation theorem is derived from packing-three here.

## Actual-source low-moment consequence

The same construction controls the UNMODIFIED slice law, not just the cut.
Let p_Q(t)=((P_t)_# sigma)(Q) for disjoint spatial grid cubes of side r<=1.
Split p_Q=g_Q+b_Q according to G_N and its complement at time t. Put
p=sigma(R^d), the fixed total source mass. Then

  max_Q g_Q(t) <= C N^d r^(ds),
  integral_J sum_Q b_Q(t)dt <= C/N.

The first bound follows from (4), with a dimensional cube/ball constant;
the second is the uniform integral-potential Markov bound. For any theta>0,

  integral_J sum_Q p_Q(t)^(1+theta)dt
    <= 2^theta integral_J [sum_Q g_Q^(1+theta)+sum_Q b_Q^(1+theta)]dt
    <= C [N^(d theta) r^(ds theta)+N^(-1)].

Here sum g_Q<=p, each bad-cell mass<=p, and all actual source/time weights
are retained in the displayed decomposition. There is no independence claim.
Take an integer N comparable to r^(-ds theta/(1+d theta)) to obtain

  integral_J sum_Q p_Q(t)^(1+theta)dt
       <= C r^[ds theta/(1+d theta)].                  (7)

For d=3 and every beta<3, choose s<1 near1 and theta>0 sufficiently small
that 3s/(1+3theta)>beta. Formula (7) then gives summable dyadic original
heavy-root charge at threshold r^beta by the usual size-biased Markov bound.
The exponent approaches 3theta as s->1 and theta->0; no exact endpoint or
fixed-theta sharp exponent is asserted. This is a uniform continuum-time
estimate for arbitrary Borel triangular maps and bounded dominated sources.

## Executed Lean checks

The four modules `scalar_borel_projection_energy`,
`parameterized_scalar_potential`, `triangular_potential_escape`, and
`triangular_borel_front_escape` contain 31 strictly checked theorem declarations.
All readbacks use only `propext`, `Classical.choice`, and `Quot.sound`.
The final `triangular_borel_front_dimH_eq_four` assumes the stated bounded
reference densities, original source domination, Borel triangular data, a
positive actual time interval, and literal original support. It has no energy
or potential-finiteness certificate among its hypotheses.

The targeted build passed 8,714 jobs. Exact hashes and commands are in
`verification/triangular-borel-front-checkpoint.json`. This is a special-class
escape, not a proof that every original sticky selector is triangular. The
original main theorem and its existing WZ-axiom dependency remain unchanged.

## Stronger original-law moment checkpoint

The subsequent [root-tail proof](TRIANGULAR_ORIGINAL_ROOT_MOMENT.md)
formally improves the original root moment to `C r^(3s theta)` for
`0<theta<1/3`, by saturating the potential cutoff and using layer-cake.
It does not replace the actual source by the reference product or normalize
individual retained pieces. The grid estimate (7) above remains a valid
handwritten consequence, but is no longer the strongest checked
original-law estimate.
