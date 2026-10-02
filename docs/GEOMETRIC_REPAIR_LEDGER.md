# Geometric repair ledger

Updated 2026-10-02. The original compact marked main theorem is unchanged.
This file records mathematical tests and remaining proof obligations, not
additional hypotheses silently added to that theorem.

## Established analytic endpoint

`OriginalResidualCriterion.compact_full_direction_residual_reduction` constructs
an actual positive bounded-density slope source inside the original front and
proves that its codimension-two residual bounds imply dimension four. The
source, exact support, singular energy, spacetime dimension gain, and Frostman
extraction are checked in Lean. The geometric estimate is still an explicit
premise of the implication.

This estimate need not hold on every source without an alternative. For radial
lines and a residual-time window containing their common intersection time,
the residual can be identically zero while the front is four-dimensional. The
original residual/Frostman alternative, or the residual estimate under the
contrary low-dimension assumption, is the relevant geometric target.

## Test 1: resampling cannot preserve a uniform product bound for free

Suppose an old graph of mass `M` is transported without losing mass to a
joint law supported where the two direction endpoints are within `2T`, with
transported law dominated by `K (sigma x sigma)`. A cubic original direction
bound gives

```text
M <= 8 K C m T^3,     m = sigma(univ).
```

If `T^3 <= m r^2` and the old graph has power-excess mass
`M >= A m^2 r^(2-eta)`, then

```text
K >= (A / (8 C)) r^(-eta).
```

Thus the required loss is a fixed power, not a constant or an arbitrary
subpower factor. Changing the endpoint law to fit a smaller source cap cannot
be called a coefficient-one product-dominated transport without proving a
new payment mechanism. This numerical test is a consequence of the checked
global terminal band bound; it is not a disproof of the main theorem.

## Test 2: positivity can replace a uniform extraction fraction

For a finite original occurrence, measurable hereditary eligibility and an
eligible positive piece in every positive remainder suffice for a countable
disjoint exhaustive partition. A source marginal `sigma.withDensity f` retains
positive mass on any positive selector piece inside `{f != 0}`. No uniform
lower bound on `f` is needed for this qualitative claim.

The `PositiveRoutingExhaustion` development proves these exact measure
identities. Finite truncation can have any prescribed positive absolute tail,
but this supplies no bound on the number of retained pieces or the number of
geometric rerouting attempts. It does not itself pay a cross-cap ledger.

When a geometric output is positive only in fresh-label space, the required
adapter conditions only those fresh labels on their positive-probability
success event. The base must retain every old endpoint and inherited mark.
`PositiveFlagConditioning` now constructs and verifies this conditional-witness
law, including its hereditary reuse on absolutely continuous suboccurrences.
Positivity of the geometric success event remains a distinct obligation.

## Test 3: union growth needs an aggregate support invariant

If the *whole retained physical selector support* has mass `Q_j>0` and every
union-growth transition gives

```text
Q_(j+1) >= a Q_j,     a > 1,     Q_j <= 1,
```

then each chain terminates, even without a common lower bound on `Q_0`. Its
length may depend on `Q_0`. A summable error allocation such as
`2^(-j) r_0^A` would have one finite budget without a common attempt count.

The displayed transition is an obligation, not a proved property of the
current geometric route. Reversal preserves old edge mass, but selecting one
small bush or degree subfamily afterward can reduce selector support
arbitrarily. All pieces must remain aggregated, or a different monotone
quantity must be proved. For a graph `A x B` with `measure(B) >> measure(A)`,
one reversal grows support; a second lossless reversal returns to `A` and
cannot grow it again. Small-subfamily selection can conceal this obstruction.

The finite-depth cap-contraction identity does not replace this invariant:
below the fixed angular cutoff, all remaining original pairs can be cross-cap.

## Established individual-bush geometric endpoint

A sequence of individual vanishing-error physical bushes, each with the same
positive lower mass bound, now yields
a positive exact bush by compactness and finite-measure reverse Fatou. On a
positive time interval away from that bush's center time, the exact bush has
cubic transverse sublevels and therefore a four-dimensional front by the
checked spacetime/energy machinery. This concrete Frostman exit is now checked in `PositiveBush`; no rate of
bush-mass decay is inferred from it. It does not replace the full vector-family
hypothesis when every individual bush mass tends to zero.

Even after that exit is established, the proof must force either such an exit
or a root-weighted paid/residual bound through the actual inherited routing.
A generic conservation, exhaustion, or independent-label theorem alone does
not supply that geometric forcing step.


## Robust union-growth test under formalization

On a comparable-mass source layer `q <= q_i <= 2q`, write
`e = sum_i e_i`, `w_i=e_i/q_i`, and `N=sum_i w_i`. If the amplified edge mass
satisfies `E=int e >= c B q Q`, split at `N=sqrt(B)`.

- If the low-`N` part carries at least `E/2`, its degree is at most
  `2q sqrt(B)`, so its target support has mass at least `(c/4)sqrt(B)Q`.
  A small relative edge-mass discard gives a corresponding robust lower bound
- Otherwise the high-`N` part carries at least `E/2`; sampling three fresh
  source labels while retaining the inherited one has collision probability
  at most `6/sqrt(B)`, provided the actual conditional source-index law has the
  stated weights

This is sharper than bare support growth from negligible edge weight.
The local split/probability estimates are now strictly checked in
`FourDistinctSources` and `WeightedGrowthStarSplit`. Their
integration into repeated geometric routing, including the common-target
return, is not yet established.

## Root-error test for finer bush returns

The checked no-Frostman consequence now gives uniform *qualitative* small-bush
mass decay over bounded time windows. It supplies no power-law rate.

A finer auxiliary bush does not automatically improve the inherited old pair's
physical collision error. If the old edge has error `r_0`, merging or enlarging
along it retains an error term

```text
O(R + delta_edge + r_0),
```

not `O(R + delta_edge + rho_aux)` merely because the new bush was constructed
at a later failure scale `rho_aux`. Applying a local lemma with its collision
thickness relabeled as `rho_aux` therefore requires a separate restriction or
identity proving that the same original pairs satisfy the finer bound. Fresh
probability labels, source-cap refinement, and exact marginal conservation do
not establish this geometric improvement.

This prevents an immediate use of qualitative small-bush decay to pay a
root-scale quadratic budget: the required small-bush radius may be much below
`r_0`. The issue is distinct from whether `r_0` is smaller than a terminal
source-cap radius such as `r_0^(2/3)`. Any repaired return must keep the old
error explicit or prove why the retained old pairs actually improve it.


## Full vector-family escape now checked

Original normalized open-cap condition (340) now implies an actual supported
Frostman probability through the whole-family physical ball estimate and an
explicit compactness/Portmanteau argument. This covers varying numbers of
bushes and total masses tending to zero. It does not assume a fixed positive
mass in any individual bush. The unresolved geometric task is to obtain the
synchronized vector condition or route its coherent hairbrush failure with
all inherited old errors and weights intact.

## Conditioning and stationary-star density guardrail

Lossless conditioning of a positive fresh-label event preserves the inherited
occurrence marginal and genuine support, but can multiply fresh witness density
by `1/q(success)`. Numerical estimates for the unconditioned cycle/product law
must therefore be reproved or charged after that conditioning. Qualitative
incidence conclusions alone do not preserve a quantitative paid estimate.

On a comparable source layer, sampling the actual aggregate target-conditional
law `p_i=e_i/(sum_j e_j)` has an advantage over the auxiliary law proportional
to `e_i/q_i`: each fresh whole-occurrence marginal is exactly the aggregate old
law **before cuts**. At normalized multiplicity at least 24 its maximal index
atom is at most `2/N`, giving at least one-half probability of four distinct
indices. A later distinctness cut or conditioning does not automatically retain
that fresh-marginal stationarity; the inherited marginal and the fresh marginals
must be audited separately.

Uniformly choosing the next distinguished coordinate before a geometric cut
also preserves the unconditional old law by exchangeability. Its successful
output is an old-law submeasure. Repeating on unused old submeasures is a
possible way to avoid amplifying rare witness densities, and genuine fractional-submeasure exhaustion is now checked. All paid
estimates for the witness joint laws must still be justified explicitly.


## Genuine contact-cycle rigidity and its availability boundary

A physical four-cycle has extra structure absent from an arbitrary 3-plane:
its horizontal and vertical edge sums are zero. If its first three horizontal
edges form an invertible frame, the identity
`sum_(i<3) (t_i-t_3) alpha_i = sum_i collision_error_i`
controls all old edge times without cubic four-time interpolation. Explicit
3x3 adjugate bounds are checked; the physical time and scalar-plane consequence
is now strictly checked with the original errors and times fixed. The time
error is at most `24 M^2 r_0 / Delta`, and the actual graph-plane error is
`6 M^2 r_0 / Delta + 144 M^5 r_0 / Delta^2`.

This does not by itself provide sufficiently nondegenerate rooted cycles.
For two separated radial direction caps of radius
`T=r^((2-eta)/6)`, the cross graph has mass of order `r^(2-eta)` while every
alternating cycle determinant is `O(T^2)`. For the relevant exponents this is
smaller than a mesoscopic `Delta=r^d`, `d<1/6`. The model has a genuine Frostman
exit; it refutes an unconditional nondegenerate-witness shortcut, not the main
theorem. The paper's arbitrary-threshold route still requires actual payment
or Frostman routing of its other alternatives.

Canonical scalar packets attached to an old collision time correctly preserve
physical support, but do not supply the determinant-small new rank-loss packet
or its original weighted anchor/cycle law required by the transverse paid
comparison. They can simplify support bookkeeping; they cannot be relabeled
as those paid-ledger witnesses.


## Actual rooted-cycle witnesses now checked

The bipartite C4 estimate and a bad-edge restriction argument show that almost
every edge of a bounded measurable graph has positive rooted-cycle witness
density. An actual conditioned Markov extension appends only fresh opposite
vertices to the whole inherited occurrence. It preserves all old endpoint,
time, and flag observables, and gives four distinct physical vertices for
diffuse selector laws and a zero-diagonal graph. This supplies real graph
witnesses, but neither a mesoscopic determinant lower bound nor uniformly
bounded conditioned witness density.

Even an exhaustive cycle coupling with every edge marginal equal to the old
law cannot generally retain a bounded four-vertex product density. For a
complete bipartite rectangle of old mass `M`, the cycle support has product
mass `M^2`, so a coupling of total mass `M` requires density at least `1/M`
somewhere. Any paid comparison must therefore control the actual old-edge
charge or the new joint law separately.
