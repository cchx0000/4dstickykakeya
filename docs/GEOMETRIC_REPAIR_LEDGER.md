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

This is a sharper candidate than bare support growth from negligible edge
weight. The local split/probability estimates are being formalized. Their
integration into repeated geometric routing, including the common-target
return, is not yet established.
