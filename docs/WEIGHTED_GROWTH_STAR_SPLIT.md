# Robust target growth or a linear distinct-source star

Date: 2026-10-02. Status: elementary weighted improvement to the internal
same-window amplification step. It does not prove the global cross-cap
payment or a monotone quantity across arbitrary bush returns.

## Inputs on one source-mass layer

Let `S_i` be finitely many disjoint source pieces, of selector masses
`q <= q_i <= 2q`, with `q>0`. Their old occurrence measures satisfy
`Gamma_i <= (sigma|S_i) x sigma`. Write their target densities as

    e_i(zeta) = d(target Gamma_i)/d sigma,
    w_i=e_i/q_i,       N=sum_i w_i,       e=sum_i e_i,
    Q=sum_i q_i,       E=int e d sigma.

Then `0<=w_i<=1` and `qN<=e<=2qN`. Suppose the amplified alternative supplies

    Gamma_i(univ) >= c B q_i^2

with a common `c>0`. Put `B=K^2`, `K>=12`. Summation and `q_i>=q` imply

    E >= c K^2 q Q.

All quantities here are the original absolute occurrence weights. Source
indices and their fiber laws are retained, rather than replaced by unweighted
support overlap.

## Exact weighted split

Let `L={N<=K}` and `U={N>K}`. At least one carries at least half of `E`.

### Low multiplicity: robust growth

On `L`, the actual target marginal density satisfies `e<=2qK`. Hence any
submeasure `nu` of the low-multiplicity target marginal, supported on `H`,
satisfies

    nu(univ) <= 2qK sigma(H).

If the low part has mass `E_L>=E/2` and `nu(univ)>=(1-epsilon)E_L`, then

    sigma(H) >= (1-epsilon)c K Q/4.                 (1)

For fixed `epsilon<1` and sufficiently large `K`, this is genuine selector
support growth. Crucially it remains true after retaining any such portion
of the low-multiplicity edge mass. It does not rely on extremely small
weights being counted as large unweighted support.

The Lean module `weighted_growth_star_split` proves the pointwise density
bound, its measure domination, (1), the amplification sum, and the exact
low/high half-mass dichotomy. It keeps the low-set measurability and original
measure domination explicit.

### High multiplicity: retain the old index and sample three new ones

Fix one old occurrence of source index `i` and target `zeta` in `U`.
Sample three fresh indices independently with probability

    p_j(zeta)=w_j(zeta)/N(zeta).

Every atom is at most `1/N<1/K`. Keep the original `i` fixed. Among the four
indices there are three possible collisions with `i` and three collisions
between the fresh draws. Each has probability at most `1/K`: for two fresh
draws, `sum_j p_j^2 <= (max_j p_j)sum_j p_j <=1/K`.

The union bound therefore gives

    P(all four source indices are distinct) >= 1-6/K >=1/2.    (2)

If the high branch carries `E_U>=E/2`, the distinct-source extension retains
at least `E/4` of the original occurrence mass. It is linear in `E`; no
`E^4` loss was introduced. Condition each new source point on its chosen index
and the same actual old target, using the genuine disintegration

    Gamma_j(dz,dzeta)=e_j(zeta) K_{j,zeta}(dz) sigma(dzeta).

Every sampled edge is then an actual old edge. All old conditional flags may
remain attached. This source-fiber construction and its physical incidence
must be included in a full geometric implementation; a probability theorem
about indices alone does not establish them.

## Why bare support growth is insufficient

The source's target-union alternative can be simultaneously true with a very
large common-target star. Its union support need not be stable under a tiny
edge-mass discard.

For example let `B` be a large integer, total source mass `Q=B^-1`, and
partition it into `B^3` pieces of mass `q_i=B^-4`. Let one target set `T0`
have mass `B^-2`, and use target density one on `T0` but only `B^-10` on its
complement, for every source piece. Each source has degree about `B^-2`,
which is more than `B q_i`, so the amplification hypothesis holds. The
unweighted target union has mass one, much larger than `sqrt(B)Q=B^-1/2`.
But discarding the `B^-10` density outside `T0` costs a vanishing relative
amount of edge mass and reduces the target support to `B^-2`, far below that
claimed growth scale.

The weighted split detects this correctly: the main mass on `T0` has large
multiplicity and enters the distinct-source star. It is not charged to a
fragile union-growth step.

## What remains before this is a terminating geometric route

Equation (1) compares the target support to the **whole source mass `Q` used
in that invocation**. A later selection of one tiny source bush can reset
that mass. Therefore it does not prove growth along a continuation unless
the complete retained support is kept aggregated. Countable qualitative
source exhaustion can avoid selecting only one such piece, but this must be
used explicitly.

If every genuine continuation has `Q_{j+1}>=a Q_j` for one `a>1`, with
`0<Q_0` and `Q_j<=sigma(univ)`, that individual chain is finite without a
polynomial lower bound on `Q_0`. If an unbounded number of internal attempts
is possible across different starting nodes, assign errors summably, for
example `2^-j r0^A` per attempt. A common sublogarithmic depth does not follow.

There is an even stronger check for pure endpoint reversal: with the same
old-pair measure and exhaustive intermediate partitions, its source and
target supports exchange. Two consecutive whole-support growth reversals
are impossible. Removing even a tiny amount of edge mass can invalidate a
claim about unweighted support unless a bound such as (1) is retained.

Finally, the four-source branch still needs the original same-window,
origin-plane, and physical synchronization arguments. Neither (1) nor (2)
pays arbitrary separated-time old pairs, proves that these assumptions hold
on all cross-cap exits, or removes the common-target/smaller-cap continuation.
