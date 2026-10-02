# A fixed regular reference source from the original packing hypothesis

This note describes the checked reference-source construction and its scope.
It does not claim the remaining transverse/root-weighted estimate.

## 1. The source is chosen before a residual graph

For every positive slack `zeta`, the original `IsStickyDatum ambient`
hypotheses yield a Borel direction selector, a marked-height bin `k`, and a
positive measurable set `B` of unit-ball slope parameters. The source is the
literal measure

    sigma = volume.restrict B.

The selected original segments contain a common height interval of length
`3/8`, pointwise for every slope in `B`. Its phase map is the original
`(direction, offset)` pair of that selected line, not a replacement label.
In particular, the pushforward remains supported in `lineCarrier ambient`.

The construction uses the original packing-dimension hypothesis for this
fixed source. It makes no reference to the mass of a later residual graph.

## 2. Compact power-cover piece

A countable cover witnessing packing dimension at most three contains a
positive-mass piece with an upper covering exponent below `3 + zeta/2`.
Taking the closure of its intersection with the compact carrier preserves
positive mass and containment. A factor-two change in radius controls the
covering number of the closure even if the original packing pieces were not
measurable. Compactness then extends the eventual estimate to every radius
in `(0,1]`, with one finite constant.

At dyadic radius `tau`, a maximal separated supported net can be selected
with separation `tau/2`, whose open `tau`-balls cover that piece. Its size is
at most a constant times `tau^(-3-zeta/2)`.

## 3. Simultaneous lower mass by one countable trimming

For a finite measure `mu`, countably many measurable sets `F_i`, and
thresholds `a_i` with summable total below half the original mass, repeatedly
delete every set whose current retained mass is below its threshold. Charge
a set only on its first eligible deletion. Its contribution to total loss
is then below `a_i`, irrespective of overlaps or later rounds.

Continuity from above shows that the limiting restriction has, for each
`F_i`, either zero mass or mass at least `a_i`. A final deletion of the
countable union of its zero-mass cells changes no measure and makes the
occupied cells cover the retained source literally.

Apply this to all reference-net ball preimages, with threshold
`c tau^(3+zeta)`. The sum of the thresholds is bounded by a constant times

    c sum_n (2^(-n))^(zeta/2).

A sufficiently small fixed positive `c` leaves positive source mass. Every
occupied reference ball therefore has original reference mass at least
`c tau^(3+zeta)`, simultaneously at all dyadic scales.

This is a lower bound for the one fixed source. It is not a lower bound for
every later submeasure or source cut.

## 4. Hereditary vertical support count

Separated reference balls have uniformly bounded overlap in the fixed
finite-dimensional direction--offset space. The north slope chart has an
explicit inverse distance bound on the unit slope ball, so `sigma <= volume`
gives a cubic upper bound on its actual direction marginal.

Fix a direction ball of radius `tau`. Every reference ball with center
direction inside it maps into the direction ball of radius `2 tau`. Hence
bounded overlap, the reference lower mass, and the direction upper density
give

    (# such reference centers) c tau^(3+zeta) <= C tau^3.

Thus their number is at most `A tau^(-zeta)`, with a finite constant `A`
dependent on the fixed selected source and the slack.

The same reference cover also covers every subset of `B`. Keeping only its
live reference cells cannot increase any count. This is why the upper
support estimate is genuinely hereditary even though the lower mass bound
is not. No division by a later old-occurrence mass is present.

The slack is an arbitrarily small fixed power chosen before the source.
This does not assert one universal source with a simultaneous subpower bound
for every slack, or a uniform bound on the density of normalized descendants.

## 5. Consequences for the original finite-scale argument

The construction supplies a replacement for the manuscript's vertical
pruning factor `L/H` in the support-counting step. For a fixed positive
reference source, later restrictions inherit the support count by inclusion.
This removes the original graph-mass denominator at that particular step.

There is a useful handwritten preprocessing consequence for the fixed scalar
polarization coordinate in `v063/v064`. With reference branch count
`B <= W^(-zeta)`, the displayed near-edge bound has exponent

    1 + alpha + chi - theta_bar - epsilon - zeta,

rather than losing the entire `chi` through `B`. Relative to graph mass
`W^chi`, this is a small fraction when
`alpha > theta_bar - 1 + epsilon + zeta`, feasible with `alpha < 1` for
`theta_bar <= chi < 2` after choosing the losses sufficiently small.

The valid order is to delete the near edges from the current graph first,
and then rerun the raw four-cycle/Maslov routing. This produces either its
physical-bush output or new raw cycles with all required edge separations.
It does not preserve an arbitrary previously selected rank-loss cycle law.
The coordinate must be fixed across the dense block; an edge-dependent old
normal or a fixed-width normal approximation is not automatically valid at
an arbitrarily fine separation threshold.

These exponent manipulations are source-level analysis, not yet a formalized
transverse payment theorem.

## 6. Boundary that remains

The reference count does not bound the number of distinct anchor-packet
occurrences through each carrier cell. In the manuscript's `v053` formula,
that separate reuse multiplicity remains in `sum r(cell) / K`. Nor does
normalizing a small descendant preserve its direction-density constant.

A genuine quantitative root-weighted charge, or a supported Frostman escape
for the remaining geometric branch, is still required. The original final
statement and its preexisting external WZ dependency have not been changed.
