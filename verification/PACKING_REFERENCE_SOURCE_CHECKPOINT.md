# Fixed positive reference source and hereditary vertical counts

## Original-data endpoint

`StickyKakeya4.ActualSlopeSource.sticky_datum_exists_actual_vertical_reference_source`
in `Theorems/Thm_StickyKakeya4_actual_reference_vertical_count.lean` starts from
`IsStickyDatum ambient` and an arbitrary fixed real slack `ζ > 0`.

It constructs the Borel direction selector, a marked-center bin `k`, and a
measurable positive-volume set `B` in that bin. The source is literally
`volume.restrict B`. Its actual `slopeCarrierMap` remains explicit in every
net and pushforward conclusion. The complete common height interval of
length `3/8` lies in the original front pointwise on `B`.

At each dyadic radius `τ = 2^(-n)`, it constructs a finite carrier-supported,
`τ/2`-separated net whose radius-`τ` balls cover the image of `B`. Every such
ball has source pushforward mass at least `c τ^(3+ζ)` for one fixed `c > 0`.
For one finite `A`, uniformly over scales and direction centers, the number
of references with direction in a radius-`τ` direction ball is at most
`A τ^(-ζ)`.

`actual_reference_cover_is_hereditary` retains a covering subfamily for any
subset `T ⊆ B` and preserves all these vertical reference counts. This is a
support-cover statement. It does not assert that the cell-mass lower bound
survives arbitrary later source restriction.

## Construction and dependencies

1. `positive_cell_regularization`: simultaneous countable overlapping-cell
   deletion; first-eligible charges pay each cell at most once. The total
   loss is bounded by the threshold sum, and every occupied limiting cell
   has its prescribed lower mass. Positive-power dyadic slack makes the
   weighted threshold sum finite. A common conull cleanup removes all
   zero-mass cells without changing the restricted measure.
2. `packing_reference_nets`: finite covers are recentered on the carrier,
   then maximally separated, with no cardinal increase. Actual
   `coveringNumber` bounds supply the finite cover witnesses.
3. `compact_packing_power_piece`: a compact positive-mass carrier of packing
   dimension below a chosen exponent contains a compact positive-mass
   power-cover piece. Raw packing pieces need not be measurable; intersect
   with the original compact set before choosing a positive piece, then
   take closure with the proved radius loss.
4. `packing_reference_source`: construct the positive source and occupied
   nets from actual covering bounds, then directly from packing dimension
   at most three. The net-ball masses are those of the actual pushforward
   of the constructed restriction, not assumptions in a certificate.
5. `actual_packing_reference_source`: instantiate this construction with
   the original bounded-density slope source and its direction--offset map.
6. `packing_reference_overlap`: compact-unit-ball normalization proves a
   scale-independent overlap bound in any proper real normed space;
   measurable-family integration turns it into a mass-counting bound.
7. `packing_vertical_count`: cubic direction upper mass and lower phase-ball
   mass yield the finite coefficient `8 K D / c` and exponent `-ζ`.
8. `north_slope_direction_density`: on the closed unit slope ball,
   `dist(a,b) ≤ 6 dist(N(a),N(b))`. Direction-ball pullbacks are contained
   in slope balls of radius `12r`; Euclidean volume gives cubic direction
   density from the actual source domination by volume. No spherical
   Jacobian estimate is assumed.
9. `actual_reference_vertical_count`: integrates the preceding facts from
   the original sticky datum and proves hereditary reference-subfamily
   coverage/counting.

## Verification and scope

`packing-reference-source-checkpoint.json` records the nine source paths,
readbacks, exact-command logs, exit statuses, and public-declaration counts.
Every source was checked with `-DautoImplicit=false`, sequentially, and every
public definition/theorem received an axiom readback. The only allowed
axioms in these readbacks are `propext`, `Classical.choice`, and `Quot.sound`.

These are targeted checks of new modules. They are not a full-project build,
a final-theorem verification, or removal of the existing Wang--Zakharov
axiom from the repository's old final route. No existing source module was
edited. No root-fiber paid estimate, moving-affine-blowup Frostman support
transfer, literal `o(1)` bound for a universal source, or final Kakeya
statement is claimed.
