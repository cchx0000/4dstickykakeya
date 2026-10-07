# Actual local-parent AD: source-faithful construction

Research date: 2026-10-05. Canonical repository inspected at commit 912dc065.
This is a mathematical derivation and an **uncompiled** Lean draft, not a claim
that the draft has passed Lean. No repository file was changed or compiled.

## Result

Write δ = D.thickness, N = 2^m, and d = Nδ/64. Starting from actual compact
native input, canonical
`NativeCompactAncestorRegularity.compact_original_ancestor_regularization`
constructs a single original-label set R before local incidence selection.
It retains at least half the number of tubes and half the total original
shading mass, retains density and CW with exponent ζ, and supplies, for every
occupied original dyadic parameter atom C at depth ell ≤ level,

    δ^ζ (2^-ell / δ)^3 ≤ |R ∩ C| ≤ δ^-ζ (2^-ell / δ)^3.

For each actual retained full parent

    Q = R.filter (parentLabel D a N = p),

with the actual existing `NativeLocalParentGeometry.line`, and every i ∈ Q,
every d ≤ r ≤ 1 satisfies

    δ^ζ / 2048^3 · (r/d)^3
      ≤ |{j ∈ Q : dist(carrier_local j, carrier_local i) ≤ r}|
      ≤ 125 · (r/d)^3.

The statement is independent of shadings. Thus later changes to actual cell
incidences do not affect these AD estimates, provided the full Q backbone is
preserved, including its zero-shading members.

The accompanying 311-line Lean draft ends with
`compact_original_local_parent_AD`, which **calls the canonical source
regularization theorem directly**. Its external hypotheses are actual compact
native input, δ sufficiently small, ζ > 0, and η ≤ ζ/16. It does not ask for
local AD as a new certificate. The intermediate `H` in its helper is exactly
the result of that canonical call. The final theorem supplies the SAME R for
all original dyadic parent scales m ≤ level.

## Why the present univ backbone cannot simply be reused

The current canonical `NativeOriginalParentSelection.backbone` is a fiber of
univ. Metric AD for the original source gives populations in balls; it does
not give lower populations on one specified side of a parameter-cell boundary.
Restricting to a half-open parameter cell can discard most or all of those
neighbors. Moreover, enlarging an R-parent back to its univ-parent adds new
centers that were removed during regularization. Lower AD at the retained
centers survives that enlargement, but lower AD at every added center does
not follow.

The necessary correction is therefore an actual original preselection R,
followed by whole-parent restriction **inside that one R**. It is not merely
adding R membership to a conclusion about an unchanged univ backbone, and it
is not replacing Q by the set of tubes used by a later refined incidence set.
All density denominators, per-parent tube masses, source enumerations and
parent incidence selections in the final caller must refer to this Q.

No explicit full-native-input counterexample was formalized here; the claim
is that the proposed restriction inference lacks its necessary premise, and
that an existing source theorem supplies the exact constructive repair.

## Metric constants and exact coordinates

For original graph parameters u_i = slope(D.line i) and
b_i = shiftedIntercept(D.line i, mesh D, shift D a), existing local geometry is

    localSlope_i     = N u_i - p.1,
    localIntercept_i = (N b_i - p.2)/4,
    localLine_i      = contractLine(ofGraph(localSlope_i, localIntercept_i, 0)).

The contractLine contraction is 1/32 in spatial offset and marked center,
and leaves its unit direction unchanged. In particular the physical graph
intercept of localLine is (N b_i - p.2)/128. The quarter-chart intercept is
(N b_i - p.2)/512. The proof here uses the pre-contraction localIntercept
definition exactly as written in the canonical source.

Forward bound: if every original u and b coordinate differs by at most t,

    dist(carrier_local i, carrier_local j) ≤ 16 N t.

Proof: the Euclidean local slope difference is at most 2Nt, the local
intercept difference is at most Nt/2, the second local intercept has norm
at most 1/2 ≤ 1, and canonical `graph_carrier_dist_le_sixteen` applies with
radius Nt. `contractLine_carrier_dist_le` then applies. Consequently a shared
original depth-ell parameter atom has local carrier diameter ≤ 16N·2^-ell.

Inverse slope bound, the only inverse estimate needed for upper AD:

    |u_i(k)-u_j(k)| ≤ (6/N) dist(carrier_local i, carrier_local j).

This follows from canonical `slope_sub_le_direction_dist`, north direction
component ≥ 1/2, `NativeLocalParentGeometry.slope_line`, and the fact that the
direction distance is at most the product carrier distance.

For completeness an unused full parameter inverse bound is also available:

    |b_i(k)-b_j(k)| ≤ (280/N) dist(carrier_local i, carrier_local j).

Derivation: let v_i = localIntercept_i, o_i = offset(localLine_i), and
s_i = localSlope_i. Then v_i(k) = 32(o_i(k)-s_i(k)o_i(4)), |s_i(k)| ≤ 1,
and ||o_i|| ≤ 1/32 (the uncontracted offset norm is ≤ 2||v_i|| ≤ 1).
At carrier distance t, the preceding slope bound gives |s_i-s_j| ≤ 6t.
Subtracting this intercept identity gives |v_i-v_j| ≤ 32(2t+6t/32) = 70t,
and b_i-b_j = (4/N)(v_i-v_j). The Lean draft deliberately proves the needed
slope inverse only; this optional full inverse is an elementary derivation.

## Lower AD at all real radii

For r ≥ 32Nδ, choose an original dyadic scale h = 2^-ell with

    r/(32N) ≤ h ≤ r/(16N).

The canonical `dyadic_below_radius` applied to r/N supplies ell. Because
r ≤ 1 and N = 2^m, the fine cell depth satisfies m ≤ ell. Because
r ≥ 32Nδ, it also satisfies ell ≤ level. The cell containing i is nonempty;
by exact dyadic nesting its full R-fiber lies in Q. Canonical
`NativeCoarseAncestorCounts.fiber_in_ancestor_eq` is the needed equality.
Its local carrier diameter is ≤ 16Nh ≤ r, so the source-derived ancestor law
puts at least δ^ζ(h/δ)^3 points in the ball. Now

    δ^ζ (r/(32Nδ))^3 = δ^ζ/2048^3 · (r/d)^3.

For d ≤ r < 32Nδ, the actual center i lies in the ball, while r/d < 2048
and δ^ζ ≤ 1. Thus the desired lower quantity is ≤ 1. This handles every
radius down to d, including all the fixed extra scales below Nδ.

This proof does not claim that a ball contains its enclosing dyadic cell.
It selects a strictly smaller atom about the center and uses the diameter
bound. It therefore has no boundary-cell gap.

## Upper AD with constant125

A local carrier r-ball gives an original slope cube with side 12r/N.
Apply `NativeOriginalSlopeCubePacking.original_cube_card_le`, whose additive
bound is valid even if that side is below the old separation δ:

    count ≤ (16·(12r/N)/δ + 2)^3
          = (3r/d + 2)^3
          ≤ 125 (r/d)^3,

since r/d ≥ 1. No original carrier AD upper estimate, no local intercept
inverse, no parent-count ratio and no chosen direction color are required.

## Readback into the actual native predicate

Enumerate exactly Q with canonical `NativePaddedCellSource.originalLabel`.
Give each index the existing local line and actual local cube shading, with
tube scale d = Nδ/64 and mesh d/2 = Nδ/128. This uses the actual constructor
`directionSeparatedWZCellSourceAtScales`: existing local direction separation
is Nδ/48 ≥ d. The ball-count readback is simply canonical
`NativePaddedSourceTransport.card_filter_originalLabel`; the reindexing is
bijective and loses no labels or counts.

Both native AD inequalities with target exponent e follow from the single
numerical budget

    2048^3 · d^e ≤ δ^ζ.

Indeed it gives the lower coefficient and, because δ^ζ ≤ 1 and
125 ≤ 2048^3, also gives 125 ≤ d^-e. The canonical
`NativePaddedSourceAdmissibility.real_AD_to_enn` converts the real inequalities
to the ENNReal fields of `IsWangZakharovFiniteInput`.

This budget is not automatic for every m merely from m ≤ level. A genuine
relative-scale power window is required when e is small. For example if
Nδ ≤ δ^α with α > 0 and αe > ζ, sufficiently small δ absorbs the fixed
constant because d^e ≤ 64^-e δ^(αe). The final geometric scale selection must
produce that window. Near m=level the local scale is 1/64, so arbitrarily
small original δ cannot by itself absorb δ^ζ against fixed d^e.

## CW interface (not duplicated in the Lean draft)

Given the actual anisotropic inverse-volume formula

    volume(F^-1 U) = 512^4/N^3 · volume(U),

the canonical `NativeLocalParentPhysicalMap.original_tube_maps` gives

    localContainedCount(U)
      ≤ δ^-η · 512^4/N^3 · volume(U) · n.

Original direction packing gives n ≤ 373248 δ^-3. The same constructed
parent ancestor lower bound gives |Q| ≥ δ^ζ/(Nδ)^3. Hence

    localContainedCount(U)
      ≤ (373248·512^4) δ^-(η+ζ) volume(U) |Q|.

The powers of N cancel exactly. Thus CW needs the numerical budget
(373248·512^4) d^e ≤ δ^(η+ζ). This uses the same actual Q, not a new CW
certificate. The unavailable historical inverse-volume theorem has not been
assumed part of canonical Lean here; only this future interface is recorded.

Density remains separate: retained original density on R is global and does
not assert every parent is dense. A genuine parent/incident-cell selection
must establish shading mass relative to full Q. Existing local cell-capacity
theorem then transports that actual mass with its proved N^3 factor.

## Canonical references used

- `native_compact_ancestor_regularity`: actual original R and all depths
- `native_coarse_ancestor_counts`: exact occupied finer-fiber equality
- `native_local_parent_geometry`: actual line, slope identity, separation
- `native_normalized_parent_carrier_metric`: graph and contraction metric bounds
- `native_padded_source_ad_lower`: dyadic radius lemma and N=1 precedent
- `native_original_slope_cube_packing`: additive slope-cube upper count
- `native_padded_source_transport`: exact original-label reindexing count
- `native_padded_source_admissibility`: real-to-ENNReal AD readback

Draft file: `native_local_parent_ad_metric_draft.lean` in this research folder.
Next authorized execution step is compile the isolated draft against the
canonical dependency cache, repair elaboration issues, and only then treat it
as proved. Current status is mathematical derivation plus explicit uncompiled
proof script, with no axioms, sorry placeholders, or changes to the original
source/admission class.
