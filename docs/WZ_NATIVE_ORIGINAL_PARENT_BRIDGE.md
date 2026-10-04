# Original native source to physical parent and one terminal refinement

This construction uses the existing actual native finite-input class in dimension four. It builds on the frozen native extremal and common-mesh incidence constructors; it does not identify that native class with every parameter-cell family in the paper.

The five new modules are `NativeOriginalCellChartGeometry`, `NativeOriginalParentSelection`, `NativeOriginalParentPhysicalData`, `NativeNearExtremalPhysicalParent`, and `NativeNearSourceSlicePopulation`.

## Original geometry, with explicit constants

For a valid original marked line with fourth direction coordinate at least 1/2, the actual graph slope has each coordinate bounded by 2. A point in its physical delta-tube has a genuine marked-segment witness at distance less than 2 delta. This proves graph residual at most 6 delta. Relative to an actual common height a in the original normalized slab, its fourth coordinate is within 1+2 delta of a.

Every original row shading is already represented exactly at mesh m=delta/2. Its original cell center belongs to that row shading and hence to the original tube. Translate integer height labels by floor(a/m), and contract all four coordinates by 1/4. The transformed old mesh is m/4=delta/8. The original cell-label map is injective and independent of the tube label. Its transformed time coordinate has absolute value at most 1. Its transformed graph residual is at most 12 times the transformed old mesh. Thus the physical data's E is the fixed integer 12, proved from original tube membership.

The actual transformed graph intercept is `(b + slope * floor(a/m)*m)/4`; the slope is unchanged by this fixed contraction. No cell is reassigned separately by tube.

## Actual parent and actual density

For a chosen positive integer N, the parent label is the pair of coordinate floors of N times the actual slope and N times the actual transformed intercept. The global shear parameters are the lower corner of this occupied parent cell. The constructed physical data has rho=1/N, old mesh delta/8, and target mesh N*delta/8. Every original tube in the complete parent backbone has normalized slope and intercept bounded by 1.

`exists_parent` selects an occupied original parameter parent by actual original incidence mass. If F is the number of the original parameter labels, its exact retention is `card(original I) <= F*card(parent I)`. F remains an actual computed cardinality. It is not declared subpower.

The backbone is ALL original tubes in that parameter parent, including empty shading rows. The density field is exactly

`min(1, (delta/8) * card(parent I) / card(parent backbone))`.

Its positivity and the complete-backbone density inequality are proved from the selected original counts. There is no supplied output density or multiplicity profile. `data_hypotheses` derives every field of `PhysicalRescalingIncidenceTransfer.Data.Hypotheses` from the original admissible source, the original rows, and the occupied parent. This theorem works for EVERY occupied parent, so a later extremal parent selector can replace the current largest-mass choice without changing the geometry.

## Consumed source caller

`exists_near_extremal_physical_parent` starts with a positive native extremal infimum. For every fixed N>0 and every positive original parameter/scale cutoff it constructs an actual original admissible D, exact original cell rows, an actual common height and parameter parent, and its physical data. It chooses the original scale below 8/N, so physical scale validity is derived.

`near_source_slice_population` then consumes that physical data in the previously frozen simultaneous spatial/phase refinement. It constructs E0 as an actual subset of the ORIGINAL D cell incidences, with an injective, equal-cardinality readback to the selected physical E. The same E carries full selected heavy fibers, all prepared spatial-ball comparisons, and all actual phase/time degree comparisons. Original retention costs exactly F times the existing self-uniform loss H. The derived final multiplicity lower bound is

`ofReal(lambda) * delta^(-kappa+theta) <= F * ofReal(2*K*H) * ofReal(mu(B))`.

All quantities are either original data, actual selected counts, or explicit constructed constants. The equality of the original and physical selected cardinalities is proved, not assumed.

## Exact remaining scope

This does not prove F or the reciprocal computed density is subpower. It does not derive the matched coarse/relative multiplicities (113), nor the ambient slice AD exponents (130)--(135). The next universal K_native application needs an actually admitted coarse/normalized parent family: original parent-backbone reindexing when required by a Fin-indexed caller, graph-parameter injectivity for that caller, direction separation at its output thickness, transformed carrier AD and convex-Wolff, and density exponent absorption. Dyadic output scales must be derived by choosing N and later padding multipliers as powers of two; arbitrary positive integer N does not imply dyadic target scale.

The existing padded cubical-source constructor can reuse the proved physical geometry, retention, and backbone bounds. Its remaining native admissibility clauses are not consequences merely of `Data.Hypotheses` and are not inserted into that structure here.
