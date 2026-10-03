# Compatible finite grains and native rescaling witnesses

2026-10-03. This checkpoint adds seven constructive modules to the local WZ
route. The original compact marked-front theorem is unchanged and remains
unproved without the preexisting project volume axiom.

## Construct the layers, including the original weights

`RichDirectionalLayers` constructs nested nonempty layers from reference
partition occupancies, retaining at least half the initial finite set. It
chooses integer thresholds by a floor-plus-one rule, so a threshold below one
does not create an artificial deletion charge. The final theorem directly
applies the independent backward-fiber count to its constructed layers.

`WeightedRichDirectionalLayers` does this with the unchanged original natural
number weights. At each step it deletes entire low-weight columns. Lower
reference column mass bounds the number of possible charged columns; a bound
on total original weight at one geometric vertex converts predecessor weight
into a ceiling lower bound on the number of distinct predecessor vertices.
No injectivity of the label-to-geometry map is required. The output retains
at least half the original weight and supplies the exact geometric layers
needed by the backward-fiber theorem.

These reference occupancy and vertex bounds are local geometric inputs, not
the desired final grain structure. Their proposed construction from actual
WZ tube profiles is detailed in
[the one-scale argument](WZ_RECURRING_TUPLE_RICH_LAYERS.md). That full approximate
tube adapter is not yet a Lean endpoint.

## Select compatible tuples with actual finite choices

`CompatibleTupleSelection` chooses a maximum-weight angular fiber in each
spatial cell at each stage. Spatial partitions refine earlier partitions;
the original conditional angular menus have cardinal bounds `B_j`. Previously
selected compatibility makes the relevant parent angular state constant on
each current spatial cell, so those conditional menu bounds apply.

The constructed subset retains weight with the explicit product loss
`product B_j`, and has compatible choices at every stage. The good-tuple-family
endpoint starts from original labels and their actual finite good tuple sets.
Its numerator is literally `sum_x w(x) * card(G_x)`. It returns good witness
pairs whose projection to original labels is injective, so final pair weight
equals the retained original-label weight. It assumes no coherent selector.

The telescoping WZ menu estimates and their parameter order remain separately
audited geometry; see
[the multiscale argument](WZ_COMPATIBLE_MULTISCALE_SELECTION.md).

## Uniformity and grain richness on the same final subset

Later arbitrary refinement need not preserve an earlier grain lower bound.
`SelfUniform.weighted_self_uniform_grain_refinement` handles this directly:
append each fixed grain partition as an equivalence relation to the existing
symmetric incidence relations and call the proved self-uniform construction
once.

It retains the same explicit bound with the total number of relations and
derives, for every final point and every grain level,

```
mass(final) <= Q^2 * card(original grain classes) * mass(its final grain).
```

Both quantities count the same final labels. The proof uses a weighted
partition sum; no final-richness certificate or alternating restoration loop
is assumed. Labels at different levels may have different types, without
global finiteness assumptions on those types.

## Literal coarse cells contain actual segment witnesses

`PaddedPhysicalCellWitness.weighted_physical_cell_witness` invokes the finite
cyclic selector on the actual fine-bin integer indices. It constructs a
common shift and a half-weight original subset, then proves that the translated
physical point and every coordinatewise nearby point belong to the same
literal half-open coarse cube. Negative indices are handled by Euclidean
division. The floor identity and the cube membership are conclusions, not
hypotheses.

`NativeGraphMarkedLine.ofGraph` constructs the native valid marked line from
arbitrary graph slope/intercept and a common marked height. It uses the
orthogonal projection formula for the line offset, proves the exact graph
parameter identities, and derives the native common slab and full height
window from coordinatewise slope bounds. It also proves an explicit endpoint
buffer. No abstract normalization certificate is supplied by the caller.

`PhysicalRescalingDensity` proves the density estimates for the tube labels
used in the ORIGINAL incidence set, including labels whose shading becomes
empty after selection. Extending this explicit comparison to a larger
backbone with already-empty initial rows requires its original full-backbone
density inequality; that arithmetic assembly is recorded separately and is
not silently inferred from the number of used labels.

The resulting
[padded native bridge](WZ_PADDED_NATIVE_RESCALING_BRIDGE.md) preserves original
incidence labels and uses the existing exact factor-two cube/tube containment
lemma. Its remaining combined assembly includes dyadic scales, coarsened fiber
counts, restored direction separation, metric AD pruning, convex-Wolff and
the exponent absorption. The seven modules do not by themselves assert all
those native admissibility clauses.

## Remaining global geometry

The new finite constructions remove assumed layers, assumed compatible tuple
choices, and assumed simultaneous final grain richness from the local route.
The geometric profile/menu callers, exact slice representation and AD-slice
estimates of Proposition 18.2 Step 6, and the later global incidence argument
remain. No new axiom or final hypothesis has been added to hide them.
