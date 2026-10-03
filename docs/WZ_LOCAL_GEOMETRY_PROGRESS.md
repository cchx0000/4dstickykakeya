# Constructive local steps toward the finite volume theorem

2026-10-03. The final compact marked-front theorem and its original hypotheses
are unchanged. This checkpoint proves finite local constructions and verifies
the existing original-source input constructors. It does not prove the final
Wang--Zakharov volume bound.

Primary source: [Wang--Zakharov, arXiv:2609.22035](https://arxiv.org/pdf/2609.22035),
Proposition 3.1, Lemma 4.2, and Proposition 18.2, especially Steps 3--5,
equations (107)--(123). The route considered here is to prove the required
universal finite theorem and then use the already constructed original-front
packets. It is distinct from asserting a uniform charge for every hereditary
old occurrence law.

## Original-front input is already available without the volume axiom

Fresh imported axiom checks verify the following existing declarations using
only `propext`, `Classical.choice`, and `Quot.sound`:

- `packing_selector_has_cover_adapted_wz_packets_at_exponent`
- `coherent_boundary_has_cover_adapted_wz_packets`
- `packing_three_pruning_assembles_wz_finite_input`
- `separated_directions_convex_wolff_estimate`

These construct actual finite packets, including dense cubical shadings,
direction separation, carrier AD counts, convex-Wolff bounds and the target
cover comparison. They do not call `wang_zakharov_published_volume_estimate`.
That axiom is still needed at the final volume step. Evidence is in
`verification/WZCoverInputReadback.lean` and its log.

## Self-uniformity on the same retained set

The earlier general incidence core compares degrees at a core against a
possibly larger ambient set. WZ's concentration calculations need both degrees
to count the same retained set. The new
`SelfUniform.weighted_self_uniform_refinement` constructs that stronger result
for finitely many symmetric reflexive relations.

For `d>0`, integer `Q>=4`, positive integer original weights and total weight
at most `Q^L`, it constructs nonempty `B` with

```
weight(A) <= 2 (4d)^(dL) weight(B),
degree_i(B,x) <= Q^2 degree_i(B,y)  for x,y in B.
```

The proof constructs a peeling decomposition, controls the colored deletion
energy using symmetry, retains a large low-degree class when peeling fails,
and decreases an integer degree-height potential. It assumes no core or
self-uniformity certificate.

Literal one-sided dyadic rectangles are not exactly symmetric. The geometric
adapter uses the source's padded tube setup, exact time/angle-cell equality,
and a symmetric midpoint residual. Each literal rectangle is covered by a
polynomial number of these symmetric neighborhoods centered at actual retained
points. The full geometric adapter is audited handwritten work in
[WZ_PADDED_SYMMETRIC_RECTANGLES.md](WZ_PADDED_SYMMETRIC_RECTANGLES.md);
the scalar padding constructions described next are independently formalized.

## Actual common translations, including preservation of the fine mesh

`GridPaddingTranslation.weighted_vector_translation` constructs a real common
translation for arbitrary real intercepts at finitely many scales, retaining
at least half the original integer weight. Its grid-boundary measure estimate
is proved by an explicit finite interval cover. This result alone does not
preserve a specified dyadic fine mesh.

`FiniteCyclicGridPadding.cyclic_vector_translation` additionally preserves
that mesh. For `N>0`, `R_j>0`, `H R_j` dividing `N`, and
`H>=max(4,16 r m)`, it constructs `q in Fin N` and a half-weight subset with

```
4 R_j <= (b_i(a)+q) mod (H R_j) < (H-4) R_j.
```

The intercept indices can be negative. The proof derives uniform cyclic fiber
cardinality and the boundary-strip count, then averages actual original
weights. For fine mesh `delta=1/N`, the translation is `q delta`; no tube or
incidence is resampled.

## Exact backward fibers and original occurrence weights

`BackwardFiberGrains.independent_backward_fiber_bound` proves the finite
backward induction used in the grain step: actual independent predecessor
directions with lower counts `L_i` give at least `product L_i` points of the
initial set in the final affine fiber. Predecessors are allowed to lie in the
previous layer; no unjustified same-layer richness is required.

The quotient-plane count and dense-class selection are also constructed.
`labelled_independent_dense_grains` keeps arbitrary nonnegative original
occurrence weights even when multiple labels project to the same point. It
counts distinct geometry through the image map and keeps the original labels
and the full weights of retained plane classes. At least half the original
label weight survives the dense-plane cut.

These are exact affine-fiber statements. Producing their independent tuple and
rich predecessor layers from the actual finite tube configuration remains a
separate geometric construction; approximate thick tubes cannot be silently
identified with exact affine lines.

## Rescaling without an inverse-scale shading loss

An anisotropic map

```
(X,t) -> ((X-b_c-t a_c)/rho,t),   rho=1/N,   sigma=N delta
```

sends old cells into new bins. Filling every new sigma-cube immediately can
inflate the union by an unwanted factor `1/rho`. The finite heavy-bin
construction prevents this.

`IncidenceBinTransfer` uses an actual incidence set `I subset T x C`, one
global spatial-cell map, and integer threshold `m>=1`. It retains every
original incidence in each tube/bin fiber with at least `m` incidences. It
proves the sharp loss `(m-1) M |usedTubes|`, exact preservation of arbitrary
additive weights within retained fibers, and

```
m |I| |U_new| <= 2 L |I_new| |U_old|
```

when at least half the original incidence survives, each tube meets at most
`M` bins, and every global bin has at most `L` old cells. There is also a
stronger variant using the retained old spatial support.

Those two geometric bounds are now proved independently:

- `ShearBinFibers.actualBin_filter_card_le` derives `L=N` for the literal
  coordinate-floor assignment of sheared old cell centers. Every bin on the
  full lattice has exactly `N` preimages, including at negative time indices.
- `TubeBinCount.distinct_gridBins_card_mul_scale_le` derives
  `M sigma <= 4(2E+4)^3` for actual points of a slope-bounded graph tube with
  coordinate error at most `E sigma` and `|t|<=1`. It constructs the finite
  floor-index boxes; no covering-number bound is assumed.

`PhysicalRescalingIncidenceTransfer.Data.physical_rescaling_transfer` now
combines those geometric bounds with the actual original density
`lambda |usedTubes| <= delta |I|`. It constructs the ceiling threshold,
retains at least half the original incidence, keeps every old label in each
retained fiber, and proves

```
mu_old <= [16(2E+4)^3 / lambda] mu_new.
```

The statement covers the threshold-one regime and empty incidence sets. Its
only inputs are original grid centers, actual affine tube parameters, physical
residual/slope/time bounds, and density. No fiber-count or tube-cover
certificate is assumed. The full AD/admissibility adapter remains separate.

## Remaining finite-geometric obligations

[WZ_COARSE_AD_CLOSURE_ADAPTER.md](WZ_COARSE_AD_CLOSURE_ADAPTER.md) audits a
constructive route from metric carrier AD to coarse and rescaled admissible
families. It uses maximal-net populations, direction coloring, explicitly
charged low-population pruning, and the heavy-bin construction. The combined
metric adapter is not yet formalized.

The next obligations are the bounded auxiliary extremal class, compatible
matched multiplicities at the intermediate scales, and the actual recurring
transverse tuple and rich-layer construction of Proposition 18.2 Step 5.
The later global grain and incidence arguments also remain. These missing
steps are not additional hypotheses of the original main theorem and have
not been inserted as certificate fields or new axioms.
