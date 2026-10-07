# Step6 same-source parent and slice readback

The reference is the current native E1/E2 construction on one original R. The older `native_original_slice_*` and `native_fixed_compact_slice_population` suppliers construct another physical-parent/refinement witness. Their conclusions cannot be substituted for the unchanged E1/E2 without a separate retention and identification proof.

The primary WZ source is [pp.72–73, equations128–135](https://arxiv.org/pdf/2609.22035#page=72). Its finite homogeneity step fixes a physical segment length and varies horizontal width. A post-rescaling horizontal height cell is therefore not automatically the original micro-height, and isotropic point-grid labels do not directly encode the required anisotropic classes.

## Verified original-reference region bridge

Module `NativeParentPointRegionCounts`,9 declarations, strict-source attempt02, SHA256 `3ab00d264a6e72c7c9c51e6f423f970aaee8fb1db720368c8acee17aa2403079`.

`regionEdges E test` is the literal edge filter by `test z.2`; `regionPoints E test` is its distinct occupied original point image. `region_card_fiber_sum` sums the point fibers of THIS edge family. With a parent-restricted edge family it uses that parent's own point weights, not global all-E2 weights.

For I an actual scheduled E1 parent, Q=coreRadix, epsilon=(2^m)delta/64 and kappa=extremalExponent, `source_parent_region_counts` derives from IsCore and HasBalancedScale:

- delta^seed epsilon^(−kappa) |regionPoints(I,test)| ≤ Q² |regionEdges(I,test)|
- |regionEdges(I,test)| ≤ Q² delta^(−seed) epsilon^(−kappa) |regionPoints(I,test)|
- Every F⊆I inherits the latter upper with its own occupied point count

`region_point_retention` requires actual retention in the particular region before proving a lower point-population transfer there. Whole-family retention alone is not used to infer every regional lower.

## Verified dense original phase-parent selection

Module `NativeDensePhaseParentRetention`,4 declarations, strict-source attempt02, SHA256 `5f5813bc2c84ea5e10943297bc78caa65311c5c82d0cd8ccfb57d85f4619c597`.

`exists_retained_fiber` partitions actual edges by any fixed label function. From J⊆I, I nonempty, theta>0, and theta|I|≤G|J| it chooses one occupied label p satisfying theta|I_p|≤G|J_p| and J_p nonempty.

`source_dense_parent` specializes this to the original scheduled phase-parent map and E1's existing point uniformity. The selected parent lies in R's original parent image, and

theta |points(E1_p)| ≤ G Q1² |points(J_p)|.

`parent_region_commute` proves that an original point cut and phase-parent restriction commute as literal filters. It does not identify their point weights with the pre-restriction weights.

For a final history point cut J of E2, the known total history mass and E1→E2 retention can be composed before this averaging step. The selected parent then has a paid aggregate edge/point retention bound. Global grain-density lower bounds still do not descend to every class inside that parent.

## Verified caller-slot decoder for anisotropic cells

Module `NativeParentSliceCallerMenu`,7 declarations, strict-source attempt02, SHA256 `8f656f5bb30b36fbf2c7ccf55098ea881758196c12f817eec538f0a2e711e2d1`.

The API takes

- `point : Parent → Index → X`
- `classes : Parent → Fin K → X → Y`

and defines exactly1+K equality relations. The point relation is tagged by the original outer parent, and every class relation has the same parent tag. The classes may retain the point's slice-height label while coarsening only its three spatial coordinates.

`parent_uniformities` decodes HasUniformFibers with factorQ2² on the actual parent restriction. `parent_occupied_class_counts` then proves factorQ2^4 comparability of DISTINCT occupied fine point counts in every occupied class. It is not a geometric AD exponent assertion.

These caller relations must be installed BEFORE the one E2 is selected. K is fixed before the source constructor chooses tau,g,L2; the actual map values may depend on the returned D,R,F,stop. One cannot silently set K=g+1 or level afterward. Parent and height values do not each require separate relations.

With existing query count Kq, adding1+K relations to old caller dimension d changes the exact second-stage cost to

retentionCost (((d+(1+K))+Kq+Kq+Kq+1)+(g+1)*(g+1)) 1 L2.

The1+K maps suffice for point-class homogeneity. If subsequent analytic comparison also requires tube/point-pair uniformity on every anisotropic point/class map, reserve another1+K relations, giving2(1+K); the current isotropic fixedPair laws do not supply them automatically.

## Existing chart and exact remaining geometric bridge

Use `NativeLocalParentPhysicalMap.physicalMap D a N p`, not a new ad hoc shear. Applied to an original cell center it is the existing common parent-dependent affine map. Its time coordinate is exactly

oldTime D a k /128 = (cellCenter(mesh D) k (3) − (shift D a)*mesh D)/512.

This time coordinate is independent of N and p. `NativeLocalCellCoherence.physicalCell_height` and `cellLabel_height_eq_physicalCell` already provide the exact common-time identities. Choose the horizontal and height bin widths independently on this chart. The independently chosen slice-height width must not be silently replaced by the original micro-height or by an isotropic raw spatialLabel width.

The geometric-readback worker owns comparison of these anisotropic occupied point/classes with the same-R fullSource two-scale counts, including fixed-height length, shear, and every time/grid factor. The current global history lower uses all-E2 point weights and full raw-fiber closure; it is not a parent-local grain lower. Finite parent selection, reference-region bounds, and new caller homogeneity are now available, but horizontal-slice AD exponents and the later post-cut lower bounds still need that geometric/profile argument.

All three modules are frozen for main's independent imported-axiom audit and canonical integration. No new full build was started.

## Fixed-height versus isotropic time-filling cost

The independent geometry audit identifies a remaining factor H/sigma for horizontal width sigma inside a fixed physical height segment H. In the depth range m≤f≤2m−6, H=64/2^m and sigma=64/2^f, this is2^(f−m); it is not a universal constant and cannot be hidden in a bounded image-menu comparison.

The actual queried short-row lower at(f,m), together with finePair(f,f) uniformity, is the proposed finite supplier of H/sigma occupied fine cells in a coarse segment, with the literal lambda delta^(c1+3c2) loss. One query entry(f,m) already installs both relevant fixedPair relations. A fixed K-element horizontal menu therefore requires up to K extra query pairs, separately from the1+K anisotropic point/class caller relations. Every relation/query cardinal must be fixed before the source constructor.

Because f≥m, these fixedPair equality fibers stay whole under restriction to the original outer m-parent. Finest original-tube localPair richness likewise stays whole under a parent restriction. Unconditional raw point uniformity does not. Arbitrary later history/source-point cuts require their own retention argument before a short-row or time-filling lower can be used.

The geometric-readback worker owns that time-filling comparison and its exact chart constants. The finite modules in this audit do not assert that it has already been proved.
