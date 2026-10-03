# Native lattice alignment: exact next theorem and adapter boundary

Audit date: 2026-10-03. This is an assembly specification, not a claimed Lean proof. Source: WZ Lemma 5.3 / Definition 5.1, printed pp. 23–25; [the complete handwritten adapter](WZ_LEMMA53_COMPLETE_PATCH_ADAPTER.md), especially §§3–8 and 11. The actual exported statements of the current constructors were inspected. This specification is not a complete Lean theorem.

## 1. Smallest useful end-to-end statement

Prove the two-dimensional theorem first. This is the nontrivial quotient dimension in native ambient d=4, ell=2; the ell=3 quotient is one-dimensional and does not need this alignment step.

For every zeta>0, construct chi>0 and eta0>0 such that, for every 0<eta<eta0, some M0 has the following property. For M>=M0 let delta=2^(-M), let A be a nonempty finite subset of Z^2, and put p(k)=delta*k. Assume only:

1. p(A) is contained in [-1/4,1/4]^2 (a fixed translated/dyadic normalization is allowed before this theorem).
2. 0<=t<=2.
3. Original-point metric AD: for every k in A and delta<=r<=1,
   (r/delta)^t / delta^(-eta) <= #{j in A: dist_inf(p(j),p(k))<=r}
   <= delta^(-eta)*(r/delta)^t.

The lattice supplies separation and injectivity. Equivalently, one may give integer-box counts at all integer radii, but use the above metric statement to call the existing ADGridCoverMenus API directly. A separate dyadic-only input corollary costs the explicit 2^t interpolation factor; it is not part of the minimal first theorem.

Construct A' subset A, s in [0,min(t,1)], a common coordinate permutation J, and common scales a,b with delta<=a<=b<=1/64. Put tau_out=64b and e=a/tau_out. Require:

- A' is nonempty; #A' >= e^zeta #A; tau_out/a >= delta^(-chi).
- a and b are original dyadic scales (delta times integral powers of two).
- For every k in A', the set B_k={j in A': dist_2(p(j),p(k))<tau_out} is exactly its retained parent patch.
- For each such k, construct alpha in [-1,1], a finite Y subset R, finite nonempty X_y subset R for y in Y, and P_k={(x,y+alpha*x): y in Y, x in X_y}.
- P_k is e-separated in Euclidean norm, lies in [-1,1]^2, and has both Hausdorff inclusions with error <=e/10 relative to {J(p(j)-q_Q)/tau_out: j in B_k}, where q_Q is the dyadic lower corner of k's parent Q.
- Each X_y is (e,s,e^(-zeta))-AD and Y is (e,t-s,e^(-zeta))-AD, using the existing closed-ball point-count convention on [e,1].
- For every e<=r<=u<=1 and every genuinely specified r-by-u segment tube T in ANY direction, the number of standard physical r-grid cells met by P_k intersect T is <=e^(-zeta)*(u/r)^s. One may instead export the equivalent minimal-cover count after proving its fixed-grid conversion.

The tube predicate can be explicit: points within sup-distance r of c+q*v, |q|<=u/2, ||v||_inf=1. Euclidean tubes are contained in such tubes with fixed dimensional changes, which must be absorbed. This output contains the whole Definition 5.1 content. Do not omit the all-direction tube condition. Do not assert t-s<=1 merely from finite-scale AD.

All fiber data, tube profiles, angular menus, witnesses, aligned sets, and patch isolation are OUTPUTS or constructed internal objects. None appears as a new theorem hypothesis. Original-point cardinality, not arbitrary shading weight, is the retained quantity.

## 2. Simplifications to the handwritten construction

Use epoch drop factor K=2 in `exists_large_finite_cover_epoch`. Its proved budget is #scalePairs * rank 2 |A|, which is O(M^3). This remains an absorbable polylogarithmic loss and gives factor-two current/start profile comparison. No mesh-dependent kappa is needed. Repeated pruning maps for equal rho at different scale pairs are harmless if their O(M^2) multiplicity is included in the budget.

For the FIRST uniform call, only three families at the m+1 candidate radii are needed: spatial cell; (spatial cell, angular bin); (source fiber, spatial cell). Their count is fixed before M. The last family gives in-parent rich spines; no all-scale anchored fiber AD or point-line metric relation is used afterward. Call the base self-uniform theorem directly: the grain wrapper exports grain richness, but not every appended grain's pairwise comparison required for angular-menu stabilization.

Use c=64 for shear quantization, C_ball=64, top tube length 1/64, and parent color modulus 260. Then tau_out and N_grid=64b/a remain dyadic. These constants meet the existing two-dimensional Euclidean movement/isolation hypotheses.

## 3. Already proved constructors and exact remaining adapters

Status W means finite bookkeeping/arithmetic from verified statements. Status G means an actual geometric map/containment/count still must be proved; the handwritten argument supplies its intended proof, but no corresponding end-to-end Lean caller was located.

1. **Actual tube footprint family (G, elementary).** On the finite original subtype A, define the finite family of ALL traces of actual segment tubes by filtering its powerset with an existential tube predicate. Retain a witnessing center/direction/parameter for each chosen trace. Prove point coverage and trace diameter. `GraphTubeGridCover.segment_occupied_cells_bound` gives the linear cover bound; `ADGridCoverMenus.finite_footprint_profile_AD_bound` gives the t-power bound. The former expects actual coordinate error witnesses; the latter expects actual footprint diameter. Neither constructor currently defines this common family for the alignment caller.
2. **Stopped profile and epochs (W, with one grid identity).** Use `CoverProfileClipping.exists_clipped_dyadic_cover_profile` on each nonempty residual, restricted to [delta,1/64], to DEFINE its selector. The selected scales/exponent are derived. Encode realized cell labels in a finite type, apply AD global-menu bounds to the penalty with lambda <=1/(C K_A^3 #scalePairs), then call the finite epoch constructor with K=2. Natural floor thresholds may be zero: recover real lower mass with `Regular.half_real_threshold`/`wholeCells_card_ge_half_real`, not the vacuous floor-times-profile output alone. Prove literal dyadic ancestor factorization using integer division and use `wholeCells_image_ancestor`. Select a heaviest direction chart by whole fibers; disjointness supplies one source fiber and one actual direction per original point.
3. **Expanded-fiber geometry and reference menus (G).** Whole-rho-cell expansion stays inside a fixed enlarged rho-by-tau tube. Local restrictions to dyadic r-parents preserve actual maximizing-tube witnesses. Fixed-factor enlarged/shifted tubes must be covered by a bounded number of original-profile tubes; extend endpoints with bounded covers. This transfers the SAME epoch-start E0 upper profile to all extracted fibers, local segments, and later strips. Exact ancestor equality alone does not prove an arbitrary localized tube inclusion.
4. **First same-set richness (W).** For J disjoint fibers, their lower mass bounds imply J*f_min<=|union F|. Their reference (fiber,b-cell) menu is <=J H(tau/b)^s. Combine the first retained mass, partition richness, and the original rho-cell population cap to get |B intersect F_j intersect Q|_rho >=h_s(b/rho)^s for every occupied pair (j,Q). Spatial reference menu and original total AD lower give |B intersect Q|>=h_t(b/delta)^t. This is derived on one B, including all candidate b in advance.
5. **Actual angular grid and PARENTWISE selection (W/G split).** The floor angular grid on the bounded chart gives actual slope closeness and its cardinality bound (elementary G). `AngularMenuStabilization` already derives menu comparability, a common winning i, global retention, whole-child saturation, and retained direction witnesses. HOWEVER `stabilize_and_select` exports only GLOBAL retained mass. The fractional density premise requires |selected intersect Q|>=|B intersect Q|/(Ks*Kj*B_ang) for EACH parent Q. A new finite wrapper must choose the maximum-weight angular class independently in every parent after fixing i. This is W, but not an inference from the current exported global inequality.
6. **Rich spines to columns (G caller, counting proved).** For every occupied quantized normal column, choose an actual original point, its selected child witness, and that witness's original fiber. The spine is B intersect F_j intersect Q INSIDE Q. Divide its rich rho-cover by the local rho-cover capacity of one a-cell to get >=c h_s H^(-1)(b/a)^s coarse cells. Check the four scalar physical/anchor/slope/time hypotheses of `SpineColumnCounting.physical_spines_column_count`, with h=a/64 and a fixed overlap M. The theorem then derives the reference-column bound; it does not derive those scalar source hypotheses or the spine richness itself.
7. **Six sheared-grid bounds for fractional alignment (G, principal remaining caller).** For the actual quantized original labels in ONE parent, prove the inverse-image weight cap U, density W>=density*U*N_grid^t, and exactly `hspace`, `hcolumns`, `hbins`, `hcell`, `hsegment`, `hstrip` of `FractionalFiberAlignment.fractional_column_alignment`. Respect its grid convention: spatialCell divides BOTH integer shear coordinates; a strip includes ALL longitudinal coordinates. `hcolumns` comes from item 6. `hspace` and `hcell` come from original AD and bounded shear/grid changes. `hbins`, `hsegment`, and especially the FULL-strip `hstrip` come from item 3's all-scale E0 profile. Individual fiber AD is not a substitute for the full-strip cover. Below rho, use a/64>=rho/64 and bounded vertices per rho-cell; do not assume the source profile exists at a/64.
8. **Second refinement, movement, isolation (mostly W).** Quantize and select a heaviest residue PER parent before the fractional call; track the original source labels. `weighted_euclidean_quantization_at_mesh` proves both movement directions and image separation. The fractional theorem constructs final fiber/quotient lower and upper counts at fixed working radii on one final set. Apply parent isolation to the union of those final original-label patches; its RHS is the original patch in THAT input union, not the entire initial A-cell. `euclidean_periodic_patch_at_multiplier` gives the literal open-ball identity.
9. **All-scale/output conversion (W plus elementary metric G).** `DyadicAlignmentParameters` and `DyadicADInterpolation` prove fixed-depth brackets, dyadic interpolation, polynomial-mass heights, and fixed-cost absorption. Still connect monotone geometric ball counts to those profiles, extend dyadic radii to real radii, transfer integer shear boxes to the actual scalar X,Y, and translate by its dyadic parent corner and dilate each patch. Derive quantized P's all-direction tube cover from E0 using actual preimages and bounded movement. Top scales b..64b need bounded-cover/nonemptiness arguments. No all-scale AD conclusion follows from finitely many tests without this step.

The algebraic constructor, menu counting, spine overlap counting, quantization, and patch separation are already verified. The remaining substantive geometric Lean work is items 1, 3, 6, 7 and the explicit tube transport in 9. This is more than import wiring, but it does not currently reveal a new unproved mathematical obstruction.

## 4. Quantifiers, caller, and recommended next assembly boundary

Choose m from zeta; epsilon much smaller than zeta/m; chi_profile from the stopped-profile theorem; eta0 small relative to epsilon*chi_profile. Choose the SECOND fixed-depth radii and each Q exponent/height before M. The first Q may depend on the minimum of the candidate adjacent ratios, so it is fixed before the winning i. With K=2 all epoch/pruning losses are polynomial in M and K_A; budget these, the direction loss N^O(1/m), two uniform losses and interpolation against the FINAL ratio tau_out/a, not the old tau/rho. A safe chi is a further fixed fraction of chi_profile/m.

The actual Step 6 shear quantization has quotient coordinate tau times an integer: `InjectiveSliceQuantization.quotient_coordinate_in_grid`. Its `labelEquiv` preserves original grid labels. The original-data caller must still instantiate the previously derived individual Y_z AD estimates on that exact finite image, and normalize its bounded box. It must not substitute an abstract quotient with the same cardinality.

For incidence-weight retention, use the preceding same-set (height z, quotient y) partition: if occupied y have original incidence weights within factor K_w, geometric retention r gives original weight retention >=r/K_w. This is a caller fact, not an arbitrary-weight promise of the geometric theorem.

Recommended order: finish the finite parentwise angular wrapper; build the actual finite geometric footprint/profile/epoch family; prove a single sheared-grid-reference theorem deriving ALL six fractional premises from those constructed original data; finally compose the two refinements and the existing patch/parameter adapters. Keep any intermediate rich-fiber package as an OUTPUT of the geometric preparation theorem. An intermediate theorem taking such derived fields can aid composition; it must not become the public native theorem's new premise.

Source auditor confirmation (17:16 UTC): the native source is `Theorems/Thm_StickyKakeya4_injective_slice_quantization.lean`; `Index k l=((Fin k->Z) x (Fin l->Z)) x Z`. `labelEquiv` changes only the normal index. The quotient Y_z is literally a finite integer-label image multiplied by tau; `GridQuotientAD` supplies its sup-box AD after the bounded-shear ambient comparison. Keep coordinate permutations/signs and the original absolute grid throughout construction (or quantize relative to the dyadic parent corner). Use the same dyadic parent corner for every k in that patch in the final affine normalization; this preserves the literal lattice and is permitted by the for-every-k affine-map conclusion. A subsequent normalization at an arbitrary original point produces a translated real transverse grid and must carry that translation explicitly.

## Verification updates and explicit quantized tube transport

`/tmp/ParentwiseAngularSelection.lean` now closes item 5's finite exported-interface gap: `stabilize_and_select_parentwise` constructs the common scale and each-parent original-weight retention, all original parents survive, and it exports whole-child saturation and actual retained angular witnesses. Its four declarations passed strict compilation and separate imported standard-axiom readback.

For item 9, quantized all-direction KT needs an actual bounded-movement transfer, not subset inheritance. Work in a bounded-slope graph chart for the tested tube, and let its output width be r>=a. If p_new has source preimage p_old with every physical coordinate displacement <=a/10, then the tested graph residual changes by at most 2a/10 and the longitudinal coordinate by at most a/10. Thus a width-r tube on the new patch pulls back to width at most r+2a/10 and its time interval expands in total length by at most 2a/10. Cover that fixed enlargement by a bounded number of admissible stopped-profile tubes. Equal old r-grid cells can produce only a bounded number of new r-grid cells, because corresponding indices differ by at most a fixed neighboring-cell offset; prove this finite image-multiplicity bound with actual paired preimages.

If the enlarged length exceeds the original stopped tau, first restrict to the original parent patch of side b<=tau and use a fixed finite cover by stopped-length tubes. If the tested width itself exceeds tau, the patch and its a/10 enlargement meet only a dimensional number of width-r cells. Coordinate permutations for the all-direction graph charts preserve the grid. Combine these facts with the SAME E0 inherited profile, then translate/dilate by the parent corner and tau_out. This is a remaining explicit geometric Lean adapter; the new approximating set is not an actual subset of E0.

## Current exported-interface update

`ParentwiseAngularSelection.stabilize_and_select_parentwise` now exports the
each-parent retention and witness properties identified in item5.
`ADGridCoverMenus` and `FiniteCellLabelReduction` now supply the literal
metric-AD grid bounds and raw infinite-label interface. The common actual
tube-family construction and remaining geometric callers are still distinct
from these verified components. See [the checkpoint scope](WZ_NATIVE_ALIGNMENT_INTERFACES.md).
