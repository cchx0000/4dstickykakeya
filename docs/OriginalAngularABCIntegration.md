# Original source-Phi and actual planar ABC input

This batch uses the literal common angular alphabet supplied by Definition17.2(4), not an assumed regularity law for an arbitrary incident-angle image. Translation alone preserves the source AD constant and mesh exactly; subsequent common-mesh refinement and the final factor2 angular normalization have explicit costs.

## Constructed angle labels and graph

`OriginalReferenceAngleSelection.source_common_angle_near` combines original fine-direction realization and common-Phi coverage. `angle` chooses an ACTUAL element of that source Phi for each original incident tube. This avoids the boundary problem in identifying the floor of a perturbed tube direction with a source Phi cell. `angle_fiber_cap` charges the actual chosen-angle fibers to ORIGINAL scalar direction balls. `exists_full_reference_rich_core` derives menu degree normalized against the FULL reference cardinality |Phi| from original W mass and original incidence counts.

`OriginalReferenceAngleGeometry` proves original grain drift and the signed anisotropic phase relation for this reference-angle map. Its geometry radius must dominate fineError+coarseError; choosing a fixed enlarged radius is permitted but must be tracked. `NativeReferencePhaseWindowGraph` constructs the maximal occupied phase window and actual dense graph with this exact reference alphabet.

The already recovered BC9 batch then fixes an actual original height/angle and selects height fibers by actual graph mass. The source Phi is not pruned by those steps. `OriginalAngularGraphTranslation` translates its scalar labels and graph exactly, preserving cardinality and density and recovering every original edge.

## Literal C regularity

`OriginalAngularAlphabetTranslation` proves cardinality, mesh, separation, AD, box and lower-cardinality transfer for C=Phi-angleAnchor. Source Phi⊂[-1,1] implies C⊂[-2,2].

`OriginalAngularFrostman` derives the all-center/all-radius relative law from point-centered AD. At finer common mesh mu≤q, the explicit constant is 2^kappa K^2(q/mu)^kappa. It includes radii below q, rather than treating the finer mesh as a free change.

`OriginalAngularBalancedFrostman` implements the final C/2 normalization. It keeps cardinality exactly |Phi|, lies in [-1,1], is separated at q/2, and at ABC mesh mu with 2mu≤q has relative Frostman constant

    2^kappa · 2^kappa K^2 (q/(2mu))^kappa.

`weaken_upper_exponent` only weakens the upper Frostman exponent on radii≤1; the original cardinality lower bound and original exponent remain untouched. For larger radii use the trivial whole-set bound. This supports the later fixed kappa*=zeta/2 application on the nontrivial kappa>zeta branch.

## Actual point sets and small output cover

`ActualPlanarTargetCover` constructs the floor-grid output cover from actual original targets, giving (2error/mesh+2)^2 |A0|. It then uses beta|A0|≤loss|Aret| to charge the original target set to the retained source set. It never requires an old target to survive vertex pruning.

`PlanarABCBalancedNormalization` performs

    A ↦ A/8,   B ↦ (B-anchor)/4,   C ↦ C/2,
    mesh ↦ mesh/8.

Products scale by exactly 1/8. The projected original-target error 2E+(1+|c|)rho with |c|≤2 becomes (2E+3rho)/8. Its cover factor at mesh rho/8 is exactly (4E/rho+8)^2.

`ActualABCImageAssembly` constructs actual finite point images and their actual image graph; injectivity proves all cardinality and density identities, and the actual sumset-cover bound follows from actual old targets. `PlanarABCProjectedProfiles` transports separation, ball and line-strip profiles through the balanced B normalization and injective point images.

## Genuine output constructor

`NativePlanarABCInput.exists_actual_planar_ABC_input` invokes the graph-aware projection theorem directly. It constructs a `Data` value containing actual unit-box finite A,B,C,G, nonemptiness, common-mesh separation, relative B and C Frostman laws, B line-strip avoidance, graph density and an actual small sumset cover. Its C is exactly the balanced original source Phi. Both retained A/B upper cardinality bounds and original-to-retained lower comparisons are returned.

Let rho denote the ACTUAL projection mesh, beta the incoming actual graph density, D_i=graphLoss(J,rho,K_i,beta), L=108 D_A D_B, and mu=rho/8. The output constants are:

- graph density beta/L
- B relative Frostman constant 400 D_B L/(beta lambdaB)
- C relative Frostman constant 2^kappa·2^kappa KPhi^2(q/(2mu))^kappa
- B native strip width w/4 and strip fraction (L/beta)theta
- sumset cover constant (L/beta)(4E/rho+8)^2

Native strips normalize the maximum of the two normal coordinates to1. For Euclidean-unit-normal strips, a fixed width factor2 is sufficient, so use w/8 when connecting to a Euclidean tube-width statement.

The original spatial inputs are supplied by the earlier phase population, coarse-height KT1 and source167 tube-transfer producers. The local original-edge relation and original target witness come from the original W phase identity and original menu/height-edge lifting. These are original-space inputs, not desired projected or ABC certificates.

## Precise remaining numerical/source obligations

1. The native lambdaB premise is lambdaB≤rho·|B_original| at the ACTUAL projection mesh. It is not inferred from absolute KT1. `OriginalCoarseHeightPopulationRatio.original_coarse_height_mass` supplies

       betaHeight*lambdaHeight/(3Lheight) ≤ (sigma/rhoGeometry)|B_coarse|

   from original fine-height separation/density, graph-selected retained mass, and sigma≥delta. Any common spatial rescaling or change of projection mesh must adjust this lower bound by the corresponding mesh ratio.
2. The projection scalar condition remains explicit:

       3(kappaClose+epsilonLine+128w/(r0w0)+2parameterMesh)≤theta^3.

3. Source167 uses a strict affine tube; its normalization requires the strict buffer Lip*rhoGeometry*(wFine/etaVertical)<rhoGeometry^(1+epsilon0). Coarse representatives widen original cross tubes by2sigma/rhoGeometry.
4. The quarter-scale route rhoGeometry≈delta^(1/4) with epsilon0<1/8 supplies a possible gap between representative error and delta^(2epsilon0) avoidance width. This gap is NOT automatic for all rho=delta^mu with independently tiny mu. Scheduled-scale and Lip losses still need the numerical budget.
5. The remaining Lemma21.1 closure must choose native parameters and invoke/prove the deep ABC expansion theorem. On kappa>zeta, use a fixed upper Frostman exponent zeta/2 for uniformity while retaining the ORIGINAL C cardinality lower bound. No final Lemma21.1/Proposition17.4 claim is made by this finite constructor.

## Verification

Sources, oleans and logs are durable under `proof-work`. `OriginalAngularABCReadback.lean` properly imports the final chain and prints every public proof declaration (definitions are not counted). The JSON manifest lists each source hash, public theorem/lemma names, strict log and proper-import axiom log. The prior recovered BC9/35-proof batch is linked separately.
