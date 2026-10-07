# Rank-three source bridge audit — 2026-10-06 23:20 UTC

This is a source inspection, not a new Lean verification receipt.

## Checked geometry output

NativeActualReferenceOneTGeometry has four declarations, source SHA 99140820a2c89d8f8fc60714aa6e062c768b05aab4943b933503eb2254eb93e6, olean SHA 73f1f0fb29539825c61f775d4325798b86684cf4e45c5eb89f65e124a1893f6d. Its source check and independent readback passed at 23:06:29 and 23:08:28 UTC. It retains the same raw f metric and xi residual on the final T. Its public wrapper is rank two only.

The exact old residual is (5/4)*rho(m)^(1-2*epsilonGraph). The actual base chooser pays this by 64*eps, hence by 64*d when eps<=d. It does not prove error<=d. Dilation by 2^c=64/w gives at most 4096*sigma for this old residual when sigma=d/w. Representative-slope rounding is an additional term and must remain visible. A coordinate error sigma gives a safe additional quotient error 6*sigma.

## Existing rank-three data

NativePhysicalCoherentThirdJoin.from_actual_source supports both ell=2 and ell=3. It constructs the actual xi and residual on Sfull and retains the same original metric, field and witnesses through its subset continuation.

NativeActualHeightThirdJoin.attach_rank_three works with finrank(P)=2 and matrices Fin 1 by Fin 2. It performs the same whole-point height/support selection, then the unique third refinement. It supplies exact frozen fields, one original translated height per final height, and HasThirdXYSourceData at ell=3. Whole-point fibers are retained in the pre-third U; arbitrary full old point/grain fibers are not claimed in final T. Final T has the actual mixed-fiber lower and uniformities.

## Rank-free actual source machinery already available

NativeActualRawWeightSource.raw_cardinality_lower and paid_raw_cardinality_lower use literal Hp population and Hp-to-T incidence retention. Their raw normalization is deltaOriginal*rParent^3. They do not depend on ell.

NativeActualRawWeightSource.exists_same_Q_source constructs the actual intermediate C with its Q, real representative lines, native input and shading lower. NativeActualRawRememberedSource.massive_old_phase and select_raw_height_and_shading then select an actual old phase and true original k3 in each final bin. They construct Efinal and the literal source Sout with genuine shading lower, without a rank assumption.

NativeRememberedSourceAdmission.native_of_selected_shading admits this same Sout from its actual shading lower, original intermediate native source and AD/CW/density budgets. It is rank-free.

## Earliest explicit rank restriction

NativeActualRawRememberedSource.exists_same_Q_source invokes NativeRememberedSourceUnion.rank_two_union and takes ell=2, finrank(P)=1. The three geometry wrappers rank_two_from_third, configured_gap_of_coarse_XY and actual_fiber_card are likewise specialized to oneTwo. The new literal source construction and shading lower themselves do not require rank two.

The low-level source_height_cell_base_keys and coarse_xy_old_dist are already generic in ell. Thus a rank-three union upper should be proved using ell=3 and split twoOne, on the complete original T XY slice, while later cuts contribute only subsets/occurrence images. Its exponent remains 3-kappa plus one time dimension. This must be checked at the actual wrappers before claiming that no new counting lemma is needed.

## Further Section20 obligation

Even after rank-three shading and union bounds are joined, full X/Y lower data on the new source Sout does not follow from subset membership in old T. The old HasThirdXYSourceData includes normal Y exponent 1-kappa at ell=3, but later phase and height choices can cut those fibers. A source-facing reconstruction or a proved retention/fiber transport on the literal sourceCells is still required. New native admission alone is not that reconstruction. The original residual must also be read through actual representative lines and retained occurrence witnesses; this is the current small attachment task.
