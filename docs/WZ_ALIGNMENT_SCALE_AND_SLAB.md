# Actual scale selection, alignment witnesses and slab planes

Verified 2026-10-03. Seven new modules add 88 strictly checked proved
declarations with standard logical axioms only. The full 247-module default
build passes 8,956 jobs. All previous 240 source hashes are unchanged;
cumulative recorded checks are 1,726.

`CoverProfileStopping` now constructs the scale pair from the actual positive
integer cover counts and their elementary tube bound. The finite improving
pair recursion proves both the common nested upper profile and a positive
power separation. The canonical improvement budget is ceil(2/epsilon).
`CoverProfileClipping` derives the admissible exponent min(s,t,1) with the
explicit CD loss from the geometric and AD count bounds; it never infers an
exact exponent inequality by ignoring finite-scale constants.

`FiniteCoverProfileEpochs` constructs the profile as a finite maximum over
actual tube footprints, derives monotonicity and positivity, chooses an
attaining footprint, and extracts all its current cells. It calls the proved
epoch constructor with this genuine extraction rule, deriving rich disjoint
original-point fibers and exact selector identity. Its finite cell-label
codomain can be the finite collection of labels used by the original points;
a native infinite grid requires that count-preserving relabeling.

`GraphTubeGridCover` proves the geometric profile input on the original
unshifted grid. A coordinatewise thickened segment in dimension n+1 meets
at most 9*8^n*tau/rho grid cells. The proof chooses a maximal direction
coordinate, uses only a coordinate permutation, and counts actual floor
labels in the resulting translated graph tube. Euclidean tube membership
supplies its coordinate-error assumptions. No covering estimate is assumed.

`AngularMenuStabilization` derives occupied menu comparability from the
actual spatial and joint spatial/angular class masses on one source. It
finds an adjacent bounded-growth scale pair and selects whole original
fine-cell fibers with genuine retained angular witnesses. Its exact loss
is K_s*K_j*B.

`EuclideanAlignmentPatches` upgrades the preceding explicit patch and residue
construction to literal Euclidean balls: each retained original point sees
exactly its own patch, and the quantized image is a-separated with both
approximation distances below a/10. Original weight retention is proved.

`SlabPlanePullback` constructs the affine-slab kernel, its graph image plane,
and a corrected point witness. It proves the plane dimension, the physical
error bound, the infimum-distance statement, and unit-direction normalization.
The norm scope is explicit: an inner-product source and normed target with
maximum product norm. Native Euclidean coordinate conversion is a separate
interface, rather than an unstated identification of norms.

The whole original AD-input-to-alignment Lean theorem remains unassembled.
The remaining native interfaces include the literal AD-to-grid covering
menus, fixed-depth all-scale parameter assembly, and reconstruction of the
full simultaneous configuration. The [parameter checklist](WZ_ALIGNMENT_PARAMETER_CHECKLIST.md)
and [higher-grain reconstruction audit](WZ_STEP2_HIGHER_GRAIN_RETENTION.md)
record these handwritten connections. The latter keeps total shading density
and tube multiplicity separate, and distinguishes pure rescaling from prior
physical thickening.

The final main theorem still uses the preexisting WZ volume axiom. No new
axiom has been introduced, and no complete main-theorem proof is claimed.
Prove2Me remains unauthenticated, with no platform submission.

[Exact hashes and checks](../verification/wz-alignment-endpoints-checkpoint.json)
