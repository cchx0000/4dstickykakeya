# Two-stage rank refinement on the original finite source

Status: the reference configuration and subset upper lemmas are Lean-checked.
The actual two-stage refinement caller and generic quantitative Gram bound
are also Lean-checked. The global rank/scale producer and complete two-stage
lower-profile caller remain under construction. This note does not claim the final contradiction.

## Why direct re-admission is insufficient

For the actual native source D and its original cubical incidences I, a cut
F contained in I with card(F) at least delta^lambda card(I) gives a native
source D_F at input exponent eta+lambda. Its lines, marks, thickness, and
carrier tree are unchanged, and its global multiplicity lower loses only
lambda. These facts are proved in native_original_shading_restriction.

They do not automatically give a usable extremal upper on D_F. WZ18.2,
Step1 and Step4 (printed pages68–70 of arXiv:2609.22035), choose epsilon1
much smaller than the rank-threshold exponents eta_ell. A cut retaining
c delta_ell^eta_ell can safely require lambda near eta_ell if all we know is
delta <= delta_ell <= 1. The native admissibility allowance chosen for an
epsilon1 upper has no proved lower bound relative to eta_ell. Thus the
condition eta+lambda <= eta0_upper must not be silently assumed. The
conditional direct-cut lemma remains valid; it is not the general rank-stage
adapter under that hierarchy.

## Fixed reference and actual retained incidences

The intended data flow is:

1. Choose the original native D with its actual near-extremal lower, with all
   upper-loss and finite-menu parameters fixed first.
2. Select one original backbone R and a reference incidence set E1. Its
   native upper estimates and original pair/point fiber uniformities are
   verified before any rank cut. All global coarse representatives use R.
3. Construct the actual rank/plane cut F inside E1, retaining its quantified
   mass fraction. This is the Step1 geometric work, not an output certificate.
4. Uniformize only inside F to get E2. Keep R, all original lines and spatial
   cell labels, and the same physical projection maps. The existing exists_retained_scheduled_pair_core applies directly to F,
   with F0=F1/lambda when |I|<=F1|E1| and |F|>=lambda|E1|. It avoids
   choosing a new backbone. A separate cubical-presentation readback is
   needed only if a source constructor is used.

The native source for the upper estimates remains the original reference.
No comparison identifies representatives selected from a new backbone with
the original representatives.

## Upper estimates already justified

If an original finite set E1 has pair and point fiber ratios bounded by Q^2,
then every literal F contained in E1 satisfies

  multiplicity(image(F, physicalPair))
    <= Q^4 multiplicity(image(E1, physicalPair)).

The proof first bounds every point degree of the reference image by its
average, then sums over the actual subset image. It introduces no inverse
retention fraction. The checked declaration is
NativeConditionalCoarseInterpolation.subset_image_multiplicity.

The conditioned version applies to each outer-parent fiber using the
E1-independent conditioned maps in NativeConditionedPairMenu. Formal
old-cell parent upper estimates use the already checked
NativeLocalMenuInterpolation.subset_edgeMultiplicity. These are the relevant
source-faithful comparisons behind the reference-upper use in WZ(110).
They apply only to maps whose reference pair/point uniformities were actually
installed. Conditional images need those uniformities on the appropriate E1
parent fiber; an all-scale upper alone does not supply them. They do not
assert monotonicity of arbitrary average multiplicities.

## Lower budget that must be assembled

If E1 has multiplicity at least delta^(-kappa+nu), F retains a fraction
c delta_ell^eta_ell of E1, and the final finite refinement retains 1/G of F,
then support inclusion gives the actual global lower

  multiplicity(E2) >= (c/G) delta_ell^eta_ell
                         delta^(-kappa+nu).

The finite incidence product inequalities can then combine this lower with
the reference-transferred parent/coarse uppers. The physical coarse bridge
must be applied using E2's own pair/point uniformity. All-parent lower
comparisons similarly need the final formal parent/point uniformity. These
requirements concern relations on E2, not native re-admission at exponent
eta+lambda. The complete same-source caller and all required costs remain
an explicit construction task.

The old IsCore fixed retention constant does not apply to E2 unchanged;
its original retention cost is now F1*G/lambda, which must stay explicit.
A rank cut alone does not preserve pre-existing lower profiles. They must
be rebuilt by this actual global lower and the exact towers. Nor does it
immediately imply a regular active tube backbone or a transverse tuple;
those geometric and counting conclusions require their own proofs.

## Quantifier guardrails

The target upper loss, schedule sizes, and reference radix exponent L are
fixed before D. The actual radix Q is computed from the original source cardinality. Rank thresholds and their finite hierarchy must satisfy the later grain
parameter requirements. The genuine cut scale delta_ell may be selected
from D, but any absorption of c, G, or logarithmic scale selection must be
proved at the already stated source cutoff. A finite branchwise minimum is
legitimate only after all its compatible parameter choices exist. No
unproved lower bound on an arbitrary extremal-admission threshold is used.

The fixed-compact extremal exponent has not been proved zero. The verified
balanced and all-middle-window endpoints remain conditional on its positivity.

## Checked constructive second refinement

NativeRankRefinedReferenceCore.exists_refined_reference_core now constructs
E2 inside the actual F, on the original native D and unchanged R. It derives
F0=F1/lambda, retains the requested finite original relations and local-pair
richness, and proves global multiplicity retention lambda/(F1*G). Every
installed reference physical image upper transfers with factor Qref^4.
The theorem does not claim the sparse E2 is readmitted at a small native
exponent, or carries the old IsCore constant unchanged.

All reference maps must be fixed when E1's relations are installed. A newly
chosen plane-dependent projection is not covered by these reference bounds.
The planned rank-one route uses only original parent/point maps from that
menu, with the geometric plane supplying a bounded parent menu.
