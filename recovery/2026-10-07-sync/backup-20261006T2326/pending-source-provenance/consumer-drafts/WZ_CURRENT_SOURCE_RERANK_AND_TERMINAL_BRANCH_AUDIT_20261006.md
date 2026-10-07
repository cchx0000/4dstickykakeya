# Current-source reranking and all terminal branches

Read-only audit, 2026-10-06. No Lean edit, build, or new verification claim. Canonical repository: `/workspace/scratch/5f2524fd4117/4dstickykakeya`. Parent remains sole integrator.

Primary source independently checked: Wang–Zakharov, arXiv:2609.22035v1, [PDF](https://arxiv.org/pdf/2609.22035), printed pp.65–76 and 83–90. PDF page index is printed page minus one. The conclusions below distinguish the printed argument, literal repository declarations, and missing geometric construction.

## 1. The decisive correction

Proposition18.1 does **not** prove that a rank-three configuration must become rank two. Its Step2 stops when the newly selected linear rank equals the current reconstructed linear rank. Only the other branch strictly decreases that rank. Consequently, a stable `(k,ell)=(3,3)` configuration is a legitimate terminal output, including when `0<kappa<=1`.

The paper's final contradiction has three consumers:

- `(3,3)`: Proposition17.3, Sections19–20, especially Lemmas20.2 and20.3 and the case split in20.4
- `(2,2)`: Proposition17.4, Section21, using the affine Lemma20.2 and the non-affine Lemma21.1
- `(3,2)`: Proposition17.5, Section22, using the two compatible grain fields and its quadratic/nonquadratic analysis

The source does not replace the first consumer by strict rank descent. In rank three, the scalar quotient has dimension `1-kappa`. Its impossibility when `kappa>1` only establishes `kappa<=1`; it says nothing contradictory in the requested interval. At `kappa=1` a zero-dimensional quotient is allowed. A positive `kappa`-dimensional direction set in R2 may be both AD-regular and slab-Frostman without being forced into an affine line, so the directional hypotheses alone also provide no forced descent.

Proposition17.2 explicitly assumes `kappa>0`; the restatement18.1 omits that phrase even though its proof uses positivity. Keep the original positive-kappa contradiction hypothesis. Neither Proposition18.1 nor Proposition18.2 is an independent assertion that a finite configuration with the desired properties may be postulated.

## 2. Exact target data in Definition17.4

There is one tube family, one mesh, one point set, one time set, and actual incident direction witnesses. All clauses must hold together on these objects.

The underlying Definition17.2 data are:

1. Parameter-AD tube family of dimension `d-1`, with relative CW control supplied by18.1
2. A mesh-separated height set of size at least `delta^(eta-1)`
3. A bounded lower matrix field `f : Z -> Mat(d-ell,ell-1)`, with its prepared-scale dyadic time continuity
4. The exact lower representation `p=(x,y+f(z)x,z)`, dense `(ell-1)`-dimensional X fibers, and Y of dimension `d-ell-kappa`
5. Coarse-time unions of Y are AD at the **coarse** resolution; this is not base-mesh cardinality AD of their full union
6. Each fine point has an actual kappa-AD direction set Phi in R^(ell-1), graph offset xi, and realizing tubes; each prepared physical cube has a common coarse angular cloud and coherent offsets

The additional higher data are a bounded field `F : Z -> Mat(d-k,k-1)`, an exact representation of the same points with dense `(k-1)`-dimensional higher X fibers, higher Y of dimension `d-k-kappa`, tube KT exponent `1-gamma`, fine Phi slab exponent `gamma>0`, and the compatibility identity

`f_bottom = F_left + F_right * f_top`.

There is no higher-field dyadic continuity requirement and no higher-Y coarse-time-union clause in Definition17.4. This matters when old heights merge: replacing their higher fields by a representative is unjustified unless one actual old height is chosen or a genuine factorization is proved.

For `(3,3)`, lower and higher fields coincide, X has dimension2, Y dimension `1-kappa`, Phi lies in R2, and compatibility is tautological. For `(2,2)`, X dimension1, Y dimension `2-kappa` in R2, and Phi lies in R. For `(3,2)`, lower X/Y dimensions are1 and `2-kappa`; higher X/Y dimensions are2 and `1-kappa`, with both representations on the same points and the nontrivial compatibility identity.

At linear rank2, the one-dimensional AD upper count gives slab-Frostman after normalizing by the actual total count. At planar rank3, scalar Y AD gives tube KT of exponent `1-kappa`, hence the desired exponent `1-gamma` whenever `0<gamma<=kappa`. Constants may enlarge. For a contradiction with `kappa>zeta`, choose e.g. `gamma_star=min(gamma,zeta/2)` before downstream loss thresholds; do not silently use a larger gamma in those thresholds.

## 3. What equations143–144 actually return

At the end of Step1, the higher rank k and its tube-KT deficit have been fixed. Lower directional rank ell can still be smaller than k. Step2 selects the least concentrating physical direction rank on the **current** point/tube incidences.

- If the selected rank equals ell, the no-concentration condition for physical `(ell-1)`-planes yields a fine angular slab law. No strict rank decrease is claimed.
- If the selected rank ell' is smaller, keep actual current incidences near the selected ell'-plane. The concentration threshold gives a quantified retained fraction. Reconstruct global `(ell'-1)`-grains through the rest of Proposition18.2, while rebuilding the old higher representation143.
- Rerun the test after this reconstruction. The anisotropic normalization can destroy the previous slab law. Equal rank now terminates; otherwise the linear rank decreases again. Rank1 is excluded using the extremal multiplicity/source argument, not by finite-dimensional linear algebra.

Equation144 is a count relative to the current pre-plane-cut point fiber. Passing to a later fiber needs its actual relative population. It is not a bound relative to a larger historical fiber with that denominator deleted.

In four dimensions, there is at most one strict descent from linear rank3 to2. The equal-rank3 terminal branch remains. Rank k is preserved through the directional descent; it is not reset to ell'. Thus a strict descent with k=3 leads to `(3,2)`, not `(2,2)`.

## 4. Same-source requirement and scale-source admission

A new unrelated extremizing source is not needed or permitted as a replacement for the current object. A strict reconstruction generally does create a **new finite scale source as a geometric image of the same retained original labels**: coarsen, choose an actual tube parent, shear/dilate, and form the incidence image. Its native source laws, shading density, and near-extremal bounds must be proved.

The fixed-source Reference boundary is useful precisely because it can build a reference from one specified source S. Its identification of the original cubical rows preserves old tube and cell labels. It does not imply that a later rawHeight or translatedHeight determines the old higher field, and it does not preserve lower X/Y populations after arbitrary cuts.

Reinvoking an existential original-source frontend to obtain a different D would discard the selected higher history and would not implement equation143. Likewise, taking an arbitrary sparse shading of S and calling it native is invalid. Carrier upper estimates may restrict; shading lower and all conditional lower profiles need a new proof on that shading/image.

The source proof invokes endpoint extremal estimates under an infimum definition. A formal implementation should use the repository's proved epsilon-slack critical-exponent estimates at the requested scales, rather than assume that the infimum is attained. All such slack belongs in the quantitative budget.

## 5. How old higher grains can survive a strict step

The existing higher-grain retention note gives a valid *conditional counting mechanism*, not an already connected constructor. Here is its decisive calculation specialized to d=4,k=3.

Let the old point mesh be epsilon, P the old points, and I0 the original current incidences, with common label weight w. Suppose old higher grains are disjoint point classes containing at least `g0*epsilon^(-2)` distinct points. Suppose total mass is at least `w*A^(-1)*epsilon^(-kappa)*|P|`; one fixed tau-parent has at most `w*A*(tau/epsilon)^kappa` incident mass above one point; and each occupied spatial tau-cell has at most `A*tau^(-kappa)` actual tau-parent possibilities.

The genuine joint key is

`(old higher grain, spatial tau-cell, tau-tube parent)`.

A bounded affine2-plane meets `O(tau^(-2))` spatial cells. The number of original keys is at most

`C*g0^(-1)*|P|*epsilon^2*A*tau^(-2-kappa)`.

If the final simultaneously prepared refinement retains mass fraction r and has comparison factor K, each occupied key can be made to carry at least

`c*r*w*g0/(K*A^2) * (tau/epsilon)^(2+kappa)`.

Dividing by the actual conditional point degree gives at least

`c*r*g0/(K*A^3) * (tau/epsilon)^2`

distinct old points. If coarsening is at rho before zooming by tau, an output point cell contains at most `C*(rho/epsilon)^2` old points from one fixed-height higher grain. Thus the new occupied higher grain has at least

`c*r*g0/(K*A^3) * (tau/rho)^2`

distinct output points. This is the needed dense higher-X exponent at output mesh `sigma=rho/tau`.

These hypotheses must come from the actual current source/maps. In particular the local tau-parent menu is not the global number of parents, and the point-degree denominator cannot be replaced by1. The next-configuration worker is deriving the fixed-S angular/cube bounds that feed this calculation; this audit does not duplicate them.

The old grain label already includes its old fine height. At a fixed old height the actual horizontal shear/dilation preserves its plane slope. Select one genuine old height per new time bin if needed, common to the whole output layer. Install the corresponding new-lower-grain-plus-old-height labels as well: otherwise a later height choice can destroy the newly constructed lower grains. Both families' distinct point counts, the full selected-slice ambient AD, and the appropriate quotient AD must then be rebuilt on the same final set. Keeping an upper KT estimate or a remembered field alone does not supply any of those lower bounds.

The source's final correction makes the lower and higher representations compatible. Before that correction, two independently snapped exact formulas cannot simply be asserted on one point set. The correction is at its actual enlarged mesh, with old line indices retained and tubes thickened; the source labels/masses remain traceable.

## 6. Why the original slab law cannot simply be transported

Restricting a kappa-AD cloud to a tau angular parent typically keeps a fraction comparable to `tau^kappa`. Under zoom, a new width-r slab pulls back to old width `tau*r`. An old slab upper bound proportional to `(tau*r)^gamma` therefore normalizes on the restricted cloud with an extra factor

`tau^(gamma-kappa)`.

For `gamma<kappa`, this is a large loss when tau is a power of the original mesh. It is not a fixed dimensional constant. In addition, several old point fibers can merge into one new point, with different old graph offsets/planes. The needed coherent field must be chosen before that identification, or proved by the actual merged-point construction.

The repository already has the explicit graph-slab-to-physical-plane geometry, including `NativeSlabOriginalPlane.original_point_slab_near`. It preserves the actual original tube index and gives original error `(2*r+e)/N`. That is a valid entrance to a fresh current-family rank test. It is not a slab-Frostman conclusion by itself.

## 7. Strongest concrete next rank-three lemma

Recommended next target: **current-source rank-three slab-or-lower-plane selection**, applied to the actual rank3 physical third-stage object. This is useful throughout `0<kappa<=1` and does not ask the caller for the desired rank2 output, slab law, or a new certificate.

Inputs are the existing actual source/third-stage data, its same-source incidence rows, fixed current graph field/offset readbacks, and the predetermined rank radius/exponent menu. Construct the containing physical3-plane from the actual graph field. Its geometry proves admissibility of rank3 at a menu radius exceeding the actual graph error. Modify the finite least-rank selector so this genuine plane supplies the top admissible rank, rather than using ambient rank4.

The output is a common rank/scale, a literal subset of the current incidences, exact point-fiber near-plane descriptions, retained current mass, and failure at each smaller allowed rank. Then:

- rank3 gives no concentration near physical2-planes on the current fibers; combine the actual slab pullback, literal direction witnesses, and paid radius interpolation to obtain a terminal weighted angular slab upper bound
- rank2 gives actual physical2-plane concentration and retained original labels for the strict reconstruction
- rank1 is ruled out by the same-source rank-one budget after its real multiplicity/source prerequisites have been established

`NativeIncidentRankSelection.exists_rank_scale_retention` already proves the finite selector with ambient rank4 as fallback. Its proof can be capped by the constructed rank3 plane; selection retains original incidence degree as point weight. `NativeTwoStagePlaneRank` proves exact rank from quantitative lower-rank failure, but does not create a new current reference.

For terminal slab normalization, if Phi has a realizer map to the current tube fiber with fiber cap J and current tube count at most D times |Phi|, a physical-plane failure `count<=A*s^beta*current_degree` gives

`|Phi in slab_r| <= J*D*A*(C*r)^beta*|Phi|`

at directly tested radii. The native tube/grid geometry and current angular profiles must derive J,D. They are not inferred by reversing a one-way map. For the initial implementation, the weighted pushforward of the **actual current incidence mass** avoids conflating duplicate fine labels with distinct angular points; its conversion to unweighted Phi must remain explicit.

A finite mesoscopic menu does not cover all slab widths automatically. Pay the actual interpolation ratio and both endpoint gaps. In particular, ball-AD in R2 does not supply the missing arbitrarily narrow line-slab upper bound. The supplied lower-menu slab estimate can extend downward only with its explicit power loss. This dependency should be coordinated with the finite-menu interpolation worker.

The finite capped selector plus actual graph pullback is the strongest short next proof step. Completing its strict branch requires the geometric reconstruction in section5. Completing its stable branch requires the Section20 consumer below. Neither is formal packaging of the selector.

## 8. Source-native terminal consumer inventory

### Terminal(3,3)

Need the full lower global2-grain data from section2, current fine slab-Frostman, and scalar Y all-radius AD/KT, all on the same native tube family with CW. No additional higher-field construction or planar Lemma5.3 is needed once these data exist.

Actual final source consumer: Proposition17.3. Section20.4 splits the actual vector slope `f:Z->R2` into approximately affine and non-affine time pieces. The affine branch uses V-tuples, a nondegenerate direction difference from slab-Frostman, the quadratic time image, and scalar KT (Lemma20.2). The non-affine branch uses L-tuples, genuine projection-fiber bounds/dense additive graph, and the nonlinear scalar growth theorem13.5 (Lemma20.3). The simultaneous scalar-projection argument uses two transverse differences in dimension4.

Repository boundary: `NativeActualHeightThirdJoin.attach_rank_three` constructs common height/support/residue cuts and calls the actual third-source continuation. Its result is `HasThirdXYSourceData` plus same-field and same-height readbacks. It does not yet establish the full global configuration or Proposition17.3. Independent consumer inventory found no actual native Section20 terminal consumer. The separate `kappa<=1` result is not a substitute.

### Terminal(2,2)

Need full global1-grain data, planar Y of dimension `2-kappa` with a positive tube-KT deficit, and CW. Phi is one-dimensional, so its actual AD gives slab-Frostman. Here higher and lower fields coincide.

Actual final source consumer: Proposition17.4. Lemma20.2 handles approximately affine f; Lemma21.1 handles its genuinely non-affine vector-valued case. The known one-T5/low-s alignment path is a rank2 producer for this branch, not its complete final contradiction.

### Terminal(3,2)

Need full global1-grain data and the same points' higher2-grain representation, scalar higher Y of dimension `1-kappa` and tube KT, the exact compatibility identity, and CW. Fine directions lie in R, so no separate rank3 slab stopping is required once the true rank2 angular AD is built.

Actual final source consumer: Proposition17.5. Section22 needs the two-field V/L identities, then its quadratic/nonquadratic analysis; its three-dimensional radial/Kaufman inputs cannot be replaced by the planar scalar versions merely by renaming them. The current oneTwo/high-s fixed-S reconstruction is a legitimate direct route into this branch and may avoid another rerank. The next-configuration worker confirms its scope is precisely this branch; it does not cover terminal(3,3).

## 9. Required quantifier and cutoff order

1. Assume the original critical exponent is positive and choose the contradiction gap, e.g. zeta=kappa/2.
2. Fix each possible branch's positive transversality/KT deficit and target accuracy first. Rank2 allows gamma<=kappa; k=3 scalar KT allows the same weakening. For all terminal outcomes take a finite positive set of weakened gamma values and accuracy budgets valid for every required consumer.
3. Fix the finite rank thresholds, interpolation accuracy, reconstruction loss budgets, and all parent/source admission cutoffs. Incoming losses must pay every division by a scale power gap, slab exponent, and KT deficit.
4. Only then invoke the original arbitrarily fine near-extremal source. After selection one cannot retroactively require its eta to beat a cutoff depending on unprepared output data.
5. At each geometric image prove an actual positive power window `delta_new<=delta_old^a`, a>0, or an equally explicit alternative controlling both mesh and exponent conversion. An upper bound by a fixed cutoff alone does not turn `delta_old^(-eta)` into a small `delta_new` loss. The repository's rank power cutoffs can supply this where their actual scale identities apply.
6. Step3 needs a correction mesh of the form `Delta>=C*delta*(C*K_KT/lambda)^(1/gamma)`. Preserve the resulting `eta/(gamma*epsilon_j)` dependence. Choose the budgets so the mesh exponent stays positive, preferably with a fixed margin such as at least1/2. Transfer all clauses at Delta, not at the old delta.
7. Set the final mesh cutoff against h at the final, enlarged eta and weakened gamma. A finite branch tree allows all such cutoffs to be precomputed before the original datum. Positivity of each source/coarsening gap, not just finite rank termination, is essential.

The manuscript compresses these choices and has several display slips. In particular Step3's prose switches the KT parameter between gamma_j and1-gamma_j; its grain-size display145 omits the expected dimensional +1. Use the consistent exponent `1-gamma_j` from143 and the dense `(ell'-1)`-grain requirement of Definition17.2. Do not interpret the slips as stronger hypotheses or derive an artificial contradiction from them.

## 10. Missing geometry versus remaining formal joins

Formal joins: cap a finite least-rank selector, sum current-label masses, interpolate a finite radius menu with its paid powers, carry an unchanged label through restrictions, apply the already explicit graph-slab pullback, and check finite branch budget inequalities.

Genuine geometric/source work: current-source angular/ambient estimates; re-admission of a geometric image with its actual shading; coherent planes before point merging; higher-grain local parent populations; simultaneous lower/higher distinct-point reconstruction and quotient AD; the Step3 correction's same-set inheritance; and the terminal Section20/21/22 contradictions.

A faithful immediate program therefore has three open tracks: finish the actual rank2 low-s branch, finish the actual rank2/high-s two-field branch, and construct the stable rank3 global configuration plus its Section20 consumer. The current-source capped rank/slab lemma is a useful shared entrance for the third track and the strict-descent subcase. No axiom, new root measure, or replacement extremizer is involved.
