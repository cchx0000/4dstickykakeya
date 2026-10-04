# Actual old-incidence to coarse-incidence continuation

## Concrete map

The original cubical label (tube i, cube k) is mapped to

    (P.cellBin (chartIndex (shift D a) k), i).

The tube i is unchanged. The chart map is injective. P.cellBin is the existing physical shear/floor map at sigma=N*delta_old, with delta_old=delta_original/8. Its whole lattice fibers have cardinality N, and the same N upper bound holds for every retained original incidence subset. This gives |E0| <= N|I| on the actual original E0, without assuming equality between abstract populations.

The point attached to coarse cell c is the actual grid center oldCenter(sigma/R,c). Tube slopes are P.slope; offsets are P.offset/R. The common normalization is R=2(E+2), so for the native error constant E=12 it is R=28. The new mesh is therefore N*delta_original/224.

## Density and geometry

The checked source incidence inequality

    lambda*|tubes(E0)| <= F*delta_old*|E0|

transfers to

    lambda/(F*R)*|tubes(I)| <= (sigma/R)*|I|.

Tube labels are exactly equal as finite images, not just equinumerous. Spatial and time rounding each cost at most sigma/2. Since normalized original slopes are bounded by 1, the raw rounded residual is at most (E+1)*sigma, and the final residual is at most (E+1)*(sigma/R). For the native source this is 13 times the new mesh. The original parent floor label also proves the normalized offset bound; no offset certificate is added.

Actual coordinate labels are injective into physical centers. The actual height alphabet is separated at sigma/R and lies in [-1,1]. A literal height-window restriction is proved to be the image of its actual old-label pullback, and its height diameter is bounded by the chosen window width. No retained density in an arbitrary window is asserted.

## First unconstructed configuration fields

PhysicalRescalingIncidenceTransfer.Data.Hypotheses has density, bounded slopes, bounded times, and physical residuals. It has no AD law for the later normalized tube family. Therefore Definition17.2(1) still requires a separate original-source transfer. The field f(z), the global-grain decomposition, the Y profiles, and fine/coarse angular fields in Definition17.2(2)--(4) also are not supplied merely by this physical map.

The new actual incidences are not declared equal to a global-grain configuration because some cardinality formulas match. The map portion is independent of those missing fields.

## Direct Eq. (146) route

A weighted macro-cell selector uses the literal physical floor-cell label and weight |Z(q)|. Its denominator is exactly the sum over original heights of the occupied physical macro-cell count. Original grain and tangent cell counting bounds one slice by (192/q) times its actual grain q-grid count.

The original AD definition (Definition3.3) is Euclidean delta-COVER AD. Y_z is not separately assumed delta-separated. Consequently the point-count AD calculation is only an intermediate lemma. NativeCoverADRepresentatives constructs original representatives with the same fine occupied grid and point AD constant 100K. A factor-nine comparison then returns a q-grid bound for the FULL original Y set. Fine lower cover mass is itself a lower bound on the original grain cardinality.

This yields a direct original-source macro-cell lower population inequality on unchanged E, with a larger explicit absolute constant. The additional absolute height population |Z(q)|*delta/q requires the scheduled UNION-Y source profile over a dense original height interval. It is not inferred from the E(q)/Z(q) ratio alone.

All new implementations are staged in proof-work. Only modules with a successful strict log and proper imported axiom readback should be described as frozen; other staged files are in-progress source assembly.

The same literal Definition3.3 issue applies to angular alphabets: the frozen angular population lemmas have separated or point-count AD alphabets among their explicit inputs. A full literal caller must produce those actual original alphabets from cover AD and charge the representative/net and angle-error costs. These valid conditional lemmas must not be interpreted as proving that cover AD alone includes separation.
