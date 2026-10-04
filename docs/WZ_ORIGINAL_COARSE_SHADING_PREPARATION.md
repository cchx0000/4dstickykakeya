# Original fine-to-coarse shading preparation

This is a finite, source-preserving adapter for the shadings used in Appendix A. It does not prove the positive-power Furstenberg gain in A.3.

Let `P` be the original finite point set, `T` the original finite tube-label set, and `Y(t) ⊆ P` the nonempty original shading of each tube. Let `h > 0` be the coarse mesh and use the literal two-coordinate floor grid. Write

- `L = floor(log₂ |P|) + 1`
- `M = 2^j`, the selected local shading-fiber occupancy
- `N = 2^k`, the selected number-of-occupied-cells scale

The construction selects an actual nonempty `S ⊆ T` with `|T| ≤ L² |S|`. For each selected original tube, it retains a whole local occupancy class, with every original shading fiber in a selected cell having size between `M` and `2M`. The cell count is between `N` and `2N`, and the original fine shading satisfies

`|Y(t)| ≤ 4 L M N`.

All these counts concern the same original tube and its own shading. They do not replace local occupancy by the largest occupancy of the ambient point set.

## Actual representatives and the union charge

Choose one actual original point in each occupied cell, then one of nine floor-residue colors. The resulting `R(t)` is contained in the original shading and its points have sup-distance strictly greater than `2h`. It satisfies

`N ≤ 9 |R(t)|` and `|R(t)| < 2N`.

Consequently every original tube incidence or shading-membership property passes to its representatives without moving any point to a cell center.

For every choice of representatives, or indeed every subset of the retained whole-fiber classes,

`M × #(union of their occupied h-cells) ≤ |P|`.

The proof pays for a union cell using one actual original shading fiber of size at least `M` inside that cell. Distinct cells consume disjoint original points. This directly gives the fine-point/coarse-cover conversion required after a coarse union estimate.

## The coarse Frostman profile is derived

Suppose the original shading has the fine-point bound

`#(Y(t) ∩ B∞(x,r)) ≤ K r^s |Y(t)|`

for every center and `h ≤ r ≤ 1`, with `K ≥ 1` and `s ≥ 0`. The selected actual representatives satisfy, for every `r ≥ h`,

`#(R(t) ∩ B∞(x,r)) ≤ 18 L K (2r)^s |R(t)|`.

Points in one literal floor cell are within sup-distance `h`, so cells of representatives in an `r`-ball lift to original fine points in the actual `2r`-ball. Lower local occupancy converts this original point count to a coarse cell count; upper local occupancy and the verified retention give the factor `2L`; residue coloring gives the factor `9`. When `2r > 1`, the proof uses the original total point count and `K(2r)^s ≥ 1`, rather than querying the fine profile outside its stated radius range.

## Formal endpoint and scope

`OriginalCoarseShadingPreparation.exists_original_coarse_shadings` executes common-bin selection, actual representative selection, separation, the original-mass bound, the coarse Frostman bound and the union charge. Its premises are the original finite data and original point-count profile. No coarse profile, favorable occupancy class, representative selection or A.3 gain is supplied as an assumption.

Seven implementation modules contain twenty public theorems/lemmas. The adjacent manifest and strict/import logs record their current verification status. This work is separate from the still-unproved robust planar projection/Furstenberg gain needed to complete A.3. Native small-scale parameter absorption, the remaining original radial exclusions and the final paper theorem must still be composed and verified.
