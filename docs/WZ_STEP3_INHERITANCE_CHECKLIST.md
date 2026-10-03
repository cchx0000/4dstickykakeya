# Step 3 correction: native inheritance and scope checklist

Read-only addendum, 2026-10-03. This freezes the scope of the completed slope-count derivation and records the actual final callers. It does not claim the complete reconstructed configuration has already compiled.

1. **Mesh and exponent.** Use the exact bound

       Delta >= C(1+E+B0) delta (C K_KT/lambda)^(1/gamma),

   rounded up to a dyadic mesh. If lambda=delta^(A eta/epsilon_j), preserve the resulting eta/(gamma epsilon_j) exponent. Choose the incoming hierarchy so Delta remains a fixed positive power of delta. Do not call an O(Delta) correction an O(delta) change.

2. **Translated longitudinal grid.** Native slice x-coordinates are delta(i+1/2), not necessarily delta i. The noisy affine image theorem already accepts x0+delta n. The quotient Y coordinates from `quotient_coordinate_in_grid` are literal delta-integer multiples.

3. **Exact simultaneous correction.** With old lower point p=(x,c+Ax,d+Bx), put q=d-Fc and D=B-C-FA. Then

       H(x,c,q)=(x,c+Ax,q+Cx+F(c+Ax))

   moves only the bottom coordinate, by -Dx, and obeys both exact plane formulas. Quantize the actual coordinates with their original labels attached. Quantizing the constant old lower-grain label q keeps the entire old lower grain in one q-bin; quantizing the actual inverse q_p can split it into boundedly many bins, whose lower counts then need rebuilding.

4. **Raw inverse-coordinate errors.** For actual p=(x,u,v), the inverse is (x,u-Ax,v-Cx-Fu). If the old lower residuals are bounded by e_u,e_v, its constant lower label (c,q) differs from this inverse by at most e_u in c and |D||x|+e_v+|F|e_u in q. An actual higher quotient witness differs from q_p=v-Cx-Fu by the recorded higher residual. These bounds supply the genuine bounded-neighbor maps for later quotient counts.

5. **Lower field continuity.** B_corrected=C+FA is within O(Delta) of the old lower B. Thus its dyadic Lipschitz comparison at every prepared radius r>=Delta follows by adding two O(Delta) errors to the old comparison. No continuity of the higher matrices C,F is used.

6. **Coefficient range.** Do not clip B_corrected entrywise. If needed, the fixed coordinate contraction (x,u,v)->(x,u,v/2) sends C,F,B_corrected to C/2,F/2,B_corrected/2 and preserves the exact identity. For sufficiently small Delta its entries are bounded by one. The native grid/tube/AD constants must pass through the existing fixed-normalization caller, or the auxiliary theorem may temporarily retain a fixed bounded coefficient class.

7. **Actual old lines.** No point-dependent replacement of a line direction is necessary. A corrected point lies within O(Delta) of its old line, so thicken that line to the new mesh. Its unchanged direction satisfies the new lower-plane formula with additional error D phi=O(Delta). When an admissible coarse family is needed, choose actual original line representatives globally per parameter cluster. Do not assign a different new line direction independently to every incidence.

8. **Coarse offsets and old-parent boundaries.** Horizontal movement may cross dyadic r-cell boundaries. To retain literal coarse xi-coherence, use suitable prepared padding or select a compatible OLD-parent branch inside each NEW r-cell. There are only O_d(1) old r-parents that can occur when movement is O(Delta) and r>=Delta. The finite compatible-selector handles these original conditional menus. Prepare all branch, grain and phase maps before the final simultaneous refinement.

9. **Final time labels.** Fix all padding translations and normalizations before choosing an original height for each output bin. Use the ACTUAL shifted time label, or reindex the translated grid and recover the original index explicitly. The selected height is common to the whole output layer. The old higher matrix for that height remains its genuine witness; no unproved Lipschitz bound on the higher field is needed.

10. **Slab-Frostman scope.** The final Step 3 slab transfer concerns only subpower thickening in the SAME bounded direction coordinates, plus fixed normalization. To handle merged fine points, use the final `(new point, coarse angular/phase cell)` partition. Sum actual old per-point slab bounds, keeping the old/final point-degree ratio, and divide by the comparable coarse-cell masses. Do not infer a slab bound merely because each constituent fine cloud has one.

    This DOES NOT transfer slab-Frostman through a genuinely small tau-ancestor restriction followed by anisotropic zoom. Such a restriction turns width r into tau r and can introduce tau^(gamma-kappa), which is not a harmless constant. Step 2 must rerun stopping on the reconstructed same-mesh cloud, or use the automatic one-dimensional kappa-AD bound when its final rank is two.

11. **Both grain populations.** Corrected lower and old higher grain labels each map into boundedly many coarse quotient labels. Prepare their actual reference menus and the original/new point-image fiber caps, then use one combined final refinement to rebuild both lower populations. Exact algebra alone does not prove these cardinality bounds. For the coarse matrix correction, Delta/delta is subpower, so explicit polynomial coarsening losses fit the enlarged eta/(gamma epsilon_j) budget; they must still be written down.

12. **Native alignment input.** The first Step 18.1 alignment invocation is on the literal transverse integer-label set created by injective slice quantization. A lattice-first L5.3 theorem therefore suffices. Coordinate permutations/signs preserve the grid. After real shears or later affine rescalings, keep the explicit translated integer coordinates or reapply the actual shear-floor quantizer. For a dyadic output, choose fixed normalization constants to be powers of two and quantize relative to the dyadic parent corner rather than centering after a real shear at an arbitrary point.
