# Exact planar native Lemma 5.3 adapter audit

Source inspected: supplied Wang–Zakharov arXiv:2609.22035 PDF, printed page 23, Definition 5.1 and Lemma 5.3; its local text is `/workspace/scratch/5f2524fd4117/paper-audit/wang-zakharov-2609.22035.txt`, lines 1135–1149. Repository target: `docs/WZ_NATIVE_ALIGNMENT_ASSEMBLY.md`, section 1. Paper Definition 3.5 uses occupied dyadic cubes for the covering count.

## Scope proved

`NativePlanarLemma53.native_planar_lemma53` treats finite original plane sets with sup-metric diameter at most one and native real-radius AD. `native_quarter_square_lemma53` consumes the exact native quarter-square input directly, so it needs no global rescaling. Its quantifiers are: every zeta>0 admits eta0>0 and chi>0; for every 0<eta<=eta0 there is delta0>0; every original source at 0<delta<=delta0 with t in [0,2] has the stated output. No tube, angular, stopping, spine, density, or output-profile input is supplied. Input separation is unnecessary for this stronger finite source statement, so separated native lattice sources are included.

This is the planar native replacement with a proved positive chi, not a proof of the printed explicit formula for chi(zeta), the arbitrary-dimensional statement, or the full [-1,1]^2 input under the same tau<=1 normalization. The quarter-square case is the repository's stated minimal native caller. No claim t-s<=1 is made.

## Literal field matching

- The original retained labels are converted to an actual `A' : Finset Plane` with `A' subset A`, nonemptiness, and exact cardinality equality; no incidence weight is substituted for original point cardinality.
- Set rho=64*mu and tau=64*b. The construction proves delta<=rho<tau<=1 and both rho and tau are delta times natural powers of two. The power gap is tau/rho>=delta^(-chi).
- The separated output mesh is e=rho/tau=mu/b. The scalar raw coordinate grid is finer, but its factor 64 has already been absorbed before this adapter. The literal AD and tube constant is exactly e^(-zeta)=(b/mu)^zeta.
- Retention is e^zeta*card A<=card A'. Since delta<=e, the additional delta^zeta retention follows. The ratio-retention is the paper's stated form.
- Each local patch is the actual open Euclidean ball `A' intersect B(a,tau)`, not an arbitrary chosen parent subset with an unverified local identity.
- `normalization j a tau` is a genuine Lean `AffineMap`: p maps to tau^(-1)*(chartPoint j p-chartPoint j a). Only translation, dilation and coordinate permutation act on the source. The selected shear is retained as the graph slope in the approximating set. The main affine-map conclusion and native coordinate-permutation convention are respected; the stronger printed orientation-only remark is not separately asserted.
- `NearlyLiteralAligned` is consumed by the final theorem on that actual affine image. Its witness is a genuine finite plane set with Euclidean e-separation, unit-square bounds, and two-way Euclidean distance strictly less than e.
- `LiteralAligned.fibers` supplies actual finite scalar Y, subtype-indexed nonempty X_y, bounded slope, literal graph equality, and existing `FiniteVoronoiRealADCoarsening.ADBounds` for Y at exponent t-s and each X_y at exponent s. Counts are closed metric-ball cardinalities, with no metric loss in this conversion.
- The same witness also has Euclidean ambient AD and all-direction `TraceBound`, which counts the occupied physical rho-grid cells in a genuine sup-distance segment tube. This is precisely the explicit tube/grid convention permitted by the native target; it is not a coordinate-direction-only estimate.

## Dependency and trust boundary

The final native statement consumes the actual source-only construction and the complete constant expansion. The dominant loss is C_fixed*I*epochCost*F1^2*F2*Q1^8*Q2^2*K^18*R^(3m*epsilon+1/m+2/H). Actual radices, source cardinality, K powers, epoch budget, and top dyadic scale are derived from the source. The choice of fixed parameters precedes delta, and output-ratio absorption preserves a positive original/output power gap.

This alignment result does not supply the subsequent dimension-raising, slab-Frostman, slope-consistency, or final sticky-Kakeya contradiction constructions.
