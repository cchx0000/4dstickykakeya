# A completed handwritten finite adapter for WZ Lemma 5.3

Independent audit and continuation, 2026-10-03. This combined mathematical argument is not itself a Lean theorem. Primary source: supplied Wang–Zakharov arXiv:2609.22035 PDF, Lemmas 5.2–5.3, printed pp. 21–25; its later invocation is Proposition 18.1, Step 1, pp. 74–75.

This note independently checks the construction in [the disjoint-fiber preparation](WZ_ALIGNMENT_DISJOINT_FIBER_REPAIR.md) and completes its transverse-product and literal local-ball conclusions. It uses the already proved finite self-uniform and compatible-selection mechanisms; the new geometric arguments remain handwritten until their actual callers are formalized.

## 1. Result and necessary preparation change

The disjoint-fiber preparation repairs the missing point-shadow inference. Together with the two-stage construction below, it yields the required nearly aligned local pieces with original-point retention, one common output scale pair, and the required tube Katz–Tao bound. It does not use slab-Frostman stopping, a global grains certificate, or a presumed quotient AD conclusion.

One convenient change to the preparation is to start its cover-profile process at `(delta,tau_max)`, where tau_max is a fixed sufficiently small dyadic dimensional constant, rather than `(delta,1)`. Choose

    C_ball = 10d,
    tau_max <= 1/C_ball,
    L_patch = 4 C_ball + 4.

This costs only fixed dimensional factors and preserves a fixed positive power separation for sufficiently small delta. It ensures the final local-ball radius, C_ball times the chosen parent size, is at most one in the ORIGINAL coordinates. No rescaling back to an output radius larger than one is needed.

## 2. Independent audit of the disjoint-fiber preparation

Let A be delta-separated and (delta,t,C_A)-AD, t in [0,d]. At every stage the residual E is an actual subset of the original A.

### Cover-profile stopping

For fixed E define M_(rho,tau)(E) as the maximum occupied rho-cell count in a rho-by-tau tube. Its maximum exists because the realized counts form a nonempty bounded set of natural numbers. The elementary tube cover gives

    1 <= M_(rho,tau)(E) <= C_d tau/rho.

At an improving nested pair, the exponent increases by at least epsilon and the scale ratio satisfies R_next >= C_d^(-1) R^epsilon. Thus, after choosing delta small, the process stops after at most ceiling(2/epsilon) steps with R>=delta^(-chi_profile). The use of COVER counts avoids assuming lower density in E.

The original A, rather than E, supplies the auxiliary bound M<=C C_A^2 R^t by a maximal-net covering argument. It is valid for an arbitrary subset E. This justifies clipping the chosen s to [0,min(t,1)] with an explicit small exponent loss. The stopping upper profile continues to hold after this clipping with that loss included.

### Dynamic lower-population pruning

The threshold lambda(r/delta)^t is charged to each ORIGINAL occupied dyadic r-cell at most once. After the cell is deleted its residual population stays zero. Interspersing arbitrarily many tube extractions cannot create a second charge. With lambda inverse of order C_A^3 log(1/delta), the total discarded original-point count is at most a fixed small fraction of |A|.

This establishes lower populations only for occupied cells of the current pruned residual. It is not an assertion that unpadded original dyadic cells had lower population.

### Whole-cell extraction and epochs

Within an epoch, freeze its initial residual E0 and the chosen pair rho,tau,s. Extract every current point in each rho-cell hit by a maximizing tube, then remove them and rerun the globally charged pruning. Every extraction is nonempty, and all extracted fibers are disjoint original-point sets.

For a dyadic r>=rho, the exact identity

    D_r(F) = D_r(E intersect T)

holds: every extracted rho-cell has a witness in E intersect T, and its unique r-ancestor contains that witness. Therefore the SAME E0 tube upper profile controls every fiber in the epoch at every required coarser width.

When the selected profile falls by delta^kappa, end the epoch. For each scale pair its profile is monotone over the entire algorithm and can suffer only O(1+1/kappa) such drops before falling below one. There are O(log(1/delta)^2) pairs. Thus one epoch extracts at least |A| divided by a fixed-parameter polylogarithm. The final epoch ending with E empty adds only one to this bound.

This supplies one E0, disjoint fibers F_j in C rho-by-C tau tubes of directions theta_j, and a dense union. A point has exactly one assigned fiber and direction. Restriction to a finite slope chart is made by whole fibers, so point projection remains injective.

### The first simultaneous refinement

Include all the following in the ONE preparation refinement:

- required symmetric point-line relations;
- ordinary spatial-cell partitions on the fixed working radii;
- (fiber j, spatial r-cell) partitions on all required fiber radii;
- spatial r_i-cell and (spatial r_i-cell, angular Delta-cell) partitions for every intermediate i used below.

The fixed fiber upper-cover menus and the original spatial menus give the corresponding lower populations on the SAME final point set B. Since the point-line projection is bijective, these are actual original-point counts.

In particular, if Q is a parent cell at a prepared dyadic scale b and B intersect F_j intersect Q is nonempty, then

    |B intersect F_j intersect Q|_rho >= h_s (b/rho)^s.             (A)

This follows directly from the (j,Q) partition lower mass and the original rho-cell population upper bound. It does not restrict an abstract AD fiber to a ball and infer lower AD. The bound holds INSIDE Q. The reference fiber-r-cell maps must therefore include every candidate parent scale b, before the first refinement.

We can write all preparation losses as R^(O(epsilon)) after kappa=epsilon chi_profile, eta sufficiently smaller than epsilon chi_profile, and delta sufficiently small. Write h_s and h_t for the fiber and spatial lower factors, H for the inherited tube-profile constant, and K1 for the first degree-comparison factor. All h_s^(-1), h_t^(-1), H, K1 and the needed powers of C_A have the stated small-loss bound after conversion.

## 3. Exact direction-menu stabilization

Write R=tau/rho=2^M. Choose fixed m large compared with d/zeta and let

    r_i = rho 2^(floor(i M/m)),  0<=i<=m.

For M>=2m these are nested dyadic scales. For a=r_i and b=r_(i+1), N=b/a is within a factor two of R^(1/m). Use ONE dyadic angular grid with cell width Delta comparable to R^(-1/m), so Delta<=C a/b for every i.

For every occupied spatial cell q define M(q) to be the angular cells containing the ACTUAL assigned directions of B-points in q. The directions are the original theta_j; they are constant on every B intersect F_j. Define D_i as the largest menu cardinality at level i.

The two prepared partitions at level i give global comparison of spatial-cell point populations and of occupied joint spatial-angular populations. Dividing shows that every occupied cell's menu has at least D_i/K1^2 elements. Nestedness gives D_i<=D_(i+1) EXACTLY. There are at most C Delta^(-(d-1)) angular cells. Hence some i<m has

    D_(i+1) <= B_ang D_i,
    B_ang <= C Delta^(-(d-1)/m) <= C N^((d-1)/m).

Fix that i for every parent patch. Inside each occupied parent b-cell Q, assign each a-child its entire original B-point count. Every child menu is at least a 1/(K1^2 B_ang) fraction of the parent menu. Weighted double counting chooses one angular cell occurring in children carrying at least

    gamma |B intersect Q|,  gamma >= c K1^(-2) N^(-(d-1)/m).

Retain ALL B-points in those selected children. Their directions need not all lie in the chosen angular cell. For each selected child q, record an ACTUAL witness p_q in B intersect q whose assigned theta_j belongs to that angular cell. Choose alpha_Q as an actual witness slope from that cell. Then |theta_j-alpha_Q|<=C a/b for each recorded witness. A coarse angular-cell center is never used as a substitute for the witness.

## 4. The genuine parallel-column count

Use graph coordinates for alpha_Q and quantize at a fixed fraction of a, as specified in section 6. Let Y_Q^ref be the normal-column labels occupied by the points in selected children, before the second refinement.

For each occupied normal column choose one original selected point and the child q containing it. The recorded p_q is O(a) away. Let j be the witness's original fiber. By (A),

    S = B intersect F_j intersect Q

has at least h_s (b/rho)^s occupied rho-cells. The source tube profile bounds the number of rho-cells of S in ANY ambient a-cell by C H (a/rho)^s, because that intersection lies in a bounded number of rho-by-a tube segments. Consequently S meets at least

    c h_s H^(-1) N^s                                           (B)

DISTINCT ambient a-cells.

All these cells lie in a fixed enlargement of the chosen parallel column. Indeed, S is in its original C rho-tube, rho<=a, and its direction differs from alpha_Q by at most C a/b; over a parent of diameter C_d b this produces at most C_d a transverse displacement. The original selected point and p_q contribute another O(a) displacement.

The enlarged parallel columns have bounded overlap. An ambient a-cell can meet only a dimensional number of them (also allowing the fixed finer quantization). The original AD set supplies

    #D_a(A intersect Q) <= C C_A^2 N^t.

Summing (B) over columns therefore gives

    #Y_Q^ref <= B1 N^(t-s),  B1 = C C_A^2 H/h_s.                (C)

This is the actual reference-column bound required by the fractional-fiber theorem. The spines lie INSIDE Q, and each is tied to an actual original fiber witness. They need not survive the second refinement: after (C) has been proved, they serve only as reference witnesses for a menu bound.

## 5. Constructing all final product counts on one set

Fix one parent Q. Let Omega_Q be its retained ORIGINAL point labels after selected-child and residue-color choices. Their quantized image is P_Q. Let U_Q bound the number of original labels at one image vertex. Original AD gives

    U_Q <= C C_A (a/delta)^t.

The first refinement's parent-cell bound and the direction selection give

    W_Q >= alpha U_Q N^t,  alpha >= c gamma h_t/C_A.             (D)

Fixed quantization/color factors are included in c.

For each prepared radius aR, 1<=R<=N, the directly counted reference bounds are:

- spatial-cell menu <= B0 (N/R)^t, B0<=C C_A^2;
- normal-column menu <= B1 N^(t-s), from (C);
- bins of x/R in any one column <= B2 (N/R)^s, B2<=C H;
- distinct vertices per spatial R-cell <= B3 R^t, B3<=C C_A^2;
- distinct vertices in one column's length-R interval <= B4 R^s, B4<=C H;
- occupied spatial R-cells in a FULL R-wide, N-long strip <= B5 (N/R)^s, B5<=C H.

The last bound is the source tube estimate at width aR and length b, applied to the SAME epoch E0. It is a common longitudinal cover for all quotient labels in the strip. It is not inferred from individual fiber dimensions.

Apply one new weighted self-uniform refinement to the actual maps

    spatial_R,
    (normal column, longitudinal R-bin),
    normal column.

Write theta2 for retention and K2 for comparison. This constructs a final original-label set Omega'_Q. Divide lower class masses by U_Q only at the step converting to distinct vertices. The explicit fractional-count proof gives:

    fiber lower:  theta2 alpha/(K2 B1 B2) * R^s;
    fiber upper:  C B4 R^s;
    quotient lower: theta2 alpha/(C K2 B0 B4) * R^(t-s);
    quotient upper: C K2 B1 B3 B5/(theta2 alpha) * R^(t-s).

The quotient upper proof sums WHOLE final fibers over a quotient ball and bounds their union using the FULL reference strip cover and reference spatial-cell capacity. The quotient lower proof counts the final ambient ball and divides by the inherited local fiber upper bound. No lower density of an arbitrary restriction is used.

For example, a sufficient combined constant is

    C_align <= C theta2^(-1) K2 gamma^(-1)
                   C_A^5 H^2 h_s^(-1) h_t^(-1),                (E)

up to fixed chart, endpoint and interpolation constants. The source tube Katz–Tao bound remains valid for the final quantized set. Earlier fiber regularity may be destroyed by this second refinement; it is no longer needed. Final product regularity is newly proved on this SAME second output.

This use of two refinements is therefore noncircular: the first constructs permanent witnesses for (C) and (D); the second constructs the final product. We never claim the first lower bounds survive unchanged.

## 6. Separation, movement, and literal near alignment

A naive shear-floor grid of step a has movement C_d a, whereas the definition asks for movement at most the output mesh and a mesh-separated approximating set. Handle both explicitly.

Choose a fixed large power of two c=c(d), let mu=a/c, and quantize each actual selected point p=(x,y) by

    x_q = mu * nearest_integer(x/mu),
    y_q = mu * nearest_integer((y-alpha_Q x_q)/mu).

The geometric image is (x_q, y_q+alpha_Q x_q). With c sufficiently large its Euclidean distance from p is at most a/10. Attach all original preimages to the quantized vertex.

Partition the integer coordinates (x_q/mu,y_q/mu) by residues modulo c, and retain one maximum-weight residue class. This costs at most c^d original weight. In that class, two distinct geometric images have Euclidean distance at least a: either their x coordinates differ by at least a, or their x coordinates agree and one y coordinate differs by at least a. The normal coordinates and each longitudinal fiber are also a-separated.

All reference-cover estimates above remain valid with fixed c-dependent constants. In the endpoint a=rho, mu<rho causes no problem: one original rho-cell contains at most C_d c^d quantized vertices, and the source profile is used at width rho. No upper profile at the unavailable width mu is assumed.

Perform this residue selection BEFORE the second refinement. The final image therefore remains a-separated, and every final original point is within a/10 of its image. Conversely each image has a retained original preimage. Thus the Hausdorff error is at most a/10 in original coordinates.

## 7. Literal local-ball patching

At this point each parent b-cell Q has an actual retained patch A'_Q and an a-separated approximately matching aligned image. Slopes alpha_Q may differ between patches.

Color the original b-cells by their integer cell indices modulo L_patch in every coordinate. After all patch constructions, keep one color carrying the largest total retained ORIGINAL point mass. This costs at most L_patch^d and deletes whole patches, so it preserves every within-patch conclusion.

Set

    rho_out = a,
    tau_out = C_ball b,
    delta_out = rho_out/tau_out = 1/(C_ball N).

By the preparation change, tau_out<=1. Also rho_out>=delta and rho_out<=tau_out. Each patch has diameter at most sqrt(d)b. Distinct retained parent cells are separated by at least (L_patch-1)b, which is strictly greater than tau_out. Therefore for EVERY retained original point a0 in patch Q,

    A' intersect B(a0,tau_out) = A'_Q.                          (F)

The whole patch lies in the ball and every other patch lies outside it. This is the exact local-ball identity missing from an arbitrary union-of-patches argument. It uses neither lower-AD inheritance under ball cuts nor any alignment of neighboring patch slopes.

Translate by -a0 and dilate by tau_out^(-1), with the fixed coordinate chart if needed. The approximate image is delta_out-separated and has Hausdorff distance at most delta_out/10 from the transformed original set. Its longitudinal and transverse coordinates are bounded by one, after the fixed C_ball normalization. Its fiber and quotient AD estimates extend from the prepared maximum scale b to tau_out by nonemptiness/total population and fixed constants. The tube Katz–Tao estimates extend across the same fixed top-scale interval using bounded coverings.

Thus (F) supplies the literal for-every-a conclusion of the nearly aligned local statement, with only a fixed dimensional loss. Four thousand numerical containment/exclusion tests checked this patch geometry in dimensions 1–4; the proof is the explicit diameter and spacing inequalities above.

## 8. Exponents, retention, and order of choices

Choose the output zeta first. Then choose m so (d-1)/m is much smaller than zeta. Choose epsilon much smaller than zeta/m; define chi_profile from the cover-profile stopping bound, and take kappa=epsilon chi_profile. Choose incoming eta and the first refinement/interpolation losses so their conversion to powers of R is O(epsilon).

The direction loss is at most

    gamma^(-1) <= C K1^2 N^((d-1)/m).

Since R is comparable to N^m, every R^(O(epsilon)) preparation loss is N^(O(m epsilon)). Formula (E), and the analogous original-mass retention product, are therefore bounded by powers

    N^((d-1)/m + O(m epsilon))

apart from the freely chosen second uniformity factor and fixed-parameter retention constants. Choose those with a small remaining budget, and finally choose delta sufficiently small. Both C_align<=delta_out^(-zeta) and original retention >=delta_out^zeta then follow after leaving a strict exponent margin.

All refinements use fixed-depth power-spaced radii, with the candidate r_i and b inserted explicitly. The number of relations is fixed before delta. The current self-uniform retention is a fixed positive parameter-dependent constant when Q is a suitable small power of the mesh; it can therefore be absorbed after choosing delta. There is no unjustified application of the coarse retention formula to every dyadic scale simultaneously.

Dyadic rounding and fixed top-scale constants give a safe final separation

    tau_out/rho_out >= delta^(-chi_safe),
    chi_safe = chi_profile/(2m)>0.

This weaker explicit function suffices for the quantified final theorem. It does not assert the stronger printed formula for chi(zeta).

The source exponent s starts nonnegative and can be clipped down to min(t,1) with the already accounted finite-scale loss. This makes gamma=1-s a genuine number in [0,1] for the later dimension-raising step. Any further ambient-dimension restriction on t-s must be justified from packing or retained with its finite-scale slack; no exact inequality is inferred merely by ignoring an AD constant.

## 9. Current mathematical and formal boundary

At the handwritten level, the disjoint-fiber epoch construction plus sections 3–8 provides a complete finite replacement for the problematic preparation, transverse AD step, and local patching in Lemma 5.3. All selected objects are original points, actual directions, actual cells, or explicitly quantized images with recorded inverse-image labels. No alignment conclusion is supplied as an input.

The central geometric statements still needing actual Lean callers are:

1. the greedy epoch construction and globally charged pruning, with the exact ancestor identity;
2. the anchored-fiber-to-parallel-column bound (B)–(C), using actual direction witnesses and bounded overlap;
3. the shear quantization/residue selection and isolated-parent patch identity (F).

The finite fractional-fiber counting constructor is being formalized separately. The small-s lattice constructor already passed its strict check. Neither fact by itself compiles the entire alignment theorem.

This is a repair of the universal auxiliary WZ argument. It does not preserve the original manuscript's old occurrence graph and is not an original heavy-root charge. The original compact theorem still requires the subsequent Proposition 18.1 dimension-raising, slab-Frostman and slope-consistency constructions and the later contradiction argument; none is silently supplied by this alignment result.

## 10. Minimal real/grid interface for the column-overlap caller

Let normal labels be z in a finite subset of Z^n. Ambient source cells are

    c_a(p)=(floor(t(p)/a), floor(x_1(p)/a),...,floor(x_n(p)/a)),

with a>0; the normal-label mesh is h>0 (in the quantized caller h=a/c). Fix alpha with |alpha_i|<=A0. For each z take an ACTUAL anchor p_z, an actual direction beta_z, and a finite original spine S_z. It suffices to prove the following scalar data from the source construction:

    |t(p)-t(p_z)| <= b,
    |x_i(p)-x_i(p_z)-beta_z,i(t(p)-t(p_z))| <= C0 a,
    |beta_z,i-alpha_i| <= D0 a/b,
    |x_i(p_z)-alpha_i t(p_z)-h z_i| <= E0 a.

The third bound comes from the selected angular cell. The fourth comes from the actual same-child witness and the explicit quantization movement. The first two are actual source tube and parent bounds.

Triangle inequalities give, for p in S_z,

    |x_i(p)-alpha_i t(p)-h z_i| <= (C0+D0+E0)a.

If S_z and S_z' meet the same ambient a-cell, use their TWO actual point witnesses in that cell. Their alpha-normal coordinates differ by less than (1+A0)a. Therefore

    |z_i-z'_i| <= [2(C0+D0+E0)+1+A0] a/h.

Choose an integer M above this value. For any nonempty source-cell incidence fiber, choose one actual label z0 in it; every other label belongs to the integer box z0+[-M,M]^n. Hence that source cell meets at most (2M+1)^n labels. This derives overlap from real geometry; no overlap bound is an input.

Double-count the actual relation `(z,c)` with c in `S_z.image c_a`. If each image has at least L distinct cells and all images lie in a reference cell image C_ref, then

    L * #Z <= (2M+1)^n * #C_ref.

The rich lower bound L itself comes from total fine-cell richness divided by the original fine-cell count inside one coarse cell. It must not be replaced by raw original incidence weight without that denominator.

## 11. Original shading weights in the later caller

The AD-set lemma retains geometric original Y_z points. It does not automatically preserve an arbitrary unrelated weight attached to those points. In the actual Proposition 18.1 shading caller, prepare the `(height z, quotient point y)` partition in the preceding SAME-SET uniform construction. Its occupied classes then have comparable ORIGINAL incidence masses. A geometric point retention fraction r transfers to an original-incidence retention fraction at least r/K. Keep all original incidence labels over each selected point, before the next declared refinement.

The point-to-quantized-vertex maps in this note retain original labels and have explicit inverse-image caps. They do not silently equate distinct geometric point counts with incidence weights. The bounded-auxiliary universal theorem and the original compact-front conclusion keep their existing quantifier distinction.

## Later formalization checkpoint

The epoch constructor, floor-threshold accounting, literal grid-ancestor identity,
fractional-column endpoint, physical-spine overlap bound, and sup-metric
periodic patch/quantization constructions now have strict standard-only Lean
checks. The complete AD-set-to-alignment caller, its scale-profile stopping
and remaining Euclidean interfaces are not yet assembled. See
[the precise formal scope](WZ_ALIGNMENT_CONSTRUCTORS.md).
