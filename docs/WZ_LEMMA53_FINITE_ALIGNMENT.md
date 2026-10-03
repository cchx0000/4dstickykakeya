# Lemma 5.3: a finite alignment construction and the remaining positive-fiber branch

Handwritten mathematical audit, 2026-10-03. Source: the supplied Wang–Zakharov arXiv:2609.22035 PDF, printed pp. 21–25 and 74–76. This is a mathematical derivation; its combined geometric callers are not all formalized. This note gives mathematical proofs and finite interfaces; it does not claim a new Lean theorem has compiled.

A subsequent [complete handwritten adapter](WZ_LEMMA53_COMPLETE_PATCH_ADAPTER.md)
repairs the point-retention, anchored-fiber, fractional-product and local
patching steps identified below. Its combined Lean caller remains unfinished. The discussion below records the precise
issue and the independent finite column construction, not a completed
implementation of the entire alignment lemma.

## 1. Exact source task

Lemma 5.3, pp. 23–25, starts with a delta-separated (delta,t,delta^(-eta))-AD set A in a bounded d-dimensional box. For a prescribed zeta, it claims a retained subset of relative size at least (rho/tau)^zeta and scales rho<tau with a fixed power separation. After local rescaling, the result is nearly aligned: one-dimensional s-AD fibers, a (t-s)-AD quotient, and a tube Katz–Tao bound of exponent s. The actual invocation on p. 74 is on Y_z in dimension d-ell. For the four-dimensional ell=2 branch this is a TWO-dimensional AD set. The ell=3 branch skips this lemma.

The source proof uses, in order:

1. Lemma 5.2: a rich-tube scale pair and the ALL-WIDTH, ALL-LENGTH tube covering bound (iii).
2. A finite family of rich tubes and its point–line incidence configuration X, followed by a uniform refinement X'.
3. Extraction of regular tube spines, equations (31)–(34).
4. Direction-menu stabilization across m intermediate spatial scales.
5. Parallel-column selection and regularization of their longitudinal and transverse populations.

The finite result below closes step 5, and closes the ENTIRE small-s branch directly after step 1, without passing through X. The remaining positive-s preparation is identified in sections 7–8. There is no assumed aligned-set certificate in either finite result.

## 2. The indispensable tube profile

Put N=tau/rho and rescale a tau-sized patch so rho is one lattice unit. Write a point as (x,y), with x in Z and y in Z^n, n=d-1. The inherited source estimate is a bound for the FULL reference set in every tube, including

    number of occupied R-cells in an R-wide, N-long strip <= H (N/R)^s,  1<=R<=N.

This is Lemma 5.2(iii) with width R*rho and length tau. It is a common longitudinal-cover bound across ALL quotient labels in that strip. Individual s-AD fibers do not imply it.

The same source estimate at width rho and length R*rho gives at most C H R^s coarse vertices in a narrow column segment of length R. At width R*rho and length tau it bounds the number of longitudinal R-bins in ANY one narrow column by C H (N/R)^s.

Fixed enlargements and quantization change H by a dimensional constant: for R<=N/C use the source estimate at width C R rho and cover back by R rho cells; for R>N/C use the bounded number of cells in the patch. A bounded graph shear has the same effect. All endpoint cases are included; a source estimate only at width rho is insufficient.

## 3. Closed finite fractional-column construction

Let Omega be a finite set of ORIGINAL labels with positive natural weights w. Let v:Omega -> Z x Z^n be an actual quantization map, P=v(Omega), and write v(a)=(x(a),y(a)). No label is replaced by a newly weighted geometric point. Let W be total weight, and assume each geometric vertex has original inverse-image weight at most U.

Fix a finite list of integer working radii R between 1 and N. Use the literal floor maps

    spatial_R(a) = floor(v(a)/R), coordinatewise;
    column(a) = y(a);
    columnTime_R(a) = (y(a), floor(x(a)/R)).

Assume the following DIRECTLY COUNTED reference bounds, with 0<=s<=t:

(a) W >= alpha U N^t.
(b) #spatial_R(Omega) <= B0 (N/R)^t.
(c) #column(Omega) <= B1 N^(t-s).
(d) For each original column, its number of occupied x/R bins is <= B2 (N/R)^s.
(e) Each spatial R-cell contains at most B3 R^t DISTINCT vertices of P.
(f) Each column segment {|x-x0|<=R,y=y0} contains at most B4 R^s DISTINCT vertices of P.
(g) The number of spatial R-cells meeting P in {|y-y0|_infinity<=R} is <= B5 (N/R)^s.

Bounds (d), (f), and (g) come from the full tube profile in section 2. Bound (c) is the parallel-column count obtained from rich local spines, not a consequence of arbitrary ambient AD alone. Bounds (b),(e) come from the ORIGINAL metric AD set using maximal separated centers and bounded grid covering; no unpadded dyadic-cell lower population is asserted.

Apply the proved weighted self-uniform refinement ONCE to all equivalence relations defined by these maps. Let Omega' be its output, W'>=theta W, and K its degree-comparison factor (K=Q^2 in the current Lean theorem). Let P'=v(Omega') and Y'=projection_y(P'). The original labels and weights of Omega' are unchanged.

The existing partition-richness theorem gives, for every occupied final class with reference menu size M,

    final class weight >= W'/(K M).

Divide by U only when passing from original mass to distinct vertices. Then, at any p=(x,y) in P',

    #P' intersect B_infinity(p,R) >= theta alpha/(K B0) * R^t,
    #X_y intersect [x-R,x+R] >= theta alpha/(K B1 B2) * R^s,
    #X_y >= theta alpha/(K B1) * N^s.

The first inequality uses the spatial_R class; the second uses columnTime_R; the third uses column. A common floor cell has coordinate diameter strictly less than R, including negative coordinates, so it lies in the claimed centered ball/interval. Upper ambient and fiber counts are inherited from (e),(f), with only a fixed adjacent-cell factor where necessary.

For the quotient lower bound, the ambient centered R-ball contains at least theta alpha R^t/(K B0) vertices, while each y-fiber contributes at most B4 R^s. Therefore

    #Y' intersect B_infinity(y,R) >= theta alpha/(K B0 B4) * R^(t-s).

For the quotient upper bound, all FULL fibers over this quotient ball lie in the FULL reference strip. By (g) and (e), that strip contains at most

    B3 B5 (N/R)^s R^t = B3 B5 N^s R^(t-s)

vertices. Every occupied final fiber has at least theta alpha N^s/(K B1) vertices. Hence

    #Y' intersect B_infinity(y,R) <= K B1 B3 B5/(theta alpha) * R^(t-s).

This is the fractional-fiber quotient argument. It does NOT replace the integer dimension k by s in the earlier dense-lattice proof. Its common-cover input is (g), supplied by source Lemma 5.2(iii).

The nearly aligned geometric set is exactly

    {(rho x, rho y + a rho x) : (x,y) in P'},

after undoing the bounded shear and rescaling. Every vertex is accompanied by its actual original preimage labels. The source tube Katz–Tao upper bound is inherited by this set with a fixed enlargement loss. No further thinning occurs after this final refinement.

### What already exists in the repository

- `weighted_self_uniform_grain_refinement` constructs the one final set.
- `partition_richness_of_self_uniform` gives all three lower-mass estimates above.
- Existing carrier-pruning maximal-net and cover-assignment arguments give the ambient reference menu bounds after their actual cardinality estimates are supplied.
- The existing compatible-selector theorem supplies a common angular state from ORIGINAL conditional menus. Its `weighted_spatial_selection` also directly supplies the small-s heaviest-vertex step: take q=normal-column label, k=the full quantized vertex, and b=F, on the ORIGINAL labels with their ORIGINAL weights. No new maximum-selection theorem is needed.
- The missing new lattice step is the actual strip-cover/fiber division and its inverse-image accounting. An abstract assertion that a quotient is AD would add nothing.

## 4. A complete small-s alignment branch

This branch requires no point–line incidence uniformization and no initial parallel-column bound (c).

Start with a delta-separated (delta,t,K0)-AD reference set A. Let A1 be the retained subset from Lemma 5.2, with |A1|>=r|A|, and let rho,tau,s,H be its tube-profile parameters. The argument works for any actual A1 satisfying those conclusions; it does not assume alignment or regular tube spines.

Partition into tau-cells. The number of occupied cells of the original A is at most C K0^2 tau^(-t), by a maximal-net argument. Discard cells whose A1 population is below half the global average over that menu. This keeps at least half of A1. Every retained tau-cell Q has

    |A1 intersect Q| >= c r K0^(-3) (tau/delta)^t.

Quantize its actual points at mesh rho, with a fixed finer subdivision if needed to make the eventual movement at most the chosen output mesh. Use all original points in a coarse vertex as its inverse-image labels. The vertex weight cap is

    U <= C K0 (rho/delta)^t.

Consequently W_Q>=alpha0 U N^t with alpha0=c r K0^(-4), N=tau/rho. Fine points on grid boundaries cause at most a dimensional covering factor; no occupied-cell lower mass is used.

Fix ANY one coordinate axis as the fiber direction. By source Lemma 5.2(iii), every parallel rho-column in Q contains at most

    F <= C H N^s

DISTINCT coarse vertices. In each occupied column choose a vertex whose ORIGINAL inverse-image weight is maximal. Retain ALL original labels of that vertex. This is a deterministic finite maximization, with

    W_selected >= W_Q/F.

The resulting geometric image has exactly one vertex in every occupied column. Thus its x-fibers are literal singletons, with AD exponent zero and constant one. The original labels may still be numerous, and none of their weights has been changed.

Now apply one final weighted uniform refinement for the working spatial-cell maps (and any required predeclared additional relations). Write theta for its retention and K for its comparison factor. Single-point fibers persist under this restriction. The final point shadow has spatial lower counts

    #P' intersect B(p,R) >= theta alpha0/(K C K0^2 F) * R^t.

Project to the normal coordinates. Since each normal coordinate has one vertex, this is also a quotient lower bound. For the upper bound, use the full reference strip profile, not the geometry of the selected singleton graph:

    #Y' intersect B(y,R)
      <= C H (N/R)^s * K0^2 R^t
      <= C H K0^2 N^s R^t.

Therefore Y' is t-AD at the new mesh, and the final approximate set is aligned with s_output=0. One valid overall AD/KT constant is

    C_align <= C K K0^6 H N^s /(theta r),

with fixed dimensional factors absorbed in C. Its original-label retention, summed over all retained patches, is at least

    c theta r /(H N^s)

relative to the initial A. The tube Katz–Tao exponent-zero bound follows directly from H (length/width)^s <= H N^s at all output scales.

If s<=c zeta and H=N^(c zeta), and the converted original AD loss, final K, and theta^(-1) together use the remaining exponent budget, then C_align<=N^zeta and the retained original mass is >=N^(-zeta). This is a closed constructive case of the desired alignment mechanism. In the source notation, s<=sqrt(epsilon0) is harmless after budgeting O(sqrt(epsilon0)).

For d=2 the normal quotient is one-dimensional. If t exceeds one by a fixed amount, the resulting t-AD count would contradict one-dimensional grid packing as N grows; this gives the expected obstruction, rather than licensing an exact finite-scale claim t<=1 without slack.

This statement outputs explicit aligned PATCHES. It does not assert that arbitrary centered-ball restrictions of their union are still AD. That stronger quantifier needs the localization discussion in section 9.

## 5. Direction stabilization with original weighted cell labels

There is a useful exact finite replacement for the ratio paragraph on p. 24. Let spatial partitions at levels 0,...,m be nested from fine to coarse, and let Theta be a finite angular-cell set. For each spatial cell q define its ORIGINAL menu M(q) of actual witness directions. Let

    D_i = max over occupied level-i cells q of #M(q).

If these are menus of one fixed original witness configuration, D_i<=D_(i+1) exactly. If #Theta<=B^m, then some i<m has D_(i+1)<=B D_i; otherwise multiplying all m strict inequalities contradicts D_m<=#Theta and D_0>=1. The source needs D_m as well as D_0,...,D_(m-1).

Suppose each selected fine child q at that i has #M(q)>=D_i/L. Inside one parent Q, its menu has size <=B D_i, so every child has at least a 1/(LB) fraction of the parent menu. Assign each child the TOTAL ORIGINAL point weight it carries. Weighted double counting selects theta in M(Q) for which the children having theta in their menus carry at least 1/(LB) of the parent weight.

This is a direct one-stage application of the existing compatible-selector primitive. Keep whole child point fibers. A menu entry must have a genuine direction witness at an actual point in that child. Replacing it by an angular-cell center is unnecessary and can lose transversality elsewhere.

If each such witness has an actual rich rho_i-spine inside a bounded enlargement of its parent rho_(i+1) patch, all selected child cells fit into parallel C rho_i-columns of direction theta. Each column contains at least h (rho_(i+1)/rho_i)^s distinct reference coarse points; different enlarged columns have bounded overlap. The original local t-AD upper count then gives

    #parallel columns <= C K0^2 h^(-1) N^(t-s).

This proves input (c) of section 3 from actual local spines. The reference spines need not survive the final refinement. Their role is to bound the reference column menu before that refinement.

The exact unresolved preparation is the construction of these local spines with enough ORIGINAL point shadow; it is not the weighted angular double counting.

## 6. Quantifier and scale accounting

There is a mismatch between the printed chi(zeta) and the bound actually delivered by the displayed proof. The proof chooses m>10/zeta and epsilon0 small enough that C m epsilon0 <= c zeta, hence epsilon<=epsilon0 is of order at most zeta^2. Lemma 5.2 applied at epsilon only guarantees an exponent of order

    chi_2(epsilon) = c epsilon^(3 ceiling(1/epsilon)).

Passing to adjacent intermediate scales divides that exponent by m. This does not justify the stronger printed c zeta^(4 ceiling(1/zeta)) as zeta tends to zero. A safe replacement is the explicitly smaller positive function

    chi_safe(zeta) = chi_2(epsilon)/(2m),

where m=ceiling(C/zeta) and epsilon=c zeta/m with fixed sufficiently large/small dimensional constants. The factor two absorbs dyadic rounding.

A valid parameter order is:

1. Choose the requested output zeta and dimensions.
2. Choose the fixed direction depth m, the interpolation depth h>=C d/zeta, and epsilon. Define chi_safe.
3. Choose the incoming eta so all terms eta/chi_safe and C eta epsilon^(-3 ceiling(1/epsilon)) fit the output budget.
4. Choose the final uniformity exponent and all fixed padding constants.
5. Choose delta sufficiently small for constant losses, finite grid/color choices, and the resulting theta to fit their allocated powers.

For the finite partition theorem, use h+1 POWER-SPACED working radii, not all O(log N) dyadic radii with the naive retention formula. Between adjacent radii the ambient/grid packing gives an interpolation loss N^(C d/h). The number of relations is fixed before delta. Taking Q=N^u makes L bounded once the original weight bound W<=delta^(-C) and N>=delta^(-chi_safe) are known. Thus the theorem's retention 1/[2(4d_rel)^(d_rel L)] is a fixed positive constant, absorbed by making delta smaller. K=Q^2 uses a chosen small part of the output exponent.

For the positive-s output, exact inequalities s>=0, s<=1, and s<=t must be justified or replaced by clipping with finite-scale slack. The covering and nonemptiness bounds yield errors O(log(constants)/log N); they do not prove exact exponent inequalities at a fixed mesh. Clipping changes all relevant powers by at most those recorded losses.

The weaker chi_safe still suffices for the universal auxiliary extremizer argument: every later scale remains a fixed positive power of the initial mesh, and the original compact packet is chosen only after all these constants. It does not constitute an old-source hereditary root charge.

## 7. The positive-s point-shadow issue

On p. 23 the paper forms X from rich tube memberships and retains X' with |X'|>=K^(-1)|X|. On p. 24 it uses the assertion that the point shadow P[X'] is sufficiently dense in the original t-AD set to obtain the local t-dimensional box count. Pair-mass retention alone does not imply this. In an abstract bipartite graph, many leaves can be attached to tubes sharing one rich core; keeping the core incidences keeps most pairs and very few original points.

This is an issue requiring a geometric argument, not a claim that the geometric theorem is false. The source tube profile gives additional information absent in that graph. Likewise (33), a global tube covering count, and a local upper bound do not alone imply the pointwise lower bound (34). The simultaneous partition construction in section 3 fixes this AFTER the needed actual reference menus and original-mass bound have been established.

Weighted point-line refinement with inverse point degrees preserves a shadow budget, but the needed tube-fiber lower concentration then changes. It cannot be cited as a completed repair without checking those new denominators.

## 8. Verified overlap estimate; limit of the proposed dichotomy

Let two graph tubes have radius rho, length tau, slopes a,b with theta=|a-b|_infinity>0. For a point (x,t) in their intersection,

    |(a_j-b_j)t + (intercept_a_j-intercept_b_j)| <= 2rho

in a coordinate j attaining theta. Thus their common t-coordinates lie in an interval of length at most 4rho/theta. The intersection lies in one tube truncated to that length. If theta is below C rho/tau the claimed angular concentration is already true. Otherwise the inherited tube profile gives

    |A intersect T intersect T'|_rho <= C H theta^(-s).

If each tube has at least H^(-1) N^s coarse points and the overlap has at least a beta fraction of one such heavy mass, then, for s>0,

    theta <= C N^(-1) (H^2/beta)^(1/s).

Consequently, for s>=sqrt(epsilon0), H=N^(O(epsilon0)), and beta=N^(-O(epsilon0)), the directions are within N^(-1+O(sqrt(epsilon0))). Thickening to that angular scale preserves a power-separated output mesh with only O(sqrt(epsilon0)) loss. This is a real potential alignment branch.

However, failure of original point-shadow retention has not yet been proved to produce such a SUBPOWER beta. Raw second-moment counting only yields beta on the order of heavy-fiber-size/shadow-size, which can be a fixed negative power of N. The factor beta^(-1/s) can then consume the whole angular scale. Therefore pairwise overlap alone does not close the positive-s branch. An additional multiscale incidence argument, or a different construction preserving the point marginal, is still needed.

## 9. Localization and the actual Proposition 18.1 caller

The source concludes that for EVERY retained a, the restriction A' intersect B(a,tau) is nearly aligned. An arbitrary ball restriction of an AD set need not preserve lower AD at all its new boundary points. Similarly, a union of patches with different selected directions does not automatically have one direction on every ball crossing patch boundaries.

The finite construction here uses actual cells, original inverse-image labels, and bounded enlargements. It proves alignment of each prepared local patch. To use it in Proposition 18.1, the chosen packet restriction must be included before the final uniform refinement, or one must give a padded separated-patch construction with its complete restriction and retention accounting. A later arbitrary restriction to a selected tube cannot simply inherit all lower AD bounds.

For several Y_z, the common rho,tau and exponent-bin selections cost finitely many scale menus and polylogarithmic factors, provided these choices are made before the final refinement. All original incidence weights associated with each selected y must be carried through the fiber map. Geometric cardinalities and those incidence masses are different quantities; U is the explicit conversion denominator.

## 10. Verification and next formal target

- 500 randomized exact-rational finite-grid checks verified the lower spatial/fiber inequalities and the quotient strip-division inequality, including negative coordinates and unequal original vertex weights.
- 400 exact weighted tests verified the heaviest-vertex-per-column retention and injectivity of the selected column map.
- These are sanity checks, not kernel proofs.

A useful smallest Lean target is the SMALL-s lattice geometry caller: given an actual finite weighted label-to-grid map, an actual per-column vertex bound F, spatial reference-menu bounds, and actual strip-cover bounds, invoke the ALREADY PROVED `weighted_spatial_selection` with q=column and k=vertex, apply the existing final partition refinement, and prove the distinct quotient AD bounds using the actual floor cells and strip covers. Do not re-prove a new abstract maximum-selection wrapper. The genuinely new proof is the geometric image count and the original inverse-image denominator. This constructs the set and proves its geometry; it does not assume an alignment output.

The next genuinely unresolved source obligation is positive-s local rich-spine preparation with quantitative original point-shadow retention. The verified two-tube intersection estimate supplies a geometric ingredient, but not the whole dichotomy. Slab-Frostman stopping and the later slope arguments are not used to fill this gap.
