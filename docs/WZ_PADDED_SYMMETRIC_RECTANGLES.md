# Padded dyadic rectangles from symmetric weighted refinement

2026-10-03. Mathematical research note. Primary source: Wang–Zakharov, arXiv:2609.22035, Definition 3.6 and Proposition 3.1, pp. 16–17; Section 4 and Lemma 4.2, pp. 19–20. The proof below supplies geometric adapters and a finite padding construction, not the final WZ estimate.

## 1. Verified symmetric weighted refinement

Let A be finite, w:A→positive integers, W=sum_A w, and let s>=1 relations R_i be symmetric and reflexive. Put d_i^B(x)=sum_{y in B,R_i(x,y)}w(y), and M_i=max_{x in B}d_i^B(x). Fix integer Q>=4 and suppose W<=Q^L.

The proposed peeling argument is valid:

1. In the current B, fix thresholds m_i=M_i/(4Q). Sequentially remove any vertex whose remaining i-degree is <m_i, recording one offending color i.
2. If the surviving core has at least half the current weight, every surviving i-degree is >=m_i and every maximum remains <=M_i. Thus all degrees on that SAME surviving set are comparable by 4Q<=Q².
3. Otherwise the removed vertices have at least half the current weight. One color class C carries at least W_B/(2s). In deletion order, every vertex of C has forward C-degree <m_i.
4. Symmetry bounds its weighted degree energy by

       sum_{x in C} w(x)d_i^C(x) <= 2 m_i sum_{x in C} w(x).

   Each unordered off-diagonal edge is counted twice; the diagonal is counted only once. Thus retaining vertices of C with d_i^C(x)<=4m_i preserves at least half C's weight. Their induced maximum is <=4m_i=M_i/Q. Other maxima cannot increase.
5. Reflexivity and positive integer weights give M_i>=1 on every nonempty set. Therefore sum_i floor(log_Q M_i) is a nonnegative integer, initially <=sL, and decreases on every failed peel. There are at most sL failures.

The final set has weight at least W/[2(4s)^(sL)] and Q² self-uniformity. No C/B substitution is used. The separate strict Lean proof is `Thm_StickyKakeya4_self_uniform_incidence_refinement.lean`; this section records the corresponding mathematical construction.

## 2. The actual WZ padded setup

Write H=2^S. Proposition 3.1 assumes a family of dyadic delta-tubes with bounded phase parameters, S>=2, delta in 2^(S Z), and S>=C_d log log(1/delta). It constructs a common physical translation z and H delta-tubes T' such that at least half of the ORIGINAL delta-tubes translate into T', and

    N_rho(T) subset T^(H rho)

for every rho in [H delta,H^-1] intersect 2^Z and every T in the rho-thickening of T'. Here N is the physical Euclidean neighborhood and the superscript is the dyadic ancestor.

The primary text explicitly flags the dyadic-boundary problem immediately before this proposition (local text lines 813–840). Section 8 applies this padding before uniformization and invokes it to relate Euclidean and dyadic counts (lines 1537–1541, 1562–1564). Section 18 uses the same point-line setup and count identities. The unexpanded notation warning in section 8 below is not a criticism of this padded construction.

For the rectangle adapter at horizontal scale h, apply the displayed padding with rho=h/H. Its stated range is available when

    H² delta <= h <= 1.

This endpoint must be recorded. One may use a new finest mesh delta_bar=H² delta, track the intervening thickening/coarsening losses, and then use all horizontal scales >=delta_bar. Since H is a power of log(1/delta), these are subpower changes. Alternatively the direct central-line padding in section 7 below covers the finest scale without this coarsening; it is a weaker specialization of the same random-translation mechanism.

## 3. Symmetric neighborhoods inside the LITERAL dyadic rectangle

Let omega=(x,t,theta), with x,theta in R^(d-1), and let

    ell_omega(s)=(x+(s-t)theta,s),
    b_omega=x-t theta.

For scales v,h,alpha satisfying v alpha<=h, WZ's literal rectangle consists of omega' with:

* t' in the same dyadic v-cell as t;
* theta' in the same dyadic alpha-cube as theta;
* (x',t') in the dyadic h-tube T^h(omega) determined by (theta,b_omega).

Define the midpoint residual

    r_mid(omega',omega)=x'-x-(t'-t)(theta'+theta)/2.

It changes sign when the two arguments are exchanged. Set epsilon=1/(8dH). Define S_(v,h,alpha)(omega',omega) by the first TWO exact dyadic-cell equalities above, together with

    |t'-t| <= epsilon v,
    ||r_mid(omega',omega)||_infinity <= epsilon h.

This is exactly symmetric and reflexive. It does NOT claim that the original one-sided dyadic relation is symmetric.

Assume the central line ell_omega lies in the padded (h/H)-tube whose h-ancestor is T^h(omega). Same angle cell gives ||theta'-theta||_infinity<=alpha. The one-sided residual is

    r_one=x'-x-(t'-t)theta
         =r_mid+(t'-t)(theta'-theta)/2.

Hence ||r_one||_infinity<=3 epsilon h/2. Its Euclidean norm is at most 3 sqrt(d-1) epsilon h/2 < h/H. At the same time t', the point (x',t') is therefore in N_(h/H)(ell_omega), and Proposition 3.1 gives

    S_(v,h,alpha)(omega) subset R_(v,h,alpha)(omega).                 (A)

Time/angle grid boundaries cause no problem because exact equality of their cells is built into S. No extra time translation, angular shear, shifted grid, or time/angle padding is necessary.

## 4. Covering one rectangle by polynomially many symmetric neighborhoods

Suppose |t|<=T_* throughout the fixed chart. For any omega' in R_(v,h,alpha)(omega_0), the definition of a dyadic graph tube gives

    ||x'-x_0-(t'-t_0)theta_0||_infinity <= (1+T_*)h.                (B)

Indeed, a point of the h-tube uses some slope/intercept within h of theta_0,b_0.

Use coordinates t' and e'=x'-x_0-(t'-t_0)theta_0. Partition the common time cell into intervals of length at most epsilon v/4, and the transverse e-box in (B) into boxes of side at most epsilon h/4. There are at most

    C_(d,T_*) epsilon^-d <= C'_(d,T_*) H^d

product boxes. For each box that contains a retained occurrence, choose one such occurrence as center.

Two occurrences in the same box have the same original time cell and angle cell. Their time difference is <=epsilon v/4. Since both angles lie in omega_0's alpha-cell, their midpoint residual differs from their e-coordinate difference by at most epsilon v alpha/4<=epsilon h/4. Consequently their midpoint residual is <=epsilon h/2, so they belong to the same S-neighborhood. This proves the required cover with centers in the ACTUAL retained set. No angular subdivision is needed.

The number of neighborhoods is O_d(1) for a fixed geometric enlargement. Here the neighborhoods are shrunk by H, so the precise loss is O_d(H^d), not O_d(1). It is subpower for the source's chosen H.

## 5. Recovering literal WZ uniformity

Apply the symmetric weighted theorem simultaneously to S_i for the s<=m³ admissible triples of the chosen m scales. Let Y be its self-uniform output and K_sym its comparison factor. For a triple i put

    M_S=max_{y in Y} w(Y intersect S_i(y)),
    M_R=sup_{all allowed centers z} w(Y intersect R_i(z)).

Section 4 gives M_R<=C_d H^d M_S. Inclusion (A) gives, for every y in Y,

    w(Y intersect R_i(y))
      >=w(Y intersect S_i(y))
      >=M_S/K_sym
      >=M_R/(C_d H^d K_sym).

Thus Y is genuinely self-uniform for the LITERAL dyadic rectangles, with factor K=C_d H^d K_sym. Both sides count the same Y and the same original weight. This is the desired adapter for WZ's concentration-number estimates.

If original occurrences have extra endpoints or marks, take R_i and S_i to depend only on their geometric projection. Padding and refinement retain actual occurrences with their unchanged weights; every other coordinate remains a label. Coincident projected points are allowed in this weighted formulation. Converting that weighted statement to unweighted distinct-tube counts is a separate, explicit step when needed.

## 6. A fully finite padding proof: smallest new formalization target

The relevant part of Proposition 3.1 can be constructed without continuous random shifts or integration.

Let delta=2^-n and N=2^n. A dyadic delta phase-tube has integer slope/intercept indices. Choose a common horizontal translation

    z(q)=(delta q_1,...,delta q_(d-1),0),
    q in {0,...,N-1}^(d-1).

The translated original phase cubes remain dyadic delta-cubes exactly. Slopes, times and the midpoint residual are unchanged. For rho=R delta and h=H rho<=1, with R and H powers of two, the intercept rho-child index inside the h-parent is

    floor((b_index+q_j)/R) mod H.

As q_j runs through 0,...,N-1, each of the H child indices occurs exactly N/H times. This is because HR divides N and each of its residue classes has N/(HR) representatives; a child index groups R such residues.

Require, in every intercept coordinate, that the rho-child index lie in {4,...,H-5}. At most 8/H of the shifts fail a coordinate at one scale. The whole rho-intercept cell is then at least 4rho from its h-parent boundary. For graph slopes bounded by two, moving a physical tube point by Euclidean distance <=rho changes the required intercept by at most 3rho coordinatewise (spatial error plus slope times time error). The slope parameter stays in its original rho-cell and hence in its h-parent. Thus

    N_rho(T^rho) subset T^h.

There are at most n relevant rho-scales. The finite union bound gives, for each ORIGINAL tube, a good-shift fraction at least 1-8(d-1)n/H. If H>=16(d-1)n, this is at least 1/2.

For arbitrary nonnegative original tube weights w_T, double counting gives

    average_q sum_(T good for q) w_T >= (1/2) sum_T w_T.

Choose a maximizing q and retain its good original tubes. Taking their H delta-ancestors gives T' with exactly the retention and padding required above. Multiple original tubes can have the same ancestor; keep the original indices/weights during the retention accounting. The conclusion is a bound on retained ORIGINAL tube weight, not a false claim that coarsening preserves the number of distinct tubes.

For incidence weights, first sum all original incidence weights assigned to each original phase tube, apply this finite argument, then retain all incidences on the good tubes. This preserves at least half the original total incidence weight with every mark unchanged.

The separately formalized finite padding module includes the needed cyclic-fiber count:

    If HR divides N, for any integer b and child j in Fin H,
    #{q in Fin N : floor((b+q)/R) mod H=j}=N/H.

Its finite weighted averaging corollary is immediate by commuting finite sums and selecting a maximum. No final padding hypothesis needs to be assumed: the residue lemma and elementary tube-containment calculation construct it.

The stronger all-scale construction uses H comparable to n=log_2(1/delta), so S=log_2 H=O_d(log log(1/delta)), matching the source. It does not actually require n divisible by S; imposing the paper's extra dyadic-stride hypothesis is harmless.

Input bookkeeping: if a point-line pair is represented by a cube point p in a tube rather than a point on that tube's central line, assign it the actual phase tube T^delta(omega) determined by theta and x-t theta. These differ from the original phase tube by only boundedly many neighboring intercept cells in a bounded chart. Alternatively choose actual points on the original lines initially. One must record this fixed-factor assignment, rather than silently equating the two central lines.

## 7. Finite-scale central-line padding and full Galilean padding alternatives

For only m prescribed horizontal scales, central-line padding is enough for (A). A horizontal shift B uniform in a unit cube sends b to b+B. At any dyadic scale h<=1, the probability of lying within h/H of an intercept boundary is at most 2/H per coordinate. Choosing H>=4(d-1)m retains at least half the original occurrence weight padded at all m scales. The same symmetric cell-equality adapter then applies even at the finest horizontal scale. This is the finite-incidence specialization of the source's padding mechanism; it does not assert full ancestor-tube padding.

For arbitrary real intercepts a fully finite version samples shifts on a grid of spacing h_min/M. At each scale, the bad fraction is <=2/H+2/M; choose M>=H and enlarge the constant in H. This avoids a real fractional-part integration lemma.

The earlier all-coordinate Galilean alternative is also valid: with independent shifts A,B,T,

    (x,t,theta) -> (x-B-tA,t-T,theta-A),
    b -> b-B+T(theta-A).

The midpoint residual is exactly invariant. Padding time, slope and intercept coordinates at all m scales with margin beta~1/(d m) retains a fixed fraction of the original weight by the union bound. Midpoint neighborhoods shrunk by beta/4 lie in the literal rectangles; a cover uses O_d(beta^-(2d-1)) neighborhoods. A fixed dyadic parabolic dilation x->x/16, t->t/4, theta->theta/4 before bounded shifts keeps the transformed data inside the standard chart. These are bounded invertible affine changes of physical spacetime, so the original front/target and all labels can be transported explicitly. The Prop.3.1 cell-equality route above is simpler and needs no such shear.

## 8. Scoped unexpanded-notation test

Without padding or enlargement, the one-sided dyadic relation need not admit a subpower self-uniform refinement. Let N be dyadic, delta=N^-3, v=alpha=N^-1, h=N^-2, and

    omega_j=(x_j=j/N³, t=N^-1, theta_j=j/N²), 0<=j<N,

in one horizontal coordinate, with other coordinates zero. Their graph intercepts are zero. The dyadic h-tube at the common time has lower endpoint x_j and width (1+t)h, so R(omega_j) intersect X={omega_k:k>=j}. Any M-point retained subset has maximum neighborhood M but a last-point neighborhood of size one. Literal K-uniformity plus retention N/K would require K²>=N.

This tests the UNPADDED same-grid wording only. The actual WZ proof first uses the padding/thickening mechanism to remove precisely this boundary effect. The constructions above supply an explicit valid bridge; the example does not obstruct their use.

## 9. Subpower accounting and repository inventory

Let B=log(1/delta), W<=delta^-C, Q=exp(B^(5/6)) rounded upward to a dyadic integer, and use a macro scale ratio K_0=Q³. Then m=O(B^(1/6)), s<=m³, L=O(B^(1/6)), and

    log(2(4s)^(sL))=O(B^(2/3) log B)=o(B),
    log(Q²)=O(B^(5/6))=o(B),
    log(H^d)=O_d(log B)=o(B)

for the source's H=poly(B). Padding loses at most a factor two. For sufficiently small delta all retention/comparison losses are <=K_0 after increasing a fixed exponent if necessary. Thus the adapted self-uniform refinement has genuinely subpower loss. At fixed finite macro scale count the bookkeeping is easier. This construction is not claiming the precise polylogarithmic bound stated for every fixed m in WZ Lemma 4.2; it supplies the subpower bound needed for the present proof strategy.

The repository already has `exists_large_weight_fiber` in the uniform-incidence-core module (line 208), `exists_weighted_density_ge_average` in residual-phase-localization (line 131), and dyadic floor/cell definitions and containment calculations in wz-carrier-pruning (around lines 1100–1230). It has the newly proved symmetric weighted refinement. A targeted source search found no existing random dyadic padding or cyclic child-residue count. The finite residue lemma, tube-containment calculation, and neighborhood-cover adapter are therefore concrete new targets; they should be proved rather than inserted as certificates.

What remains after this adapter: deriving the actual extremal-class closure and matched multiplicities, then the transverse-tuple and grain construction in Proposition 18.2 Step 5. This note removes the false C/B-to-self-uniform substitution and explains how to obtain the required geometric self-uniformity with the source's genuine padding mechanism; it does not close those later geometric steps.

## Formal status at this checkpoint

See [WZ_LOCAL_GEOMETRY_PROGRESS.md](WZ_LOCAL_GEOMETRY_PROGRESS.md) for the exact
proved module boundaries and remaining handwritten geometric adapters. The
final finite volume theorem and the original main theorem are not completed.
