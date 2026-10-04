# A genuine single-scale tube engine, and the remaining small-shading gap

Status: handwritten mathematical argument, not a Lean-certified theorem.

This is an independent mathematical derivation. It does not assume WZ A.3, a projection theorem, a sum-product theorem, or an incidence theorem. It proves the endpoint s=1 and a stated near-endpoint range of A.3. It does **not** prove the small-s case needed by the native dimension-one graph caller.

## 1. Actual source and scope

Wang–Zakharov, Appendix A, Theorem A.3, printed page 107, asks for M=delta^(-t) essentially distinct planar delta-tubes, and the cap

    #{T: T is contained in W} <= lambda M,
    lambda=delta^u, w=delta sqrt(M),

for every w-tube W. Each tube has N comparable delta-cells of shading, with normalized s-Frostman constant K=delta^(-eta). The desired union is at least a constant times

    N sqrt(M) delta^(-s u/8).

Use 0<s<=1, 0<t<2, 0<u<=min(t,2-t). The apparent t=2 endpoint in WZ is empty because u>0.

The primary reference is [Orponen–Shmerkin, version4](https://arxiv.org/pdf/2301.10199v4), Theorem5.61, pp.60–62. Its dual conclusion leaves room for the WZ loss. The version matters; the current numbering differs.

## 2. Single-scale cap implies an all-scale parameter bound

Work first in the literal chart

    T(a,b) = {(x,y): |y|<=1, |x-a y-b|<=delta},
    |a|,|b|<=1.

Let S be its finite set of slope/intercept parameters, delta-separated in maximum norm, #S=M. Put L=lambda M and w=delta sqrt(M). Assume the original tube-containment cap. For small delta, w>=16 delta because t>0 is fixed.

For any center z in parameter space and r>=delta, write n_z(r)=#(S intersect B_infinity(z,r)). There is one universal C such that

    n_z(r) <= C (r/delta)^2,                         (2.1)
    n_z(r) <= C L max(1,(r/w)^2),                   (2.2)
    n_z(r) <= M.                                    (2.3)

Here (2.1) is the packing of disjoint parameter squares of side delta/2. To prove (2.2), tile a parameter square of radius r by squares of side w/16. Every such small parameter square is contained in a parameter ball of radius w/16 about some (a0,b0). If (a,b) belongs to that ball, then for |y|<=1,

    |(a-a0)y+(b-b0)|+delta <= w/8+delta <= w.

Thus its entire actual delta-tube lies in the actual w-tube T_w(a0,b0). Each small square contains at most L original tubes. A square of radius r needs at most C max(1,(r/w)^2) small squares, proving (2.2). Chart endpoints and half-open parameter cells only change C. A bounded number of direction charts treats arbitrary planar tubes. Dyadic tubes likewise have the required parameter packing and chart comparison.

There is a useful consequence which is stronger than just restating the cap:

    n_z(r) <= C r sqrt(L)/delta for every r>=delta. (2.4)

For r<=w, multiply (2.1) and the bound n_z(r)<=CL from (2.2): n_z(r)^2<=C^2 r^2 L/delta^2. For r>=w, multiply (2.3) and (2.2), and use w^2=delta^2 M: n_z(r)^2<=C L r^2/delta^2. Taking nonnegative square roots proves (2.4).

Thus the cap produces a real all-scale, one-dimensional parameter counting bound with coefficient sqrt(lambda M)/delta. No incidence information has been discarded in deriving it.

## 3. Thick-tube intersection geometry

For different parameters z=(a,b), z'=(a',b'), put

    d=max(delta,|a-a'|,|b-b'|).

Use the centers of the actual shading delta-cells. A cell belonging to both shadings has its center in fixed C delta enlargements of both tubes. Their intersection, when nonempty, has diameter at most C delta/d.

Here is the elementary calculation, including the nearly parallel case. For a common point with |y|<=1+O(delta), subtraction of the two strip inequalities gives

    |(a-a')y+(b-b')| <= C delta.

If d is larger than a sufficiently large fixed multiple of delta, this forces |a-a'|>=c d. Subtract the inequalities at two common points to obtain

    |a-a'| |y-y'| <= C delta.

Hence |y-y'|<=C delta/d, and the original strip equation with |a|<=1 bounds |x-x'| by the same amount. If d=O(delta), the bounded ambient box gives the result directly. In particular one never replaces thick incidence by exact collinearity, and one never divides by a possibly zero angle.

Let each shading Y_z have between N and 2N original delta-cells and satisfy

    #(Y_z intersect B(q,r)) <= K r^s #Y_z

for delta<=r<=1, where K>=1. The intersection geometry and this Frostman estimate imply

    #(Y_z intersect Y_z') <= C K N (delta/d)^s.      (3.1)

If the displayed radius C delta/d exceeds 1, use the trivial #Y_z<=2N instead; if it is below delta, the bounded parameter chart gives a fixed adjustment of the constant. The same bound includes z=z' through d=delta. In this paragraph Y_z denotes the literal set of delta-cell labels. Ball counts can equivalently be imposed on the cell centers with a universal constant adjustment.

## 4. A full finite energy and union estimate

Let J=2+ceil(log_2(4/delta)). Partition all z' by the actual distance d in dyadic annuli [2^j delta,2^(j+1)delta). Equations (2.3) and (2.4), with

    A=C sqrt(L)/delta,

give n_z(r)<=min(M,A r). Consequently, for 0<=s<=1,

    n_z(r)/r^s <= M^(1-s) A^s.                    (4.1)

For example, this follows by multiplying n_z(r)^(1-s)<=M^(1-s) and n_z(r)^s<=(A r)^s. Each annulus contributes at most twice this quantity to sum_z' d(z,z')^(-s). There are at most J annuli. Summing (3.1) therefore gives

    sum_z' #(Y_z intersect Y_z')
        <= C K N J M^(1-s) L^(s/2).               (4.2)

Define mu(q)=#{z:q belongs to Y_z} on the actual union of original delta-cell labels. Exact finite double counting gives

    sum_q mu(q) = sum_z #Y_z >= N M,
    sum_q mu(q)^2 = sum_z,z' #(Y_z intersect Y_z').

Cauchy–Schwarz and (4.2) prove the genuine geometric estimate

    #union_z Y_z >= [N/(C K J)] M^s / L^(s/2)
                  = [N/(C K J)] M^(s/2) lambda^(-s/2).   (4.3)

All sets here are the input tube parameters and their actual shading cells. The only hypotheses are separation, the single-scale cap, and actual shading Frostman bounds. No desired energy or output-cardinality certificate appears as a premise.

For fixed 0<s<1 one can remove J by summing the two geometric tails either side of r=M/A. A constant depending on s then replaces J. Keeping J is simpler, is uniform for s in [0,1], and costs only a subpower.

## 5. Precisely what this proves

At s=1, (4.3) reads

    #union Y >= [N sqrt(M)/(C K J)] delta^(-u/2).   (5.1)

This is stronger than the s=1 case of A.3. For example choose eta<=u/4, then choose delta small enough that C J<=delta^(-u/8). Equation (5.1) yields exactly the required gain delta^(-u/8). Thus the quantifier order is: fix t,u; fix eta<=u/4; then choose delta small enough for the stated logarithmic absorption and w>=16delta. The constants and threshold can be uniform on compact positive t,u ranges.

For general s, comparison of (4.3) to N sqrt(M) gives the gain exponent

    g = s u/2 - (1-s)t/2.

It proves a positive gain whenever g>0, and proves the specific WZ su/8 gain whenever

    D = 3 s u/8 - (1-s)t/2 > 0,
    equivalently s > 4t/(4t+3u).                  (5.2)

For that statement choose eta<D/2 and then delta small enough that C J<=delta^(-D/2). Strict inequality leaves room for harmless chart losses.

This range does not cover the native caller. In A.1, original point dimension t_point<=1 gives

    sigma=t_point-gamma,
    a=t_point-sigma=gamma,
    s_bar=min(a,1)=gamma,

where gamma=min(zeta/100,min(t_point,1)/2). In particular the native t_point=1 graph still has arbitrarily small shading exponent gamma. Its tube-family dimension t_bar is a separate parameter in [chi/2,2-gamma]. Nothing in the checked construction enforces (5.2). The overlap argument then loses the fixed power

    (1-s_bar)t_bar/2 - 3 s_bar u_bar/8

against A.3, before eta and logarithms. The endpoint result must not be advertised as closing native radial 13.2.

## 6. Why more parameter counting alone cannot repair the deficit

The inverse-distance potential underlying (4.3) is sharp under the single-scale cap. Take integers q>=m>=1, set M=q^2 and L=m^2, and place a q by q parameter lattice of spacing

    h=delta q/m=delta/sqrt(lambda)

inside a square of side

    R=q h=delta M/sqrt(L)=w/sqrt(lambda).

A w-square contains O(m^2)=O(L) points. For a positive fraction of centers z, a positive fraction of the M other parameters have distance comparable to R, so

    sum_z' d(z,z')^(-s) >= c_s M R^(-s)
                              = c_s delta^(-s) M^(1-s)L^(s/2).

This matches the power in the upper estimate. The square fits into a bounded chart exactly in the allowed range t+u<=2 (up to fixed constants).

For s=1 and full tube shadings, the resulting union has order R/delta^2, which also matches (5.1) with N of order delta^(-1). For s<1, this is **not** a counterexample to A.3: it demonstrates sharpness of the parameter-potential estimate, not simultaneous attainability of every per-pair Frostman intersection bound. A successful small-s proof must use the geometric compatibility of the shading sets across many different intersecting tubes. Estimating every pair separately throws that information away. Merely refining the parameter cap, or substituting an exact-line Szemeredi–Trotter statement, does not repair this.

## 7. A precise residual geometric ingredient in the primary proof

The primary dependency chain uses OS Theorems5.35 and5.7 through the robust
regular projection Corollary4.9; the high-density Corollary5.51 uses Fu–Ren
thick-incidence estimates. These are geometric inputs, not consequences of
the existing BSG construction alone.

One sufficient weaker local theorem, isolating exactly the geometric strength needed, is this:

For each fixed s>0 and each loss kappa>0, a (delta,s,delta^(-epsilon),N)-nice thick-tube configuration on a (delta,sigma,delta^(-epsilon))-Frostman carrier of cardinality comparable to delta^(-sigma) has at least

    N delta^[-sigma/2 - (s/4)min(sigma,2-sigma) + kappa]

distinct tubes, for 0<sigma<2, with epsilon>0 and delta_0>0 chosen before the configuration. Required uniformity on a fixed compact sigma interval must be established; positivity of an unspecified epsilon(sigma) does not imply a positive uniform infimum.

This local theorem is weaker than the three primary estimates just listed. It is still a genuine missing thick-incidence theorem, not a proposed axiom or a proved Lean result. In particular its middle-density part supplies an actual power beyond the elementary square-root incidence count.

For perspective, the final scalar branching step can be simplified independently. Let beta:[0,1]->[0,2] be convex, nondecreasing and 2-Lipschitz, beta(0)=0, beta(1)=t, and A=1-t/2. If beta(A)>=u, then

    integral_0^1 min(beta'(x),2-beta'(x)) dx >= u. (7.1)

To check it, let B separate slopes at most 1 from slopes at least 1. The integral equals 2(beta(B)+A-B). If B<=A, use beta(A)<=beta(B)+2(A-B). If B>=A, use t-beta(B)<=2(1-B), giving A-B>=-beta(B)/2, and monotonicity beta(B)>=beta(A). Both cases yield (7.1). Thus a local gain (s/4)min(sigma,2-sigma), multiplied through the actual incidence factorization, supplies gain su/4 before losses; WZ's su/8 leaves room. For the discrete branching decomposition one retains its endpoint approximation errors. This arithmetic does not prove the local geometric estimate or the factorization.

## 8. Formalization boundary

The full Sections 2–4 are a feasible standalone finite geometric implementation: parameter grid cover, actual thick-strip intersection, dyadic inverse-distance sum, literal shading collision count, and Cauchy–Schwarz. They would give a proved endpoint engine with no new axiom. This handwritten note adds neither a Lean theorem nor a conditional Lean wrapper. The native small-s radial gain remains open until a genuinely stronger multi-tube incidence estimate is proved.

## 9. Ordered shading edges: exact multiplicity and crossing obstruction

This is an audit of a concrete proposed thick-tube crossing argument, not a claim that no such argument can ever work.

Take two distinct shading delta-cells whose centers are separated by ell>=C delta. In a bounded slope chart, any tube meeting both has its slope in an interval of length O(delta/ell), and its intercept, after the first slope is fixed, in an interval of length O(delta). Thus parameter delta-packing gives

    multiplicity of this cell pair <= C/ell.       (9.1)

The original w-cap improves this only to

    multiplicity <= C min(ell^(-1),
                         L max(1,delta/(w ell))). (9.2)

To derive the second term, cover the actual thin parameter parallelogram by O(max(1,delta/(w ell))) parameter w-squares. A fixed affine shear with bounded coefficients turns it into an axis-parallel rectangle and changes only constants.

The size 1/ell is real, not a weakness in that proof. Place cell centers at (0,0) and (0,ell); tubes with intercept b=0 and slopes a=k delta for |k|<=c/ell meet both cells. This gives a constant times 1/ell distinct tubes. If ell>=delta/w and 1/ell<=L, this entire pencil fits into one w-square and is allowed by the cap. It can be embedded as a small subfamily of a globally dispersed cap-admissible family.

In particular, even N evenly spaced shading points give consecutive edges of length about 1/N. Equations (9.1)–(9.2) allow edge multiplicity of order N when

    N<=sqrt(M) and N<=L.

Both inequalities are compatible with the hard native small-s regime. The cap therefore does not imply a constant, or even subpower, worst-case edge multiplicity.

If one optimistically had only O(M^2) crossings, a multigraph crossing estimate with E of order MN and multiplicity mu of order N yields

    V >= c E^(3/2)/(sqrt(mu) M) = c N sqrt(M),

which is exactly the baseline, with no positive gain. The extra sqrt(N) furnished by exact-line Szemeredi–Trotter is cancelled by the genuinely possible thick-edge multiplicity.

Thinning evenly spaced points by a factor k produces E of order MN/k and mu of order N/k. Under the same optimistic crossing bound its lower estimate becomes N sqrt(M)/k. Connecting kth neighbors without thinning retains E, but creates overlapping bundles: even for straight source paths the number of potentially crossing edge pairs grows by k^2. This does not improve the bound.

For merely s-Frostman shadings, a stronger obstruction to long-edge selection is available. A separated s-dimensional Cantor discretization with N of order delta^(-s) has only O(r^(-s)) consecutive gaps of length at least r, for delta<=r<=1. Thus selecting only r-long consecutive edges can retain a fraction as small as

    O((delta/r)^s)

of the original N edges. If r=delta^a for fixed a<1, this is a fixed power delta^(s(1-a)), not an arbitrarily small bookkeeping loss. This construction obeys actual normalized Frostman bounds with constants independent of delta (e.g. the standard middle-thirds Cantor construction for s=log(2)/log(3)).

There is also a separate thick-crossing issue. Choose at most one center per horizontal grid row in each tube, losing a fixed factor, and join consecutive centers. The resulting path is y-monotone and lies within O(delta) of its central line. For two source tubes at parameter distance d, all their path intersections lie in the common strip window of diameter O(delta/d). A difference of the two piecewise-linear graph functions can have one zero per linearity interval. Its number of such intervals is bounded by the number of vertices of BOTH paths in that common window, plus a constant. After a generic arbitrarily small perturbation to remove coincidences, this gives the valid upper bound

    crossings <= C M^2 +
        C sum_T,T' [#Y_T in their common window + #Y_T' in that window]
              <= C M^2 + C K N J M^(2-s) L^(s/2). (9.3)

A claim of only O(1) crossings per thick tube pair is not justified for these paths; the two polygonal paths may oscillate inside their common strip window.

Using the nontrivial term in (9.3), E~MN and mu~N in the crossing inequality gives, at best,

    V >= c (KJ)^(-1/2) sqrt(N) M^(1/2+s/4) lambda^(-s/4).

For the allowed minimal shading size N~delta^(-s), its ratio to N sqrt(M) is

    c (KJ)^(-1/2) delta^[s(2-t-u)/4],

which is at most a constant because t+u<=2. So even this more optimistic algebra has no positive power in the full A.3 parameter range. The case E not large enough relative to mu V is no better.

A possible successful crossing-based proof must therefore establish a genuine **average** pruning or routing improvement using correlations of all original shadings: it must beat the possible edge multiplicities while retaining delta^o(1) MN incidences, or reduce crossings beyond (9.3). Neither conclusion follows from the one-scale cap and individual Frostman bounds by the elementary estimates above.

## 10. What the primary proof does instead

OS equation5.27 controls how often direction counts grow rapidly. At the
remaining levels, equations5.29–5.31 synchronize many original direction
fibers on a common dense direction set. The robust regular projection
Corollary4.9/restated5.32 supplies the positive power, which the multiscale
incidence factorization combines.

This uses compatibility across the original shadings. The finite slow-growth
selection alone does not prove the gain, and neither the pair-potential
calculation nor the naive crossing graph supplies that projection expansion.
