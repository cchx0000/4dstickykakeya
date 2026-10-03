# Exact parameter and working-radius checklist for the native alignment assembly

Read-only checklist, 2026-10-03. Companion to the completed handwritten Lemma 5.3 patch adapter. This is a handwritten combined derivation; its native callers are not all formalized.

## 1. Use the actual source-mass exponent

For the FIRST alignment refinement the labels are original geometric points, one point-line pair per point. Delta-separation in a bounded d-dimensional box gives

    W=|A| <= C_d delta^(-d).

If one writes W<=delta^(-d-eta), the leading constant has been absorbed only after requiring delta^(-eta)>=C_d.

For a WEIGHTED later call, do not automatically reuse the quotient-space dimension d. Establish an actual bound

    W <= C_w delta^(-D0)

from the current label domain. For native incidences, the tube count times the actual per-tube point-bin count gives such a bound; any repeated original marks require their recorded multiplicity factor. For a weighted quotient point, the vertex weight cap must be included. All these are polynomial bounds in the original mesh, but their exponent can exceed the quotient dimension.

Either absorb C_w into an explicitly chosen exponent margin v0>0, obtaining D_w=D0+v0 for sufficiently small delta, or keep it in the height choice below.

## 2. Q, L, and finite refinement cost

Let the relevant output scale ratio satisfy N>=delta^(-chi), with chi>0 fixed before delta. Choose u>0 before delta and

    Q=max(4, ceiling(N^u)).

If W<=delta^(-D_w), take

    L=ceiling(D_w/(u chi)).

Then Q^L>=N^(uL)>=delta^(-D_w)>=W. If retaining the leading constant explicitly, it suffices to take

    L=ceiling(D0/(u chi))+ceiling(log_4(max(1,C_w))).

The refinement relation count d_rel is FIXED before delta. Thus

    C_ret=2(4 d_rel)^(d_rel L)

is a fixed positive integer. For a chosen retention allowance v_ret>0, requiring N^v_ret>=C_ret gives retained mass at least N^(-v_ret)W. This is a legitimate final small-mesh condition, not an extra hypothesis on the selected subset.

For N^u>=4, Q<=2N^u and the comparison factor obeys

    Q^2<=4N^(2u).

To fit a budget N^v_unif, choose v_unif>2u first and then require N^(v_unif-2u)>=4. The choices of u,L,d_rel precede this final choice of delta.

Before the winning adjacent direction scale is selected, use the minimum ratio of all candidate adjacent dyadic scales as N. Their ratios are within a factor two of one another, so the same fixed positive chi works after slightly decreasing it. The first refinement therefore does not depend circularly on the eventual winning i.

## 3. Literal dyadic working radii

For dyadic rho<=tau with tau/rho=2^M and fixed h>=1, define

    r_j=rho*2^floor(jM/h),  j=0,...,h.

These include both endpoints and are nested original dyadic grid scales. Repeated radii may be removed. Consecutive DISTINCT scales have ratio at most

    2(tau/rho)^(1/h).

Insert all candidate parent scales, all required old-grain/fine-height scales, and the finite list of scales occurring in the geometric relations. Inserting scales can only reduce the largest gap. This does not make the number of relations depend on delta when those lists have fixed depth.

For ambient radii across [delta,1], use the same formula with rho=delta,tau=1 and a fixed depth h0. Since N>=delta^(-chi), the gap is at most 2N^(1/(chi h0)). Choose h0 sufficiently large compared with d/(chi times the allotted interpolation exponent).

For the first fiber refinement across [rho,tau], if the final ratio is N comparable to (tau/rho)^(1/m), the gap loss is N^(O(dm/h)). Thus choose h sufficiently large compared with dm divided by its output exponent budget.

For the final lattice product call, N is dyadic (or a fixed dyadic multiple after finer quantization). Use integer radii 2^floor(j log_2(N)/h2). The same endpoint and gap statements apply. Choose h2 sufficiently large compared with d divided by its allotted output loss.

## 4. What is and is not proved between working radii

If the final set has AD bounds at working radii and consecutive radii have ratio at most Lambda, monotonicity of centered ball counts gives the bounds at EVERY intervening radius with an extra factor at most Lambda^q, where q is the relevant exponent. Here 0<=s<=t<=d and 0<=t-s<=d, so Lambda^d is sufficient simultaneously for ambient, fiber and quotient AD.

For upper bounds at arbitrary centers, use an actual point in the ball, if one exists, and enlarge the radius by two. Empty intersections are automatic. Euclidean versus box norms and the fixed shear contribute only dimensional constants.

This interpolation loss must appear in the final exponent budget. Uniformity on finitely many radii alone is not an all-scale AD conclusion.

The tube Katz–Tao profile has a different provenance: the cover-profile stopping construction tests ALL dyadic nested pairs (u,v) in the epoch interval. It therefore directly supplies those dyadic upper estimates. Nondyadic u,v follow by bounded upward dyadic rounding and grid covering. There are O(log(1/delta)^2) possible test pairs, but they are NOT all relations in the self-uniform refinement. Their number contributes only the polynomial epoch count and its polylogarithmic retention loss.

At the final isolated-patch radius tau_out=C_ball b, extend from the working maximum b to tau_out by a fixed top-scale constant and total population/nonemptiness. Do not insert an unbounded extra range implicitly.

## 5. The literal metric-AD grid adapter

The remaining native menu estimate has the form

    #D_rho(A intersect B(x,tau)) <= C_d K^2 (tau/rho)^t,
    delta<=rho<=tau<=1, 0<=t<=d.

Take a maximal rho-separated subset of A intersect B(x,tau). Its rho/3-balls are disjoint. Original lower AD counts apply to the FULL A in those balls; current residual or shading subsets are not used for the lower estimate. A net rho-ball meets only O_d(1) original fixed-grid rho-cells.

When rho<3delta, the center point itself gives the needed lower count: 1>=K^(-1)(rho/(3delta))^t. This explicitly handles the fine endpoint.

If x belongs to A, enlarging the parent to B(x,2tau) gives a safe 6^t K^2 net bound. For an arbitrary center x, first choose an actual A-point in the nonempty ball and use a larger enclosing ball; 9^t K^2 is a safe bound with the rho/3 choice. Since t<=d, either is absorbed in C_d. When the enclosing radius exceeds the stated AD maximum, cover the original bounded domain by a fixed number of admissible top-scale balls.

Every other alignment menu follows from this adapter, the actual graph-tube grid cover, the epoch's inherited tube upper profile, and the already constructed spine/column and angular-menu counts. A bounded shear or fixed-factor quantization maps one r-cell into O_d(1) r-cells; include that elementary covering factor explicitly when changing grids.

## 6. Final order and checklist

Choose, in order:

1. Requested output zeta and the fixed dimension.
2. Direction depth m, stopping epsilon, and the resulting positive chi_profile and chi_safe.
3. Incoming eta and all loss exponents, including source-mass, uniformity and interpolation margins.
4. Every fixed-depth radius list, geometric relation and appended grain/height partition; thereby fix d_rel.
5. The mass exponent D_w, Q exponent u, height L and constant C_ret for each refinement.
6. The fixed chart, quantization residue modulus, patch color modulus and top-scale constants.
7. Delta small enough for all retained strict exponent margins, rounding conditions and constant absorptions.

Actual Q and dyadic radius values then depend on the chosen mesh, but their exponent parameters, list lengths and retention-height bounds were fixed beforehand. The resulting chi_safe may be much smaller than the displayed source formula; its positivity is what the later universal theorem needs.
