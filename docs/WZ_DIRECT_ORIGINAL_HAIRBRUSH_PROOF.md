# A direct finite proof of the original-point inverse hairbrush

Mathematically reviewed derivation, 2026-10-04. This is a paper proof to be formalized, not a Lean theorem and not a new hypothesis supplied to the final theorem. It uses only the actual original endpoint graph, the already proved original parameter-cell multiplicity/energy estimates, actual heavy cubes, elementary coordinate geometry, and finite counting. It does not assume Katz–Tao axioms or cite an unproved hairbrush estimate.

## Quantitative statement

Let P be a nonempty finite subset of [-1,1]^3, with n=|P|, and let 0<delta<=tau<=1/8. Assume K>=1 and

    |P intersect B(p,R)| <= K R^2 n

for p in P and delta<=R<=1. Let 0<lambda,nu<=1. Let G be an ordered graph in P x P, without diagonal pairs, satisfying |G|>=lambda n^2. Every original pair z=(p,q) in G is assumed rich at its original line:

    |P intersect T_z(tau)| >= nu tau n.

Write L=1+ceil(log_2(4/tau)). Then the argument below gives an actual affine plane slab S with half-width at most

    10^12 K^2 lambda^-1 nu^-1 tau

and

    |P intersect S|/n >= 10^-140 lambda^10 nu^14 K^-21 L^-3.

The numerical constants are deliberately rounded down/up. Minimum endpoint separation r is unnecessary for this coordinate proof; it is sufficient that endpoints differ. If the existing projective-normal overlap theorem is used instead, the same proof gives additional polynomial r losses, which are also harmless for the source application.

The graph can first be restricted to one largest-coordinate chart i, retaining density lambda0=lambda/3. Every pair line then has the form

    x_j = a_j x_i + b_j,

with a_i=1, b_i=0, and |a_j|<=1. All constants below use this common chart. For a pair z denote its slopes and offsets by a_z,b_z.

## Existing proved inputs used literally

1. Actual representatives R subset G, one for each occupied tau parameter cell, preserve all original graph endpoints in the representative's 8tau tube. Slopes of an original pair and its representative differ by at most tau in every coordinate.
2. Every 8tau tube contains at most 3200 K tau n original points.
3. The actual cell-injective family has two-point multiplicity

       # {T in R: x,y in T(8tau)} <= D/max(|x-y|,tau)^2, D=10^9,

   for arbitrary original bounded points x,y.
4. Its original rich-family energy gives

       |R| <= 4 D L K nu^-2 tau^-2.

5. One global set of heavy tau cubes, at threshold nu tau^2 n/768, has at most A tau^-2 members, A=768/nu. Each rich original tau tube meets at least beta/tau retained cubes, beta=nu/(8K).
6. Choose one original point x_c in P from every globally heavy cube c. The resulting X subset P is injective under the actual global cube-code map, |X|<=A tau^-2. The shade Y_T of T consists of the x_c whose cube meets the retained original points of T. It satisfies |Y_T|>=beta/tau and Y_T subset T(4tau). This is a global representative choice; there is no per-tube resampling or mass substitution.

## 1. Original graph wedges produce a transverse hairbrush

Set

    gamma=lambda0/(6400K),  theta=gamma/2.

Call an ordered graph wedge (p,q1,q2) bad when all slope differences of the two original lines are at most gamma. In that case q2 lies in the 4gamma tube about the original line (p,q1): use the point of the first line with i-coordinate q2_i; each remaining residual is at most 2gamma, because |q2_i-p_i|<=2.

The original tube Frostman bound therefore gives at most 1600K gamma n=lambda0 n/4 choices of q2 for each (p,q1). This tube bound is available when delta<=4gamma. In the nontrivial small-tau branch below, delta<=tau<=s<gamma, so that condition holds.

Let d_p be the outdegree. Cauchy–Schwarz gives sum d_p^2 >= |G|^2/n, and |G|>=lambda0 n^2. The number of bad wedges is at most (lambda0 n/4)|G|, hence at most one quarter of sum d_p^2. Thus there are at least

    (3/4)lambda0^2 n^3

good original wedges.

Assume tau<=gamma/4. Map the two original pairs to their actual representatives T,U. Some slope coordinate differs by at least theta, because each representative slope moves by at most tau. The original root p is in both 8tau tubes.

For such a transverse pair choose j with |a_T,j-a_U,j|>=theta. At any common point x the two graph residuals are at most 16tau, so

    |(a_T,j-a_U,j)x_i+(b_T,j-b_U,j)| <= 32tau.

For two common points x,y this implies |x_i-y_i|<=64tau/theta. The other graph coordinates differ by at most |x_i-y_i|+32tau, so |x-y|<=192tau/theta. If there is an original common point p0, all original common points lie in B(p0,192tau/theta). Frostman, or the trivial total-mass estimate when this radius exceeds 1, yields

    |P intersect T(8tau) intersect U(8tau)|
        <=40000K tau^2 theta^-2 n.

For a fixed root and representative T, all original neighbors mapping to T lie in its actual 8tau tube. There are at most 3200K tau n of them. Therefore each ordered representative pair has at most

    40000 * 3200^2 K^3 tau^4 theta^-2 n^3

preimage good wedges. The number J of transverse representative pairs sharing an original root is consequently at least

    J >= 10^-12 lambda0^2 theta^2 K^-3 tau^-4.

Divide by |R|<=4*10^9 L K nu^-2 tau^-2. Some actual stem T0 has a brush B with

    H=|B| >= h tau^-2,
    h=lambda0^2 theta^2 nu^2/(10^22 L K^4).

Every brush member has a slope gap at least theta from T0 and shares an actual original point with T0's 8tau tube. Fix one such original point p_T for every brush tube.

## 2. Explicit local cube counts and deletion near the stem

For a cube-injective point set inside a 4tau tube, graph residuals are at most 8tau. The existing GraphTubeGridCover.occupied_cells_bound with E=8, dimension 2, gives

    # points with x_i in any interval of length ell >=tau
        <=1200 ell/tau.

This is a literal count of the original global tau cubes, not a rotated-grid estimate.

In particular a ball of radius a>=tau contains at most 2400a/tau shaded representatives.

If x is in the 4tau brush tube and the s tube about T0, subtracting graph residuals at a slope-gap coordinate gives

    |(a_T,j-a_T0,j)x_i+(b_T,j-b_T0,j)| <=8tau+2s.

When tau<=s and theta<=1, all such x_i lie in an interval of length at most 20s/theta, so at most

    24000 s/(theta tau)

shade points lie within distance s of the stem.

Set

    beta=nu/(8K),  b=beta/2,  s=beta theta/96000.

Assume tau<=s. Delete from every Y_T all points within physical distance s of the stem. At most beta/(4tau) are deleted. The retained shades Z_T therefore satisfy

    |Z_T|>=b/tau,   Z_T subset T(4tau),
    Z_T subset X outside T0(s).

These inequalities also ensure tau<=b/4800. If instead tau>s, a coordinate slab of half-width tau/s covers all of P, already giving the announced conclusion. Thus every subsequent use of small tau is justified by this single branch split. In particular tau<=s implies tau<=gamma/4 and delta<=4gamma.

## 3. Universal finite union bound, requiring no planar or KT axiom

Let F be ANY subfamily of R with shades Z_T as above, and U_F=union Z_T. Set a=b/4800. For each x in Z_T, at most 2400a/tau=b/(2tau)<=|Z_T|/2 other shade points lie within distance a. Thus each T supplies at least b^2/(2tau^2) ordered pairs of shade points at distance greater than a.

At each such ordered point pair, the existing actual two-point multiplicity is at most D/a^2. Finite double counting yields

    |F| b^2/(2tau^2) <= (D/a^2)|U_F|^2,

and consequently

    |F| b^4 <= 10^17 tau^2 |U_F|^2.                 (U)

This holds in full three-dimensional space. Its use inside a plane group needs no projection theorem, slicing, area, volume, or separate planar Kakeya estimate.

## 4. Construct actual planes and group them by two scalar charts

Write the two non-i coordinates as a two-vector y and t=x_i. Let the stem be y=a0 t+b0. For a brush tube let v=a_T-a0, w=b_T-b0. It has v!=0. Choose n_T=(1,t_T) or (t_T,1), with |t_T|<=1, perpendicular to v. Choose the first chart when |v_2|>=|v_1| and the second otherwise. The plane

    n_T dot (y-a0 t-b0)=0

contains the exact entire stem line.

At its shared original point p_T, the two 8tau graph residuals give |v p_T,i+w|_infinity<=32tau. If x is any original point in T(8tau), its brush graph residual has infinity norm at most 16tau. Perpendicularity to v therefore gives

    |n_T dot (y-a0t-b0)| <=96tau.

Within each of the two charts, partition actual t_T values by floor(t_T/tau). In each occupied bin choose an actual member's value t_k. Assign all tubes in this bin to that actual stem plane. The assigned normal differs in one coordinate by at most tau. At original bounded x, the vector y-a0t-b0 has each coordinate bounded by 4. Thus every original point of every assigned T(8tau) satisfies

    |n_k dot (y-a0t-b0)| <=100tau.                  (S)

The full three-dimensional normal is (-n_k dot a0,n_k), with norm at least 1. Hence (S) is an actual affine plane slab of physical half-width at most 100tau. Its rich tube populations are literal original P populations.

## 5. Bound overlap away from the actual stem

Fix x outside T0(s), and write z=y-a0t-b0. The point of the stem at the same i-coordinate shows |z|_infinity>s/2.

For a first-chart slab containing x, |z_1+t_k z_2|<=100tau. If tau<=s/800, existence of such a slab forces |z_2|>=s/4: otherwise the larger coordinate z_1 would force a residual greater than s/4. The allowed t_k lie in an interval of length at most 800tau/s. Distinct bins floor(t_k/tau) then give at most 800/s+2<=802/s possible planes.

If tau>s/800, the total number of first-chart bins in [-1,1] is at most 2/tau+2<=1602/s. The second chart is identical. Thus every original point x outside the stem s-tube belongs to at most

    M0=4000/s

of the assigned slab groups' unions U_k. Therefore

    sum_k |U_k| <= M0 |X| <= M0 A tau^-2.

This is a direct finite pencil-of-planes overlap proof. It does not need ambient sphere packing, the endpoint separation r, or a desired slab concentration bound.

## 6. One group has critical size, and original energy pays its mass

Let n_k be the size of plane group k and n_max=max n_k. Applying (U) in each group gives

    sum n_k <= sqrt(n_max) * sqrt(10^17) tau b^-2 * sum |U_k|.

Since sum n_k=H>=h tau^-2, there is a group with

    n_max >= q tau^-2,
    q=h^2 b^4/(10^17 M0^2 A^2).

Let S be its actual slab from (S), and P_S=P intersect S. Every original 8tau-tube population for the selected group lies in P_S. Applying the exact square-sum swap and the original pointwise inverse-square energy, with x restricted to P_S and y summed over P, gives

    sum_T |P intersect T(8tau)|^2
        <=4 D L K |P_S| n.

All selected tubes are rich already at width tau. Therefore

    |P_S|/n >= q nu^2/(4 D L K).

Substitute A=768/nu, M0=4000/s, b=nu/(16K), s=nu theta/(768000K), h above, and theta=lambda0/(12800K). Rounding constants conservatively gives

    |P_S|/n >=10^-140 lambda^10 nu^14 K^-21 L^-3.

In the small-scale branch S has half-width at most100tau. In the other branch a coordinate slab of half-width tau/s suffices. Since lambda0=lambda/3,

    1/s=29,491,200,000 K^2/(lambda nu)<10^12 K^2/(lambda nu).

This proves the stated polynomial slab conclusion.

## Checks against false model implications

- A cone or a regulus has only approximately tau^-1 full rich ruling tubes at bounded parameters, not the critical approximately tau^-2 family forced by dense original pair data. The proof does not infer a contradiction from richness alone. For graph densities of order tau the trivial-width branch is allowed.
- A union of m unrelated planes can have density and richness of order 1/m. The conclusion permits a polynomial loss in both parameters, and selects an actual plane group carrying original mass. It does not incorrectly force all planes into one slab.
- Purely parallel families do not produce the graph wedge transversality. The original graph's off-axis neighbors are paid by the source Frostman estimate before any representative-family argument is made.
- Global critical cardinality alone is never used to assert Katz–Tao(1,1), small-cap sparsity, slab sparsity, or broadness. Broadness comes from original graph rows; overlap comes from explicit plane equations; mass comes back from the original pointwise energy.

## Source context

The target assertion is Wang–Zakharov arXiv:2609.22035, Appendix A.2, equation (253), local audit text lines6040–6070 (PDF pp114–115). The cited Maldague–Wang–Zakharov arXiv:2510.26644 Lemma3.5 is a dense-shading volume estimate under two Katz–Tao exponents. No implication from its hypotheses to the present graph configuration is asserted here. The construction above instead proves the particular inverse statement by elementary finite counting and common-chart geometry.

Primary source links: https://arxiv.org/pdf/2609.22035 and https://arxiv.org/pdf/2510.26644.

## Verification boundary and implementation qualifications

A separate mathematical check found no failed implication or constant in this finite argument. This is not a completed Lean theorem. Preserve the actual parameter-cell equality when constructing representatives: use the common-chart selection followed by the exact parameter-family constructor. Mere widened-tube containment cannot replace that equality in slope transfer.

Use each pencil slab with the exact displayed linear inequality, |N*x-c|<=100tau. Its physical half-width is 100tau/norm(N). Replacing it by a larger Euclidean slab changes the overlap argument. Localized energy keeps the ambient original P and its Frostman normalization; only the outer sum is restricted to P intersect S. The existing formal constructors use K=delta^(-eta), which is the required native case; the fully generic-K interface would require a separate specialization or extension.

The literal constant substitution gives approximately 2.638899496*10^(-130), leaving room for the stated 10^(-140). The large-scale coordinate-slab case also extends the conclusion to tau<=1. These numerical and scope checks do not stand in for the remaining Lean geometry and count assembly.


## Formal source-only implementation

The full original-P/G construction and exact constant substitution now have strict Lean and fresh imported foundational-axiom checks. See [the exact proved statement and scope](WZ_ORIGINAL_SOURCE_HAIRBRUSH.md). The 764-module canonical build and all eleven new imported checks also pass; this local estimate does not complete A.4 or the four-dimensional theorem.
