# Theorem 13.5: a proved finite Kaufman step and the remaining deep inputs

This note concerns the actual finite auxiliary route toward Proposition 17.3. It neither assembles the native configuration nor asserts Theorem 13.5 or the final compact packing-three theorem. All finite selections below use original point, slope, and incidence labels. No desired projection or expansion estimate is introduced as a certificate.

WZ source locations: Theorems 13.2 and 13.4 on pp. 51–52; Theorem 13.5 and equations (78)–(93) on pp. 52–55; Lemma 13.7 on p. 54; Appendix A.1 and Lemma A.2 on pp. 106–107; Theorem A.3 on p. 107 and its use on pp. 110–111. The WZ PDF/text already downloaded in the shared audit directory is the primary source inspected here.

## 1. Native specialization and dependency map

For the (d−1)-linear contradiction, the needed scalar nonlinear expansion has beta=1, C={1}, and alpha<1. Thus the last ABC sum-product invocation in the general Theorem 13.5 proof is unnecessary: after equation (93), a beta-dimensional subset already forces the lower count of A. This does not remove the following two substantial inputs:

1. The radial projection theorem, WZ 13.2/A.1. Its proof uses the positive-power planar Furstenberg improvement A.3. The initial graph in this application can be made metric 1-AD by the concrete native construction in Section 4 below, resolving its uniformity premise in this restricted class.
2. The genuinely asymmetric Balog–Szemeredi–Gowers statement 13.7, including an iterated sumset conclusion. The available repository dependency proves an equal-cardinality two-set BSG theorem, not this statement.

The Kaufman step, Theorem 13.4, is elementary enough to prove directly from finite pair geometry. Sections 2–3 give a quantitative construction and proof.

## 2. Exact finite projection-pair estimate

Let delta=2^(−n), n>=1, let 0<t<=1, and let P subset [-1,1]^2 and Lambda subset [-1,1] be nonempty finite sets. Put N=|P| and M=|Lambda|. Assume normalized maximum-norm Frostman bounds

    |P intersect B_infinity(p,r)| <= K_P r^t N,
    |Lambda intersect [c−r,c+r]| <= K_Lambda r^t M         (K1)

for every center and delta<=r<=1, with K_P,K_Lambda>=1. For r>=1 the corresponding bounds follow trivially. Point and slope delta-separation are compatible with these hypotheses but are not needed separately in this counting argument. We count ORIGINAL points when their projected values coincide.

Write pi_lambda(x,y)=x−lambda y and d(p,p')=||p−p'||_infinity. For r>=delta, define the actual ordered far-pair count

    E_r = #{(lambda,p,p'): lambda in Lambda, p,p' in P,
          d(p,p')>=4r, |pi_lambda(p)−pi_lambda(p')|<=r}.

Let L=n+3. Then

    E_r <= 4 K_P K_Lambda L r^t N^2 M.                   (K2)

Here is the geometric proof. Put dx=x−x', dy=y−y', and d=max(|dx|,|dy|). If |dx−lambda dy|<=r, |lambda|<=1, and d>=4r, then |dy|>=d/2. Otherwise |dx|=d and |dx−lambda dy|>d/2>=2r, a contradiction. Consequently the admissible lambdas lie in the ACTUAL interval

    |lambda−dx/dy| <= r/|dy| <= 2r/d.

There is no division by zero. Since d<=2, the radius 2r/d is at least r>=delta, so (K1) applies without an unproved estimate below the mesh.

Partition the possible distances into at most L dyadic annuli s/2<d<=s, with s<=2. On one annulus, (K1) gives at most K_P s^t N^2 ordered point pairs. Each such pair has at most K_Lambda (4r/s)^t M admissible slopes. Their product is at most 4 K_P K_Lambda r^t N^2 M because t<=1. Sum the annuli to prove (K2). If the displayed slope interval has radius above one, use the trivial M bound, which is smaller than the same displayed estimate.

This actual line-projection interval bound is the smallest genuinely geometric formal target here. The remaining argument is finite counting, deletion, and interval-grid covering.

## 3. Constructing the robust projected subsets

Fix 0<q<1 and set

    A = 8 K_P K_Lambda L^2/q^2.

For every lambda and every dyadic scale r in {1,1/2,...,delta}, partition P by the literal half-open cells of floor(pi_lambda(p)/r). Call a cell heavy if its ORIGINAL population m exceeds A r^t N. Let H_(lambda,r) be the set of original points in those heavy cells.

For any p, the number of p' at distance less than 4r is at most 4K_P r^t N. This also holds when 4r>1, by the trivial bound. Since A>=8K_P, at least m/2 of the points paired with any point in a heavy cell are far. Thus that cell contributes at least m^2/2 ordered pairs to E_r, and

    E_r >= (A/2) r^t N sum_lambda |H_(lambda,r)|.

Combining with (K2) yields

    sum_lambda |H_(lambda,r)|
          <= 8K_P K_Lambda L N M/A.

Let H_lambda be the union of these heavy-cell point sets over all dyadic working radii. There are at most L radii, so

    sum_lambda |H_lambda| <= q^2 N M.                    (K3)

Define

    Lambda_good = {lambda: |H_lambda|<=qN},
    P_lambda = P minus H_lambda.

Markov's finite counting inequality gives

    |Lambda_good| >= (1−q)M,
    |P_lambda| >= (1−q)N,      lambda in Lambda_good.      (K4)

For any original point subset P' subset P_lambda with |P'|>=q|P_lambda|, its projected multiset obeys, at every center c and every real radius r in [delta,1],

    #{p in P': |pi_lambda(p)−c|<=r}
       <= [48 K_P K_Lambda L^2/(q^3(1−q))] r^t |P'|.     (K5)

Indeed choose a dyadic h with h<=r<2h. The interval [c−r,c+r] meets at most six half-open h-cells, including endpoint cells. Any cell meeting P_lambda was not heavy, so it has ORIGINAL mass at most A h^t N. The interval therefore contains at most 6A r^t N points. Divide by |P'|>=q(1−q)N. This proves (K5) on the SAME retained set for every subset and every scale; no later arbitrary restriction is asserted to retain a lower bound.

Taking K_P=K_Lambda=delta^(−eta), q=delta^eta, and delta small enough that q<=1/2, the coefficient is at most

    96 L^2 delta^(−5eta).

If eta<epsilon/10, choosing delta last makes this at most delta^(−epsilon). Thus (K4)–(K5) prove the source's robust conclusion of Theorem 13.4, with explicit constants and all scales, including coincident projected values. Empty P or Lambda can be handled separately by the empty-set conclusion; the substantive theorem above uses their nonemptiness only for normalizations.

The same proof has a weighted-point version if (K1), heavy populations, retained mass, and ordered pair counts use original nonnegative point weights consistently. Merely substituting a weighted total in an unweighted cardinality bound is not sufficient. The unweighted statement already matches the required distinct geometric point caller.

## 4. Native beta=1 graph uniformity from anchored time populations

Theorem 13.2/A.1 assumes a spatially uniform planar set. The graph Gamma={(b,F(b))} in the abstract Theorem 13.5 is immediately separated and Frostman, but those facts alone do not establish the stated uniformity premise. Selecting an unrelated uniform subset after the prescribed dense graph has been formed could lose its density.

For the bounded native caller this premise can be proved BEFORE forming the L-tuples and their additive graph. Here is a precise finite statement.

Let B be a subset of a translate of h Z in [-1,1], with 0<h<=1. Let the finite nested dyadic working radii include h and 1, and let successive radii have ratio at most G>=1. Assume that every occupied original working interval I of length s has

    |B intersect I| >= c s/h,                 0<c<=1.     (N1)

Let F:B->R^m be an actual bounded vector field such that, in the same working intervals,

    ||F(b)−F(b')|| <= L_F s,       b,b' in B intersect I.  (N2)

Fix ANY linear scalar projection psi of operator norm at most R. Put A0=max(1,R L_F). Then its graph Gamma_psi={(b,psi(F(b)))} satisfies, for every graph center and h<=r<=1,

    [c/(2A0G)] r/h
       <= |Gamma_psi intersect B_infinity(center,r)|
       <= 3r/h.                                         (N3)

Proof: the upper bound is the original time-grid count. If r>=2A0h, choose a working interval containing b of length s<=r/(2A0), maximal among the allowed scales. Then s>=r/(2A0G), and all its graph points lie in the ball by (N2), proving the lower bound from (N1). If r<2A0h, the center itself proves the same lower bound. The argument works at a boundary because the occupied ORIGINAL interval containing b is used; no arbitrary ball restriction is claimed to inherit density.

Consequently all these scalar graphs are metric 1-AD, and hence spatially uniform, with constants bounded by C A0G/c. The statement holds simultaneously for all bounded psi; it does not need one refinement per possible direction. Maximum and Euclidean norms change fixed factors. A fixed bounded affine normalization places the graphs in the square used by Theorem A.1.

For the actual Section 20 normalization, the nonlinear expansion mesh is h=rho, while the original physical time scale corresponding to h is rho^2. The normalized vector field is

    F(b) = [f(z0+rho b)−f(z0)]/(tau/rho).

If the next working ancestor of the physical time scale has ratio at most G0, then its oscillation bound gives L_F<=C rho^2 G0/tau. Choosing the actual tau>=C G0 rho^2 makes L_F bounded. This is the reason the working-grid factor must be retained in tau. The condition tau<=rho follows by taking the original loss exponent smaller than the fixed power gap for rho.

The anchored population (N1) is produced by the already proved original-label partition refinement on time intervals. Keep entire original height fibers after selecting the time labels, then construct the one-arm/L-tuples on that retained set. Their average-incidence count still applies because each occupied height/spatial class and each occupied original grain/spatial class has its prepared lower population. The native scalar graph used by the radial theorem is therefore genuinely uniform; it is not an additional hypothesis on the final target.

A separate actual coarsening step is still needed when the initial time set is finer than h. Its deterministic time-cell image, actual representative values of F, and the maximum original fibers must be used. The within-cell bound from (N2) makes the scalar function move by O(h); dense additive-graph counts and non-affine tolerances must be transported with those original fibers. The graph-uniformity statement (N3) itself is for the resulting explicit h-grid labels.

## 5. First geometric preparation in Theorem 13.5

Let B be delta-separated and beta-Frostman, and suppose F:B->[-1,1] satisfies the actual non-affine condition (78). The following elementary conversion supplies the two-ends hypothesis for the radial theorem.

Take a planar strip of width delta^(2epsilon1), with unit normal (n_x,n_y). If |n_y|>=delta^epsilon1, solving its inequality for F(b) puts its graph points in an affine-error strip of vertical thickness at most C delta^epsilon1. Use (78), with a fixed subdivision or a slightly weaker exponent to absorb C. If |n_y|<delta^epsilon1, then |n_x| is bounded below and the boundedness of F forces b into an interval of length at most C delta^epsilon1. The beta-Frostman bound applies to that ORIGINAL time interval.

Thus the graph has two-ends mass bounded by a fixed multiple of

    delta^epsilon2 + K_B delta^(beta epsilon1).

Under eta<=beta epsilon1/2, this is a positive power of delta. Applying Theorem A.1 with tube-width exponent 2epsilon1 requires 2epsilon1<=zeta_rad/8, namely zeta_rad>=16epsilon1, before harmless slack. The printed transition after (78) uses an 8 instead of a 16; a formal hierarchy should keep the actual input width and adjust the constants.

Slopes of chords may be large, even for a dyadically Lipschitz function. Theorem 13.4 only covers lambda in a bounded slope chart. Use two actual projective charts for chord directions, reflecting or interchanging the graph coordinates where necessary. The radial direction measure and its multiplicity must be transported to those charts, rather than asserting that every chord slope is in [-1,1].

There is also a sign to track: with pi_lambda(x,y)=x−lambda y on the transposed graph (F(b''),b''), the chord slope lambda=(F(b')−F(b))/(b'−b) gives a MINUS mixed expression. To obtain the PLUS expression in (86), apply the projection theorem to the reflected slope family −lambda. Reflection preserves the same Frostman counts. This makes the later polarization identity consistent.

## 6. The actual deep radial input

WZ Theorem A.3 asks for a finite family of essentially distinct planar delta-tubes, #T=delta^(−t), 0<t<2, and 0<u<=min(t,2−t). At the intermediate width w=delta sqrt(#T), every w-tube must contain at most delta^u #T members. Each tube has an actual s-Frostman shading with comparable delta-cover cardinal N, 0<s<=1. Its conclusion improves the baseline union count by a positive power:

    |union Y(T)|_delta >= c delta^(−su/8) N sqrt(#T).

This is stronger than finite Cauchy–Schwarz or ordinary AD counting. Bounded coordinates and original lattice labels do not supply it for free.

The cited source is version-specific: [Orponen–Shmerkin, arXiv:2301.10199v4](https://arxiv.org/pdf/2301.10199v4), Theorem 5.61, printed pp. 60–62. In its point/tube dual formulation the gain is su/4; WZ uses slack. The [current v5](https://arxiv.org/pdf/2301.10199) explicitly records that this theorem was removed from that version. The v4 argument combines multiscale incidence factorization with planar Furstenberg estimates on branching intervals, including Theorem 5.35 in the intermediate range. These are genuine remaining geometric proofs, not consequences of the native finite bookkeeping.

A self-contained formal proof of WZ A.1 therefore needs either a proof of this finite A.3 statement or an independently proved weaker expansion on the precise shaded tube families constructed in Appendix A. The latter families have the single-scale spacing and shading estimates explicitly derived in (231)–(238), but are not known to satisfy an easier directional-separation or regular-carrier premise. One cannot replace A.3 by the original four-dimensional volume estimate without making the argument circular.

The parameters in that application satisfy s_bar>=gamma0>0, t_bar in [chi/2,2−gamma0], and fixed u_bar>0. A formal caller must prove a uniform choice of the expansion loss for that range, or make a quantitative finite parameter discretization. Mere membership in a compact interval does not imply that an unspecified positive threshold function has a positive infimum.

Before A.3, Lemma A.2 is another feasible elementary geometric target: two thin strips making angle theta have intersection diameter O(width/theta). A maximal family of rich thin strips then has at most O(delta^(−chi)) members by pair counting. Its transverse-overlap points have small mass, and the two-ends hypothesis controls the remaining nearly parallel rich strips. This is a direct finite construction, but it does not replace the subsequent positive-power expansion.

## 7. The additive-combinatorial input and available code

WZ Lemma 13.7 requires a truly asymmetric statement for delta-separated X,Y subset [-1,1], with |Y|<=|X|^C and approximate mixed energy at least nu |X|^2 |Y|. It returns large ORIGINAL subsets X',Y' and controls all fixed iterated sums

    |Y'+nX'−mX'|_delta

by a polynomial loss times |Y|. In the native application X is the popular polarization-value set and Y is A; their cardinalities need not be comparable.

The installed file `LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean` explicitly describes and requires `X.card = Y.card` in `balog_szemeredi_gowers_asymmetric` and its explicit-constant sibling. Its graph theorem has the same equality requirement. It is useful infrastructure, but cannot directly discharge 13.7. Arbitrarily truncating the larger set to equal size can lose a fixed power of the mesh and is not a subpower repair.

A valid extension must derive the unequal-size energy refinement and its iterated-sumset estimate, using actual lattice rounding for the approximate energy and the existing Ruzsa/Pluennecke results where applicable. Claim 13.8 supplies a genuine polynomial lower cardinality for the popular set; it does not make the two sets equal-sized.

For the already audited L-tuple task, `TwoTubePathCollisionCount.square_card_le_image_mul_collisions` is fully generic in the original finite set and label map. It directly handles the final pair-of-one-arm-path collision count. The existing `nat_sum_sq_le_card_mul_sum_sq` and `sum_halfPaths_eq_sum_tubeDegree_sq` supply the two Cauchy ingredients. What must be added is the actual one-arm set grouped by original grain, its exact cardinal identity, and the actual geometric label-image bound. There is no reason to duplicate the collision machinery.

## 8. Concrete next implementation order

1. Prove the raw slope-interval implication preceding (K2), with the nonzero denominator and exact radius range.
2. Prove its dyadic-annulus sum and the deterministic heavy-projection-cell deletion, yielding (K3)–(K5) on original labels. This closes Theorem 13.4 without an imported projection axiom.
3. Instantiate (N1)–(N3) from actual prepared time labels and the bounded dyadic field, including the explicit coarsening fibers. This closes the radial theorem's native uniformity premise.
4. Prove the finite strip-intersection geometry and rich-strip selection of A.2; then tackle the finite positive-power Furstenberg estimate A.3, with all auxiliary families constructed.
5. In parallel, extend the unequal-size additive-energy refinement needed by 13.7 and transport its conclusions through the actual popular-value grid.

Theorem 13.5 remains open until those deep geometric and additive proofs, as well as their actual finite callers, are completed. The original final theorem remains unchanged throughout.
