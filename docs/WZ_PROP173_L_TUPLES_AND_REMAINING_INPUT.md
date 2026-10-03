# Proposition 17.3: exact remaining route, L tuples, and the first new count

Source: Wang–Zakharov, arXiv:2609.22035, printed pp. 83–90, with Theorem 13.5 on pp. 52–55. This note continues the frozen Section 19 box/growth note. It does not assert that Proposition 17.3, the native configuration, or the final compact packing-three theorem has been proved.

## 1. Current mathematical status and dependency order

There is NO remaining Section 19 lemma that alone turns Lemma 19.2 into kappa<=zeta. Lemma 19.2 only excludes sufficiently flat local slope fields when the convex-Wolff constant is small. For the case k=ell=d−1:

* Lemma 19.4 concerns the higher slope; here it is the same field f, so it is not an additional route to the conclusion.
* Lemma 19.5 supplies Lipschitz control of the higher field in general. Here f already has the required dyadic control from Definition 17.2.
* Section 20.4 splits the actual slope field into an approximately affine branch and a non-affine branch.
* The affine branch is Lemma 20.2, pp. 86–87. It uses the V-tuple identity (157), a nondegenerate direction difference, a quadratic time image, and the tube Katz–Tao upper bound.
* The non-affine branch is Lemma 20.3, pp. 88–90. Its input is the L-tuple count, the additive relation (161), actual projection-fiber bounds, and the substantive nonlinear expansion Theorem 13.5. The latter uses the radial/projection results in Section 13 and asymmetric Balog–Szemeredi–Gowers, Lemma 13.7. This dependency is not covered by the existing finite counting and grid modules.

Proposition 17.3 itself is stated for a (d−1)-linear configuration. Section 20 starts with the planar condition as well. In this codimension-one case it follows from the one-dimensional Y_z AD upper bound: if kappa<=zeta there is nothing to prove; otherwise weaken the directional exponent to gamma_star=min(gamma,zeta/2). Then gamma_star<=kappa, so the inherited tube exponent 1−kappa is at most 1−gamma_star. This supplies the planar KT clause with recorded constants. The later hierarchy must use gamma_star, not silently retain a possibly larger original gamma.

Thus Proposition 17.3 remains open in the current audit. The complete Section 20.2/20.3 proof and its Theorem 13.5 dependency have not been certified here. Sections 2–5 below prove a small concrete next construction and spell out the affine geometric count; Section 6 identifies the remaining nonlinear obligations.

## 2. A complete finite one-arm count for Lemma 20.1

Let P,T be finite sets of distinct geometric points and tubes, with actual incidence relation I. Write P=|P|, T=|T|, I=|I| when no confusion results. Give every point an original grain label g(p), including its height. Suppose every occupied grain class in the localized point set has at least G points. Let Z be the set of actual heights.

A one-arm path is the original labelled tuple

    (p,p',p_tilde',p'',T1,T2)

with p--T1--p', p' and p_tilde' in the same original grain, and p_tilde'--T2--p''. Repetitions are allowed. Put

    h(p') = sum_(T incident to p') degree(T).

Then the exact identity and Cauchy bounds are

    J = sum_(occupied grains A) [sum_(p' in A) h(p')]^2,
    sum_p h(p) = sum_T degree(T)^2 >= I^2/T,
    #occupied grains <= P/G,
    J >= G I^4/(P T^2).                                  (J1)

No per-tube lower shading degree is used. If I>=mu P and I>=lambda |Z| T, then

    J >= G mu^2 lambda^2 P |Z|^2.                         (J2)

The original grain population G inside the SAME spatial rho-cube must be derived. It does not follow from restricting an arbitrary globally dense grain to a cube. The existing preparation can append the fixed label (original grain, rho-spatial cell), separately at each original height. A full grain has at least K^(−1)delta^(−a) points, a=k−1, and meets at most C_d rho^(−a) spatial rho-cells. The reference class count is consequently at most C_d K |E_z| (delta/rho)^a. One same-set partition refinement gives

    G >= K^(−C)(rho/delta)^a

in every occupied final grain-cell, with the same cost bound at every height. Spatial and grain partitions are included in that single call, and all incident tube fibers at retained points are kept. Taking the union over disjoint height sets does not multiply the retention cost by the number of heights.

## 3. The actual geometric label menu and L collisions

Use the k-linear coordinates p=(x,y+F(z)x,z), with x in R^a and y in R^(d−k). Assume the actual incident direction at p is (u,xi_p+F(z)u)+O(delta). Let delta<=tau<=rho and suppose the source's small-variation hypothesis holds:

    ||(F(z)−F(z'))u|| <= c tau/rho

for the actual initial direction witnesses, allowing the fixed O(delta) conversion from Phi_p if necessary.

For the first arm p--T1--p' at heights z,z', let t=z'−z. Direct subtraction of the physical incidence equations gives

    y(p') = y(p)+t xi_p+t(F(z)−F(z'))u+O(delta).            (J3)

Therefore, for fixed p,z', every possible grain label y(p') lies in one O(tau) normal box. The jump point p_tilde' has the same grain label. After additionally fixing its deterministic half-open tangential tau-cell, all possible jump points lie in one O(tau) PHYSICAL box, since F(z') is bounded.

The common direction menu for a spatial tau-box gives at most K_tau tau^(−kappa) terminal angular tau-cells there. A bounded enlargement meets only C_d adjacent grid cells; if tau is not a stated working scale, retain the factor from refinement of the next working ancestor, as in the Section 19 note. The number of tangential tau-cells meeting the rho-cube is at most C_d(rho/tau)^a.

Label each original one-arm path by

    (initial point, middle height, terminal height,
     jump-point tangential tau-cell, terminal angular c_d tau-cell).

There are at most

    N_label <= C_d K_tau P |Z|^2 (rho/tau)^a tau^(−kappa)  (J4)

labels. The small angular grid factor makes two terminal slopes in one label at distance at most tau. Pairing two paths with the same label gives an actual source L-tuple. The label is recoverable from the original paths, so there is no multiplicity loss from the source's overlapping-neighborhood notation for x_tilde. All original points and tubes remain in the tuple.

Cauchy–Schwarz now gives the closed finite lower bound

    L >= J^2/N_label
      >= G^2 I^8 tau^kappa (tau/rho)^a
             /[C_d K_tau P^3 T^4 |Z|^2],                 (J5)

or, using mu and lambda,

    L >= (C_d K_tau)^(−1) G^2 mu^4 lambda^4
                     P |Z|^2 tau^kappa (tau/rho)^a.

Substituting G>=K^(−C)(rho/delta)^a and mu>=K^(−C)delta^(−kappa) yields precisely the lower bound of Lemma 20.1:

    L >= K^(−C) P delta^(−4kappa) tau^kappa
                     (rho/delta)^a (tau/delta)^a |Z|^2.

An upper bound of the same scale follows by direct choices with the corresponding upper populations and angular fibers, but the lower bound is the part used for the later dense additive graph. The proof above replaces the manuscript's omitted “on average” intersections by one exact path identity and one actual finite label map.

The additive relation (161) also follows directly. If the two initial arms have direction coordinates u1,u2, their intermediate grain labels satisfy

    y1'−y2' = (z'−z)(F(z)−F(z'))(u1−u2)+O(delta).

The grain jumps preserve y1',y2'. Their tangential jump coordinates differ by O(tau), and the terminal directions differ by at most tau. Subtracting the two last legs and then applying the shear F(z'') gives

    y1''−y2'' = (z'−z)(F(z)−F(z'))(u1−u2)
                  +O(tau ||F(z')−F(z'')||+tau rho+delta).

Thus the error is O(tau rho+delta) under the required dyadic slope control. The two jump points need not lie on the same original grain.

## 4. Exact L-tuple projection fibers for equation (164)

Fix a terminal height z''. Put G_rho=C_d(rho/delta)^a and G_tau=C_d(tau/delta)^a for UPPER point capacities in one actual grain segment. Let D bound all incident tubes at a point, and let U_rho,U_tau bound its angular fibers. Fix the projected data

    (terminal normal label y1'', z,z', coarse initial u1, coarse initial u2).

The number of original L-tuples above this label is at most

    C_d G_rho^2 G_tau D U_rho^2 U_tau.                    (J6)

Indeed choose p1'' in its fixed grain (G_rho), T1' (D), its jump point at z' (C0), the first intermediate point in that grain (G_rho), T1 in the fixed rho-angular cell (U_rho), its point p at z (C0), T2 in the other fixed rho-cell (U_rho), its intermediate point (C0), the second jump point in the same original grain and within O(tau) tangentially of the first jump point (G_tau), T2' in the tau-angular neighborhood of T1' (U_tau), and its terminal point (C0).

Combining (J6) with (J5), the actual lower original grain population at z'', and a weighted choice of z'', gives the advertised graph density

    #G >= K^(−C) #Y_(z'') |Z|^2 m_rho^2.

The scale cancellation is literal: D U_rho^2 U_tau has size rho^(2kappa)tau^kappa delta^(−4kappa), while the numerator supplies tau^kappa delta^(−4kappa).

The source later asserts symmetry in z,z' for this projected graph. An arbitrary image of L-tuples does not automatically have that symmetry. When the later argument only uses the additive containment, replace it by the ACTUAL geometric relation

    G_geom = {(y,z,z',phi1,phi2):
       dist(y+(z'−z)(F(z')−F(z))(phi1−phi2),Y_(z''))
          <= C tau rho }.

This contains the witness image and is symmetric in z,z', because the product is unchanged when both differences change signs. It uses an actual target point of Y, not a new tube-incidence assertion. Its greater cardinality preserves the lower density and the same additive upper-cover conclusion. Do not label the added geometric edges as original L-tuples.

## 5. The affine branch: precise use of Lemma 19.2 and a quadratic estimate

The affine branch in Section 20.4 finds models

    ||F(z)−r_I z−u_I|| <= rho^(1+epsilon0)

on a globally dense selected height set. The printed transition to Lemma 20.2 suppresses important powers. The usable implication is

    ||r_I|| >= rho^(epsilon0/2)
      ==> rho^(1+epsilon0)
              <= rho^(1+epsilon0/2)||r_I||.               (A1)

If instead ||r_I||<=rho^(epsilon0/2), the model varies by at most C rho^(1+epsilon0/2) in I. The flat-slope conclusion of Lemma 19.2, applied to this globally dense subset, gives

    C_CW(T) >= delta^[C_d(eta/gamma+epsilon)]
                        rho^(−kappa epsilon0/2).

For rho=delta^mu and kappa>=zeta, this contradicts C_CW(T)<=delta^(−eta) if

    C_d(eta/gamma+epsilon)+eta < mu zeta epsilon0/2

with a fixed margin. Thus a dense set of intervals must have the lower slope size required in (A1). To use a prescribed dense height subset without putting epsilon into the transversality constant, prepare spatial/grain partitions separately at each original height, retain all incidence fibers there, and only then take that height subset. This is a valid stronger caller of the Section 19 proof. A single global point refinement could miss a prescribed sparse height subset.

The source also prints a local height count delta^eta(delta/rho) in Section 20.4. The required and dimensionally consistent count is delta^eta(rho/delta). A globally small total affine-model population must be converted to a local upper bound by discarding intervals according to their relative model population; a bound involving the GLOBAL |Z| in every interval is not (163).

For completeness, the actual new geometry of Lemma 20.2 can be isolated as follows. Let Z0 be delta-separated in an interval of length rho, and let J subset Z0 have M>=lambda rho/delta elements. Fix z_* and a nonzero vector v. Suppose each z in J has an actual Y witness within E Delta of

    y0+(z−z_*)^2 v.

If M>=4, delete |z−z_*|<lambda rho/8 and keep the heavier side of z_*. At least M/4 elements remain, all at distance at least a rho from z_*, where a=lambda/8. On that one side,

    |(z−z_*)^2−(w−z_*)^2| >= 2a rho |z−w|.

Choose a coordinate of v of magnitude ||v||_infinity. If two actual Y witnesses occupy the same Delta-cell in that coordinate, then

    2a rho ||v||_infinity |z−w| <= (1+2E)Delta.

Since the ORIGINAL times are delta-separated, each output cell has at most

    1+(1+2E)Delta/[2a rho ||v||_infinity delta]

preimages. This proves an explicit lower bound for the number of actual Y cells, with no filled-interval or continuity assumption. In the range Delta>=rho ||v||_infinity delta it gives

    #Y_in_tube at Delta >= c_E lambda^2 rho^2 ||v||/Delta. (A2)

The witnesses lie in a C_E Delta-neighborhood of a line segment of length O(rho^2||v||). A tube Katz–Tao upper bound K(T/Delta)^(1−gamma), with T=C rho^2||r|| and ||v||>=h||r||, therefore yields

    (T/Delta)^gamma <= C_E K/(lambda^2 h).                (A3)

For the source's affine model one has Delta=C rho^(2+epsilon0)||r|| after retaining the explicit incidence errors. This uses rho>=delta^(1/4), ||r||>=rho, and 0<epsilon0<=1 to absorb delta and rho^3||r||. Thus T/Delta is comparable to rho^(−epsilon0). Equation (A3) is the actual contradiction when the loss parameters are small compared with mu epsilon0 gamma.

The vector v can be obtained using fine-point Frostman, without declaring the coarse union Phi_q Frostman. Fix a rich V-tuple endpoint p1. The ambient upper number of V-tuples there is C0^2 D^2 |Z|. For fixed first tube, height, and common initial point p, fine-point Frostman removes the second tubes with ||r(u1−u2)||<=h||r|| at a cost at most C F h^gamma of that upper count. Choose h to beat the actual V lower/upper ratio. Projection to (z,coarse u1,coarse u2) has fiber at most C0^2 U_rho^2. Pigeonholing then fixes an actual nondegenerate coarse direction pair and a dense time set. The coarse approximation preserves ||v||>=c h||r|| provided rho is sufficiently smaller than h; the required hierarchy eta/gamma<<mu ensures this.

This isolates a rigorous finite geometric estimate suitable for formalization, but it is not a certification of every native caller in Lemma 20.2. In particular, if the maximizing affine r_I is not a priori bounded, retain its actual bound. A locally dense model set and dyadic Lipschitz F give ||r_I||<=delta^(−O(eta+epsilon)) by comparing two separated model times. One must check the resulting tube length T<=1, or use the corresponding bounded subdivision; one cannot silently interpret an arbitrary maximizing vector as an entrywise bounded matrix.

## 6. The remaining nonlinear input and precise unresolved interfaces

For Proposition 17.3, the non-affine branch is indispensable. Lemma 20.3 normalizes a dense graph to

    a + (b'−b)(F(b')−F(b))(phi1−phi2),

whose rho-covering number is at most a small-loss multiple of |A|_rho; see (164)–(166). For a suitably non-affine scalar projection of F, it invokes Theorem 13.5 with beta=1 and C={1}. The conclusion |A|_rho>=rho^(−1+zeta/2), compared with the inherited upper exponent 1−kappa, gives kappa<=zeta.

Theorem 13.5 is an actual nonlinear expansion theorem, not a restatement of AD regularity or one of the existing finite grid lemmas. Its hypotheses include a mesh-separated time set with a normalized nonconcentration bound, a genuinely non-affine scalar function on that set, a dense graph, and a small additive-image cover. Its proof on pp. 52–55 uses Theorems 13.2 and 13.4 and Lemma 13.7. None has been replaced here by an assumption on the desired output.

Before claiming the Lemma 20.3 caller, the following actual interfaces still need checking:

1. The source again asserts coarse Phi_q slab Frostman. It needs either a proof from actual reference data or a witness-level repair. A possible constructive repair is to refine the actual L-tuple set by its projected graph-edge label before discarding fibers. Its total mass and the menu upper bound make every occupied graph-edge fiber a controlled fraction of the upper scale (J6). Fine-point slab estimates on original L witnesses can then be converted to upper counts of bad projected edges. This must be proved on the same final witness set; the raw upper fiber bound alone cannot transfer a slab upper bound to the image.
2. The actual A and B after rescaling initially live at finer mesh than rho. Theorem 13.5 requires rho-separated sets. Their grid image, representative choice, function approximation, and dense-graph fiber counts must be supplied. The time function's dyadic Lipschitz control at the physical rho^2 scale, with the actual working-scale gap, is precisely what can keep the new F error O(rho) when tau is chosen large enough.
3. An arbitrary interval cut of Y need not inherit lower AD. For the additive theorem only a cover upper bound on A is necessary, but graph density after coarsening needs a correct denominator. Use actual full reference Y neighborhoods and bounded-overlap net patches, or prepare their class populations before selection; do not assert lower AD of a truncated Y(q) for free.
4. In the scalar-projection dichotomy on p. 89, the set on which Theorem 13.5 is applied must be the rich induced time set B(phi1,phi2) satisfying non-affine concentration bounds. The displayed B_(phi1,phi2) is defined as a maximal approximately affine subset, so applying the nonlinear theorem to that subset literally would contradict its hypothesis. Keep the two sets distinct and apply the theorem to the former.
5. Choosing several scalar projections with a common large time set requires a genuine transverse-pair counting argument, with determinant loss included. A cardinally large subset of an arbitrary coarse angular union is not enough.

The nonlinear expansion theorem and these interfaces are the first remaining substantial obstacles to a complete Proposition 17.3 proof. The finite L-tuple construction above is a concrete prerequisite that can be formalized in parallel. It does not close the nonlinear branch or the final finite-volume contradiction.

Sanity checks: 600 finite incidence/partition examples verified the exact one-arm lower inequality, and 600 exact-rational quadratic-image examples verified the stated same-cell fiber bound, including negative slopes and nonuniform time sets. These are checks of the handwritten formulas, not Lean proof claims.
