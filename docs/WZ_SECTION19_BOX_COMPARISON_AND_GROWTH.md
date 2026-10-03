# Section 19: actual W geometry and a quantitative route through Lemma 19.2

This is a source-level mathematical derivation, not a claim that the native configuration or this entire lemma has been formalized. The original compact packing-three theorem is unchanged. The argument belongs to the universal auxiliary finite-volume route; it does not pay the original manuscript's old occurrence/root charge.

Primary source: Wang–Zakharov, arXiv:2609.22035, downloaded PDF and text in `/workspace/shared/sticky-paper-audit/`. Relevant printed pages are 77–80: Lemma 19.1 and W tuples, equations (148)–(153), Lemma 19.2, Claim 19.3, and the transverse-neighborhood argument on p. 80. Definition 17.2 is on p. 65, Definition 17.4 on p. 66, and the bounded graph-tube model is equation (19), p. 16.

## 1. The exact next source result

After the proved two-tube walk/collision count, the first new geometric estimate is **Claim 19.3**, inside **Lemma 19.2**. If two terminal tubes occur in an actual W tuple, and the three relevant slope matrices differ by O(sigma), their anisotropic neighborhoods of transverse width sigma and tangential width rho are comparable. The source assumes

    delta^(1/3) <= rho <= 1,       rho^2 <= sigma <= rho.

The elementary comparison itself only requires delta <= sigma <= rho <= 1, plus the quantitative incidence errors below. It does not need slab Frostman, tube Katz–Tao, higher grains, AD regularity, or a nonzero time gap. The power range implies delta <= rho^2 and delta <= sigma for later counting.

Lemma 19.2 uses the global grains representation, incident direction graphs, fine-point slab Frostman, actual direction and tube counts, and actual dense time sets. It does not use the higher planar slope or its tube Katz–Tao axiom. Its conclusion is

    C_CW(T) >= delta^[C_d(eta/gamma + epsilon)] (rho/sigma)^kappa,

up to fixed dimensional constants. Sections 4–8 below make two implicit parts of its proof explicit: a rich W core and the passage to transverse directions. In particular, no upper slab law on a coarse union is silently assumed.

## 2. A closed finite form of Claim 19.3

Work in product maximum norms on R^a x R^b x R, with a = ell−1 and b = d−ell. Let F0,F1,F2 : R^a -> R^b be linear maps and let

    ||F2|| <= A,
    max_(i,j) ||Fi−Fj|| <= S,
    ||u_i|| <= B,                  i=1,2.

All operator norms here are from maximum norm to maximum norm. An entrywise matrix bound gives an extra factor a. The source's slope cluster gives S <= C_d sigma.

There are heights z0,z1,z2 in one interval of length rho, a common starting point p, intermediate points p_i, terminal points p_i', initial slopes (u_i,v_i), terminal slopes (u_i',v_i'), and offsets xi,xi_i. Put e = E delta. Assume the actual shared-point direction equations

    ||v_i − xi − F0 u_i|| <= e,
    ||v_i − xi_i − F1 u_i|| <= e,
    ||v_i' − xi_i − F1 u_i'|| <= e.

Assume actual graph incidence along both legs, with maximum-norm horizontal error at most e:

    p_i,h = p_h + (z1−z0)(u_i,v_i) + r_i,
    p_i',h = p_i,h + (z2−z1)(u_i',v_i') + s_i,
    ||r_i||, ||s_i|| <= e.

Finally assume ||u_2'−u_1'|| <= rho. The W definition's full terminal direction gap implies this. Write

    du = u_2'−u_1',    dv = v_2'−v_1',
    dx = x_2'−x_1',    dy = yphysical_2'−yphysical_1'.

Then the following three explicit inequalities hold:

    ||dv−F2 du|| <= (2B+rho)S + 6e,                         (C1)
    ||dx|| <= 2B rho + rho^2 + 4e,                         (C2)
    ||dy−F2 dx|| <= (4B+rho)rho S
                       + [8rho+4(1+A)]e.                 (C3)

Proof: the first two direction equations give

    xi_i = xi + (F0−F1)u_i + error of size <=2e.

Subtract the terminal equations and then F2 du to obtain

    dv−F2 du = (F0−F1)(u_2−u_1) + (F1−F2)du
                   + error of size <=6e,

which proves (C1). Write t=z1−z0 and s=z2−z1. Subtracting the two physical paths gives

    dx = t(u_2−u_1) + s du + error of size <=4e,

which proves (C2). The initial normal difference is F0(u_2−u_1) plus an error of size <=2e. Consequently

    dy−F2 dx = t(F0−F2)(u_2−u_1)
                   + s(dv−F2 du)
                   + error of size <=2rho e+4(1+A)e.

Substitute (C1), use |t|,|s|<=rho, and obtain (C3).

Thus the terminal direction normal gap is O(sigma), the terminal base-point tangential gap is O(rho), and its normal gap is O(rho sigma+delta). This last bound is sharper than treating the complete point error in equation (150) as O(rho^2); the cancellation in (C3) is important when comparing thin normal directions.

For a terminal point p_i'=(x_i',y_i',z2), define the explicit adapted box

    B_i(L) = { (x,y,t) : |t−z2|<=L,
        ||x−x_i'−(t−z2)u_i'|| <= L rho,
        ||y−y_i'−(t−z2)v_i'
               −F2[x−x_i'−(t−z2)u_i']|| <= L sigma }.

Suppose S<=S0 sigma, delta<=sigma, and E,A,B,S0 are bounded fixed constants. Set

    P_x = 2B+1+4E,
    P_n = (4B+1)S0 + (12+4A)E,
    D_n = (2B+1)S0 + 6E,
    C = max(1, 2+P_x, 1+P_n+D_n).

For every L>=1, direct subtraction of the defining residuals proves

    B_1(L) subset B_2(C L),    B_2(L) subset B_1(C L).       (C4)

Indeed the tangential residual increases by at most P_x rho+L rho, and the normal residual by at most P_n sigma+L D_n sigma. The affine map from residual coordinates to physical coordinates is triangular with determinant one. Hence

    volume(B_i(L)) = (2L)^d rho^a sigma^b.                 (C5)

A standard graph delta-tube incident to p_i' lies in B_i(L0), where L0 depends only on A,E and the bounded common time slab. Conversely the source box

    U(z2,T_i') = N_sigma(T_i') + {(w,F2 w,0): ||w||<=rho}

and B_i(L0) contain fixed dilates of one another, additionally using a fixed bound on the FULL terminal slopes and the common time slab. The native graph-tube model provides that full slope bound; it is not needed for (C1)–(C4) themselves. Euclidean and maximum neighborhoods cost dimensional constants. This proves the source's mutual containment claim. If all original incidence error constants are fixed dimensional constants, C is dimensional as claimed. If a caller leaves an error parameter E growing with the mesh, its contribution cannot be erased.

The same calculation gives a formalization target consisting entirely of vector equalities, norm inequalities, and membership in an explicit affine box. It has no abstract concentration premise.

## 3. Literal configuration inputs needed by the later count

Use distinct geometric points, tube labels, and point–tube incidences. Repeated original metadata remain attached, but do not multiply the number of geometric W tuples. The following quantitative quantities must be obtained from the actual configuration:

* C0: maximum number of separated points in a tube at one fixed height. Bounded graph tubes and delta-separated points give a fixed dimensional C0.
* D: upper bound for the number of incident tubes at a point, with a comparable lower bound d. The directional kappa-AD set and bounded tube-per-direction-cell multiplicity give D,d comparable to delta^(−kappa) up to the recorded loss.
* U: upper bound for incident tubes whose first a slope coordinates lie in one fixed C rho-box; U <= K (rho/delta)^kappa.
* m: number of coarse tangential direction cells available in the spatial rho-cube q; m <= K_q rho^(−kappa). These are actual projected slope-cell labels, not new line directions.
* Fine point slab law on actual tube labels: for every point p, unit normal n, offset c, and r>=delta,

      #{T incident to p: |n·u(T)−c|<=r} <= F r^gamma D.

  It follows from Definition 17.4(3), the actual O(delta) direction graph, and bounded multiplicity of fine direction labels. If the original Phi_p is used instead, record these bounded fibers. At widths exceeding one the trivial D bound suffices.

No lower directional population is transported through a later arbitrary tube restriction here. All upper estimates use the full prepared reference configuration; actual retained W witnesses are a subset of that reference.

## 4. Keep epsilon out of the transversality loss

There is a useful exact way to localize the source's assumption (154). A naive heaviest spatial cube after a height cut can put epsilon into the W density parameter, producing an avoidable epsilon/gamma loss. The following ordering avoids it.

First, on the original configuration, refine POINTS using the partition

    p -> (its original height, its original spatial rho-cell).

Keep all original incidence fibers at the selected points. The number of reference classes is at most

    C K delta^(−1) rho^(−(d−1−kappa)).

The original point population is at least K^(−C)delta^(−(d−kappa)). The existing self-uniform partition constructor therefore gives a subset, at a delta^[O(eta)] cost, in which every occupied slice-cell contains at least

    delta^[O(eta)] (rho/delta)^(d−1−kappa)                 (L1)

points. Its upper population is inherited from the reference slice counts. This is a single finite partition at this chosen rho; it does not require a new all-scale uniformity assertion. The direction sets remain whole at every retained point.

For each original rho-time interval I, choose a maximal subset with pairwise matrix distances strictly greater than 2sigma of the finite matrix set {f(z):z in Z∩I}. The sigma-balls about its centers are disjoint. Assumption (154) says each contains at least delta^epsilon |Z∩I| original heights. Therefore there are at most delta^(−epsilon) centers. The 2sigma-balls cover all original heights. Choose the heaviest such cluster using the already prepared POINT mass, retaining at least a delta^epsilon fraction of that mass in I. Its pairwise matrix variation is at most 4sigma.

This cut retains entire original-height classes, so it retains every prepared (height,q) class wholly. Thus (L1) survives with no epsilon in its constant.

The reference grains, coarse Y-union counts, bounded f, and its dyadic rho-continuity give at most

    C K^C rho^(−(d−kappa))

occupied spatial rho-cubes globally. This is a cover count: in each rho-time interval, cover the actual coarse union of Y_z at rho, then cover the bounded x-domain by rho-cubes; bounded shear and rho-variation add a fixed dimensional factor. A heaviest q after the preceding cut therefore has

    |E(q)| >= delta^[O(eta)+epsilon] (rho/delta)^(d−kappa).

Using the per-height upper bound and (L1), its ACTUAL occupied time set Z_q satisfies

    |Z_q| >= delta^[O(eta)+epsilon] rho/delta,
    |E(q)| comparable to |Z_q|(rho/delta)^(d−1−kappa),      (L2)

where the comparability loss in the second statement involves eta only. All its heights have the required O(sigma) matrix variation.

Since Z_q is delta-separated, any interval of length rho^2 contains at most

    H <= C rho^2/delta

heights (rho^2>=delta). Consequently

    |Z_q|/H >= delta^[O(eta)+epsilon] rho^(−1).            (L3)

The source writes Z(q) first for occupied local times and later for all slope-good global times. The construction above uses the actual occupied local set throughout and proves the required time-density estimate.

The localization also makes the count (146) explicit. The common coarse angular menu and carrier upper bound yield

    |T(q)| <= K^C rho^(−kappa)(rho/delta)^(d−1).

Together with (L2) and d>=K^(−C)delta^(−kappa), this gives I>=K^(−C)|Z_q||T(q)|. The already proved two-walk collision theorem applies with no per-tube lower degree.

## 5. Rich terminal pairs from the actual W lower bound

Let V be the actual terminal pairs v=(z'',T') for which T' has an incident point in E(q) at z''. An actual W tuple has an ordered left endpoint v and right endpoint w, and swapping the two branches is an involution. Loops and repeated points/tubes remain allowed.

Put

    B_W = C0^5 D^2 U |Z_q|^2.

There are at most B_W W witnesses at any one left endpoint. To see this, fix v=(z'',T1'). Choose its terminal point p1' and its intermediate point p1 at height z' (at most C0^2 choices), T1 at p1 (at most D), its starting point p at height z (at most C0), T2 at p (at most D), its point p2 at z' (at most C0), T2' at p2 with terminal slope within rho of T1' (at most U), and its terminal point p2' (at most C0). Sum over z,z' in Z_q.

The collision lower bound and the actual local estimates give

    W_total >= alpha |V| B_W,       alpha=delta^[O(eta)].   (R1)

To check the scale cancellation, B_W has size

    K^C |Z_q|^2 rho^kappa delta^(−3kappa),

whereas W_total is at least

    K^(−C)|E(q)|delta^(−4kappa)rho^kappa|Z_q|^2.

The ratio is controlled by |E(q)|delta^(−kappa)/(|Z_q||T(q)|), which has only eta loss by (L2). This is why the earlier per-height preparation matters.

Construct a core by repeatedly deleting any vertex whose number of currently surviving outgoing W witnesses is below alpha B_W/4. Deleting a vertex destroys at most twice that many ordered W witnesses, by the branch-swap involution. Over at most |V| deletions fewer than W_total/2 witnesses are destroyed. Hence a nonempty core remains, containing at least W_total/2 original W witnesses, and every core vertex has at least alpha B_W/4 outgoing witnesses to another core vertex.

This gives the precise persistent richness needed for neighborhood iteration. Merely retaining vertices that were initially rich does not prove that their witness partners remain rich.

## 6. Pointwise Frostman gives escaping menus, without coarse-union Frostman

Definition 17.4(3) explicitly imposes slab Frostman on each fine Phi_p. The proof on p. 80 says the common coarse Phi_q is slab Frostman. Inclusion Phi_p subset Phi_q^(rho), plus kappa-AD counts, is not by itself a general upper-bound transfer to the whole union. The following original-witness argument supplies exactly the property the iteration needs.

Fix a core terminal vertex and any proper linear subspace V0 of R^a. For every fixed first branch and times, T2 is incident to the SAME starting point as T1. Thus the fine-point slab law bounds choices with

    dist(u(T2)−u(T1), V0) <= r

by at most C F r^gamma D. Repeating the preceding ambient count gives

    number of such bad W witnesses <= C F r^gamma B_W.     (R2)

This upper bound is on the full reference choices. It is compared to the actual retained lower threshold alpha B_W/4; no conditional uniformity of the selected W family is asserted.

Give every actual tangential slope its deterministic half-open rho-grid label, using a fixed sufficiently small dimensional grid factor. The coarse label differs from its actual slope by at most C_d rho. Choose

    h = C_d^(−1) [alpha/(C_d F)]^(1/gamma)

with the dimensional denominator inside the 1/gamma power large enough that C F (C_d h)^gamma <= alpha/8. Its fixed dependence on gamma is retained until delta is chosen; a gamma-independent small factor outside the power alone would not suffice. If rho<=c_d h, a coarse difference within h of V0 has actual difference within C_d h. Equations (R1)–(R2) leave at least alpha B_W/8 W witnesses whose COARSE difference is at distance at least h from V0.

For a fixed endpoint v and coarse menu

    g=(z,z', coarse u(T1), coarse u(T2)),

the actual W fiber has size at most

    L_W = C0^5 U^3.                                      (R3)

Indeed T1 is now in one rho-angular fiber at p1, T2 in one such fiber at p, and T2' in the rho-neighborhood of the fixed terminal direction. The five point-at-height choices are unchanged. This estimate retains all original tube and point labels.

It follows that at every core vertex, for every proper V0, at least

    alpha B_W/(8L_W)
      >= beta |Z_q|^2 m^2,       beta=K^(−C)alpha           (R4)

coarse menus have difference escaping V0. The last inequality uses the actual bounds D/U and m<=K_q rho^(−kappa), retaining their K factors. Choose one original W witness and partner for each menu. This is a finite choice from genuine witnesses; the coarse labels are used only for counting and approximate displacement.

If rho>c_d h, the eventual lower bound in (G1) below is at most a dimensional constant and follows from nonemptiness after reducing its fixed prefactor. This handles the coarse endpoint without asking a rho-grid to resolve transversality below rho.

## 7. A complete finite transverse-growth lemma

Here is the exact combinatorial/geometric statement used in the source's phrase “using this information and some pigeonholing.” Let a>=1 be fixed. Suppose:

* A nonempty finite graph of original terminal vertices, all at the same terminal height, has coordinates x(v) in a bounded rho-cube in R^a.
* Z is a finite time set in a rho-interval; every rho^2-interval contains at most H elements.
* A finite coarse angular alphabet has m elements, each represented by its actual grid coordinate in a fixed bounded set.
* For every vertex v and proper subspace V0, at least beta |Z|^2 m^2 menus (z,z',phi1,phi2) have dist(phi2−phi1,V0)>=h and have an actual neighboring vertex w such that

      ||x(w)−x(v)−(z'−z)(phi2−phi1)|| <= E0 rho^2.

Then the rho^2-covering number of vertices at graph distance at most a from any starting vertex is at least

    C_growth^(−a) beta^a h^(a^2) (|Z|/H)^a.              (G1)

Here, if each coordinate of every difference vector has absolute value at most V_bound, one may take

    C_growth = 2 a! V_bound^(a−1)(1+2a E0) + 2,

provided 0<h<=1. This is an explicit fixed dimensional constant in the source normalization.

Proof. Construct a depth-a tree of menus. At step i exclude the span of the previously chosen difference vectors. There are at least beta |Z|^2 m^2 children at every node. For every branch the resulting difference vectors v_1,...,v_a obey

    dist(v_i, span(v_1,...,v_(i−1))) >= h,
    |det(v_1,...,v_a)| >= h^a.

Fixing all a ordered angular pairs by averaging leaves at least beta^a |Z|^(2a) distinct ordered time-pair sequences. The choice of one witness and partner per menu makes the tree a deterministic function of its menu sequence, so these are distinct time sequences, with no additional path multiplicity denominator.

For such a sequence the endpoint satisfies

    x_end = x_start + sum_i (z_i'−z_i)v_i + error,
    ||error|| <= a E0 rho^2.

If two endpoints lie in one rho^2-grid cell, their two coefficient vectors differ by at most C_(a,E0)h^(−a)rho^2 in each coordinate. This follows from the adjugate formula: every inverse-matrix row has absolute row sum at most a! V_bound^(a−1)h^(−a), and the physical output plus two path errors is at most (1+2a E0)rho^2. Fixing z_1,...,z_a leaves at most

    [C_(a,E0)h^(−a) H]^a

choices for z_1',...,z_a' in such a coefficient box. Thus one endpoint cell receives at most

    |Z|^a [C_(a,E0)h^(−a)H]^a

time sequences. Divide the retained sequence count by this bound to prove (G1).

For the actual W graph, choose one genuine incident point at the terminal height for each vertex. Any other such point is within C_d delta, so changing to these fixed representatives adds O(delta). Equation (150), terminal angular closeness, and replacing the two initial slopes by their rho-labels give the required displacement with fixed E0, because delta<=rho^2. No arbitrary nonincident point or tube direction is introduced.

Applying (L3), (R4), and h bounded below by a fixed gamma-dependent constant times delta^[O(eta/gamma)] gives

    |X_a|_(rho^2) >= delta^[O(eta/gamma+epsilon)] rho^(−a).

For d=4 the depth is a=ell−1 in {1,2}; it is fixed independently of delta and eta. The graph paths are made of genuine W relations, so Claim 19.3 puts all their terminal tubes in C_d^a times the starting adapted box.

## 8. The last count in Lemma 19.2

Let Q denote the loss factor in (G1), so |X_a|_(rho^2)>=Q rho^(−a). Take a maximal sigma-separated subset of the ACTUAL terminal x-coordinates. Since one sigma-ball contains at most C_d(sigma/rho^2)^a rho^2-cells, its cardinal n obeys

    n >= c_d Q (rho/sigma)^a.

At each chosen terminal point p_i, use the full fine kappa-AD direction set within rho of its incident terminal tube. Its rho-ball population, divided by the maximal population in one sigma-angular cell, supplies at least

    K^(−C)(rho/sigma)^kappa

distinct actual sigma-angular cells, each with an original incident tube witness. Their graph directions differ from the terminal tube tangentially by O(rho) and normally by O(delta) relative to F(z), so these tubes, and their bounded-slab sigma ancestors, lie in a fixed dilation of the same adapted box.

A single sigma-tube intersects the fixed height in a set of tangential diameter O(sigma), so it can be counted for only C_d of the sigma-separated chosen points. Thus

    #T_sigma[C_d U] >= c_d Q K^(−C)(rho/sigma)^(a+kappa).

Its convex box has volume comparable to rho^a sigma^b. The carrier AD fiber lower bound gives at least K^(−1)(sigma/delta)^(d−1) original fine tubes beneath each sigma ancestor, and the global fine tube count is at most K delta^(−(d−1)). Summing the disjoint ancestor fibers directly yields

    C_CW(T) >= c_d Q K^(−C)(rho/sigma)^kappa.

This does not require declaring a new convex-Wolff certificate for the thickened family. It uses actual ancestor fibers and their geometric containment. Standard tubes may first be represented by the bounded dyadic parameter grid with the already accounted fixed factors.

## 9. Quantifier order, unassembled prerequisites, and formal targets

The complete native Definition 17.2/17.4 configuration is still an unassembled prerequisite. This note is parallel dependency work toward the finite-volume contradiction, not a proof that the original compact input already has all these properties.

The local uniformity call has fixed relation count. Its desired loss exponent is fixed first, and the actual cardinal upper bound and finite height/spatial label menu supply its parameters as in the earlier alignment parameter checklist. The call is BEFORE the slope-height cluster cut; the latter is a union of whole height classes. No post hoc point or tube thinning is claimed to preserve lower populations.

For literal scale interfaces, take rho and sigma on the dyadic grid. Definition 17.2 supplies its common-cell data only on its stated working scales. If rho is not one of them, let rho_plus be the least available dyadic working ancestor and retain G=rho_plus/rho explicitly. Refining its common angular menu and its occupied spatial boxes to rho costs at most G^(C_d); the fine-point slab and AD bounds remain the original ones. Its time interval contains the smaller dyadic interval by nesting. Thus this note uses K_eff=K^C G^(C_d), rather than asserting an all-scale common field for free. When the working schedule gives G<=delta^(−c eta), this is still delta^(−O(eta)). Sigma-ancestor counting uses the actual dyadic parameter grid and fine AD bounds. Arbitrary real scales can be rounded with fixed-factor coverings only after recording the corresponding original interval labels.

The geometric constants in Claim 19.3 and E0 are fixed before the mesh. Given gamma>0 and a desired contradiction exponent, choose eta sufficiently small relative to gamma and that exponent; choose epsilon separately small. Then take delta small enough to absorb all fixed constants. If rho/sigma>=delta^(−r), the Wolff lower bound contradicts C_CW(T)<=delta^(−eta) once

    r kappa > C_d eta/gamma + C_d epsilon + eta

with a strict margin. The source's Proposition 17.2 quantifiers allow these choices once its native construction has been completed. The fixed iteration depth a does not require an eta-dependent scale tower.

Section 19.1 introduces rho>=delta^(1/4), whereas Lemma 19.2 is stated for rho>=delta^(1/3). The proved finite walk count has no need for the stronger former range. The geometric use here needs delta<=rho^2, which the latter range satisfies. A formal caller should use this directly rather than invoke a lemma outside its stated range.

Smallest next formal target: (C1)–(C4), the actual W-tuple shear-box comparison, followed by the exact rich-W deletion and fiber count (R1)–(R4). The next substantive finite geometry target is (G1), using actual time-cell caps and a determinant bound. None should take the final tube-concentration inequality as an input.

Sanity check: 1,600 exact-rational examples in dimensions a,b in {1,2} verified (C1)–(C3), with noisy incidences, arbitrary signs, equal/reversed time levels, and rho^2<=sigma<=rho. This is a computational check of the stated constants, not a Lean proof claim.
