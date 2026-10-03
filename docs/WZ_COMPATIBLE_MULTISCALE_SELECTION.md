# Compatible multiscale tuple selection, with simultaneous final uniformity

Mathematical audit, 2026-10-03. Primary source: Wang–Zakharov, supplied arXiv:2609.22035 PDF, Proposition 18.2, Step 5, printed pp. 70–72, equations (117)–(127). Definition 17.2 is on printed p. 65; its Lipschitz constant is an absolute implicit constant, by the notation on p. 15.

This note proves a small finite selection statement and gives its actual geometric caller. It concerns the alternate universal finite-volume proof. Retained labels and weights are always original labels of the chosen admissible configuration. Choosing that extremal configuration does not prove the original manuscript's hereditary old-root/cross-cap charge.

## 1. A closed finite compatible-selection lemma

Let Omega be a finite set of original labels, with nonnegative integer weights w and total W. Let a rooted finite spatial tree have levels 1,...,J. Every label belongs to exactly one leaf and therefore to its unique ancestor at every level. A forest is allowed by applying the same statement to each root.

Each node q at level j has a finite menu M_q of tuple states. For each child r of q there is a parent map

    pi_r : M_r -> M_q.

There are positive bounds B_1,...,B_J such that:

- every root menu has cardinality at most B_1;
- for a node r at level j>=2 and every u in its parent's menu,

      #{v in M_r : pi_r(v)=u} <= B_j.

Each original label x has a set G_x contained in the menu of its leaf. These are its good terminal states. No regularity or recurrence assumption on G_x is needed.

**Conclusion.** One can choose at most one state u_q at each node, consistently along occupied branches, and retain the original labels

    Omega_* = {x : the selected state of its leaf belongs to G_x},

so that

    weight(Omega_*) >= [sum_x w(x) |G_x|] / [product_(j=1)^J B_j].        (A)

A child with no extension of its selected parent contributes no retained labels. In particular, if every |G_x|>=G, the retention fraction is at least G/(product B_j).

### Deterministic construction and proof

At a leaf q define

    S_q(u) = sum_{x in q, u in G_x} w(x).

At an internal node put

    S_q(u) = sum_{children r of q} max_{v in M_r, pi_r(v)=u} S_r(v),

using zero for a maximum over an empty fiber. All scores are finite nonnegative integers. Choose a maximizing state at the root and backtrack a maximizing extension at each occupied child. This constructs the tuple field and the retained labels; its retained weight is the selected root score.

For each child r at level j, bounded fiber cardinality gives

    sum_u max_{pi_r(v)=u} S_r(v) >= (1/B_j) sum_v S_r(v).

Sum over children and iterate upward. The root maximum is at least its score sum divided by B_1. The leaf score sum is exactly sum_x w(x)|G_x|. This proves (A). The entire argument consists of finite sums, bounded fibers, and finite maxima.

A simpler implementation of the same bound runs a stagewise maximum-fiber selector on auxiliary witness pairs (x,u), u in G_x, with weight w(x). Its initial witness mass is sum_x w(x)|G_x|. The angular map at stage j is the ancestor of u; each conditional menu has at most B_j states. At the final stage there is only one selected terminal state in each spatial leaf, so at most one surviving witness pair lies over each original label x. The final projection is injective and its mass is exactly unchanged original label mass. Intermediate witness multiplicity is not reported as original retained mass.

The denominator uses an extension bound **for each parent state**, not just a bound on the total child menu. This is the part supplied by the relative multiplicity statement (113).

## 2. Actual WZ menus and telescoping scale factors

Choose nested dyadic spatial scales

    Delta_1 > ... > Delta_J,

and a fixed dyadic angular offset 0<s<=1. Put nu_j=s Delta_j, so the angular grids are nested too. Menus consist of ordered ell-tuples of nu_j-angular cells represented by actual tubes shading the spatial node q. Parent maps take angular ancestors coordinate by coordinate. Spatial containment guarantees that the resulting parent state belongs to the parent's menu.

Take fine physical labels at the original resolution delta. At each point x retain the good fine tuples from the ell-linear nonconcentration construction, with wedge at least a and good fraction at least g. A terminal state is good for x if one of those actual tuples projects to that state at angular scale nu_J. Store an actual tuple witness for every nonempty such fiber.

Write the matched multiplicity bounds with a common factor A>=1. At one physical nu_j-cell, the total coarse direction menu has size at most C_d A nu_j^(-kappa), and the number of nu_j directions inside one fixed nu_(j−1)-direction cell is at most

    C_d A (nu_j/nu_(j−1))^(-kappa).

The angular/phase-cell distinction costs only C_d at a fixed physical point: the intercept lies in an O(nu_(j−1))-box determined by that point and angular cell. A spatial Delta_j-cube is covered by at most C_d s^(-d) physical nu_j-cubes. Consequently valid state bounds are

    B_1 <= [C_d A s^(-d) nu_1^(-kappa)]^ell,
    B_j <= [C_d A s^(-d) (nu_j/nu_(j−1))^(-kappa)]^ell,  j>=2.

At a fine point, there are at least A^(-1)delta^(-kappa) fine directions; each nu_J-direction cell contains at most C_d A(delta/nu_J)^(-kappa) of them. Compressing good fine tuples therefore gives

    |G_x| >= g (C_d A)^(-2ell) nu_J^(-kappa ell).

All powers of nu telescope in (A). Thus a valid uniform retention fraction is

    lambda_0 = g (C_d A)^(-ell(J+2)) s^(d ell J).                     (B)

Fixed-dimensional enlargements can be included by increasing C_d. Nothing in (B) is a near-extremality assumption: its inputs are the actual common and relative multiplicity counts already obtained from (113).

Using nu_j=Delta_j, or s=1, gives compatible tuple coordinates with only an A^O(ell J) loss. The smaller angular scales in the next section control the **planes** as well as their possibly ill-conditioned spanning tuples.

## 3. Actual witnesses and quantitative plane continuity

For every occupied node q choose one retained descendant label and one of its stored good fine tuple witnesses. Call this actual tuple theta_q. It has wedge at least a. Every retained label in q has its own good terminal witness in the selected angular ancestor tuple at q. Therefore all those witnesses, including all descendant node witnesses, lie in exactly the same ordered nu_j-cells.

For descendants r,r' of the same level-j node,

    max_i |theta_(r,i)-theta_(r',i)| <= C_d nu_j.                    (C)

There is no accumulated sum over levels. This is exact ancestor-cell consistency. Dyadic cell centers are never used as transverse vectors.

For graph vectors (theta_i,1), the horizontal difference vectors theta_i-theta_ell span an (ell−1)-plane and have wedge at least c_d a. Standard finite-dimensional Gram–Schmidt/inverse-matrix estimates then give

    distance of the corresponding horizontal planes <= C_d nu_j/a.

Thus choose a fixed dyadic s with c_d a/2 <= s <= c_d a. If Delta_1 is a sufficiently small dimensional constant, all planes in one root stay in a fixed graph chart whose projection has a fixed lower singular-value bound. In that chart the graph matrices satisfy

    |f_r-f_r'| <= C_d Delta_j                                     (D)

for descendants of the same level-j spatial node. The graph chart can be chosen once per root, using one actual witness plane. A finite root/chart pigeonhole costs a fixed factor when a single chart is needed.

This explains why plain angular consistency at scale Delta_j only gives an a^(-1) Lipschitz constant. That factor is not an absolute constant and should not be silently dropped in (127). The offset nu_j≈a Delta_j pays an explicit subpower menu loss in (B) and restores the absolute bound (D).

The smallest angular scale must still exceed the original resolution. If Delta_J=epsilon and a>=epsilon^sigma with sigma<1, then nu_J≈epsilon^(1+sigma) remains above epsilon^2 for sufficiently small epsilon. The source declares epsilon^2 to be its working fine point scale after ell-linear selection. The geometric caller must check that the original tube thickness is no larger than the h_j used here (in particular delta<=epsilon^2), or supply the appropriate earlier refinement/rescaling. The finite tree lemma itself has no such geometric scale assumption.

## 4. Insert all rich-layer constructions with one global budget

After selecting the compatible field, every retained label in a node has the actual directional witnesses needed for the one-scale construction in WZ_RECURRING_TUPLE_RICH_LAYERS.md.

For each level j and node q use the original reference labels in a fixed enlargement of q, including whole spatial net atoms. Write their mass W_ref(q). Enlarged dyadic cubes have bounded overlap, so at each level

    sum_q W_ref(q) <= C_ov W.

No individual lower bound on the mass of an occupied dyadic q is required here. Let h_j=Delta_j^2. The earlier self-uniform spatial profile supplies h_j-scale reference atoms with masses in [m_j,G_j m_j]. Dense uniform h_j-tube shadings supply at least

    b_j = c_d lambda_sh/(K_Y Delta_j)

reference atoms in each relevant directional column after padding.

Choose each node's adapted grid with a padding failure fraction at most 1/(4J), measured against the same compatible label set Omega_*. This only increases the grid constant H to C_d J. The weighted padding selectors at different nodes are independent choices, and the union bound over levels loses at most lambda_0 W/4. All resulting grids are fixed from then onward.

Put

    alpha = lambda_0/(8 ell J C_ov).

Run the rich-directional-layer constructor at every node and every level, on the CURRENT retained labels. At node q, direction i, delete columns of current original integer mass below

    k_j = ceil(alpha b_j m_j).

The number of relevant columns is at most W_ref(q)/(b_j m_j). Since k_j−1<alpha b_j m_j, the loss at that node/direction is less than alpha W_ref(q). Summing over all nodes, directions, and levels loses at most lambda_0 W/8.

A single adapted grid vertex has original mass at most

    M_j = F_j G_j m_j,   F_j <= C_d (J/a)^d.

Hence each surviving point at the moment of this node's construction has at least

    L_j >= alpha b_j/(F_j G_j)

distinct predecessor grid vertices in the previous layer. The already proved independent-fiber multiplication gives a grain-class count bound. Every later retained set is a subset of that output, so its occupied grain classes satisfy

    N_(j,q) <= C_d W_ref(q)/(m_j L_j^ell).

At a fixed level, regard the grain class as the PAIR consisting of its spatial node q and its normal grid index. Summing over q gives the fixed bound

    N_j <= C_d C_ov W/(m_j L_j^ell).                              (E)

All tuples, grids, and class maps are now fixed. Later refinements cannot increase N_j. What later refinements can destroy is the population of an individual class. The next step repairs exactly that issue while obtaining final uniformity.

## 5. One final self-uniform refinement gives both uniformity and rich grains

Let Omega_R be the output of the preceding constructions, with mass at least lambda_0 W/2. For each level j define the equivalence relation

    x ~_j y iff x and y have the same pair (spatial node, grain normal index).

These are symmetric reflexive relations on the original retained labels. Add these J relations to the finite family of symmetric point-line and spatial relations for which final self-uniformity is required. Apply the already proved symmetric weighted self-uniform refinement **once** to Omega_R.

Let Omega_f be its output, with

    W_f >= r_unif weight(Omega_R),

and comparison factor K_unif. Padding, good tuple membership, and ancestor-cell consistency survive because Omega_f is a subset. The same output has the required point-line/spatial self-uniformity.

For each j, the occupied grain classes still number at most N_j. One has mass at least W_f/N_j. Self-uniformity of the equivalence relation then forces EVERY occupied level-j grain class to have mass at least

    W_f/(K_unif N_j)
      >= c_d r_unif lambda_0 m_j L_j^ell/(K_unif C_ov).            (F)

Dividing by M_j gives a lower bound on retained grid vertices, hence on physical h_j-covering numbers with the fixed-overlap conversion. Thus every occupied grain is quantitatively rich at every working scale, on the **same final labels** that have point-line/shading uniformity.

This avoids an alternating prune/uniformize argument. An arbitrary subsequent refinement could destroy these properties and is not claimed to preserve them. Any further required finite symmetric relations should be included in this final call, or its losses and grain populations must be re-established.

Adding J equivalence relations changes the relation count from S to S+J. For fixed J and polynomially bounded original integer incidence mass, the proved self-uniform theorem still permits r_unif=delta^o(1) and K_unif=delta^(-o(1)). Actual finite tube-point incidence labels have the required polynomial bound. Arbitrary real old-occurrence measures are not being silently discretized with unbounded integer weight.

The source says both E_0 and E_1 are uniform in (126). Earlier E_0 keeps its previously established uniformity. The final call above gives the required uniformity to the actual E_1/point-line output, while grain equivalence relations ensure its richness simultaneously. Include physical point-fiber relations when converting incidence uniformity into unweighted physical-point uniformity.

## 6. Parameter order and why the scale spacing must be chosen separately

Set epsilon=Delta_J. Suppose

    A <= epsilon^(-u),   a >= epsilon^v,

and all other reference profile losses are epsilon^(-O(u+v)). Choose s≈a as above. Formula (B) gives

    lambda_0 >= c_(d,J) g epsilon^[ell(J+2)u + d ell J v].          (G)

The rich-layer and final grain formulas introduce only fixed-dimensional powers of lambda_0, a, the profile constants, and J. Consequently their total exponent is at most C_d J(u+v), apart from the separately chosen arbitrarily small self-uniform exponent. No tower of losses is necessary.

A valid quantitative order is:

1. Fix the desired final loss exponent zeta>0 and desired output scale spacing tau>0 (tau may be a small fixed multiple of zeta).
2. Choose the FINITE working depth J=O(1/tau), independently of the fine mesh. Use dyadic scales Delta_j≈epsilon^(j/J), including the endpoints needed after the final rescaling. Rounding costs fixed factors. A fixed smaller first root scale can be included.
3. Choose u,v so that C_d J(u+v)<=zeta/4. In the source variables, v=O_d(eta_ell/eta_(ell−1)); choose that ratio after J, small enough for this inequality. Choose the input/matched-multiplicity slack still smaller.
4. Choose the final self-uniform retention/comparison exponents below zeta/4, including all needed point-line, spatial, and J grain relations. Padding constants are polynomial in the fixed J.
5. Choose epsilon and the original fine mesh sufficiently small to absorb fixed constants, make nu_J>=epsilon^2, and satisfy every power-separated class-closure call. To convert a self-uniform loss measured in the original delta into epsilon-loss, explicitly use epsilon<=delta^c with c>0 fixed before delta, and choose its delta-exponent below c times the allowed epsilon-exponent. Also require delta<=epsilon^2 for the coarse-shading geometry. A fine/coarse loss conversion without such a scale relation is not automatic.

One should not simply set our working step spacing equal to the same much smaller input eta used elsewhere in the paper. That gives J≈1/eta, and an explicit loss A^O(J) need not be absorbable. The finite self-uniform theorem allows arbitrary finite prescribed scales, so using a coarser working list chosen from the desired OUTPUT spacing is legitimate. The original finer list can be retained when useful; it need not be the list on which tuple choices are made.

After the source's final rescaling epsilon=delta_tilde^2, all epsilon-exponents double when written in delta_tilde. Reserve this fixed factor in C_d. The output definition only asks for dyadic Lipschitz control on its specified finite scale list; all endpoints and its rounded scales must be included in the working list rather than supplied by interpolation with an uncontrolled mesh ratio.

## 7. A second bounded-branch selection makes the field depend on height

Spatial consistency does not by itself imply the height-only statement (127). There is an additional finite construction that supplies the missing relation. Set tau=sqrt(epsilon), the source's final tube and point scale after anisotropic rescaling.

Every original fine incidence label has its actual fine tube, hence a unique coarse phase ancestor T_tau. Keep that label; no choice of a different tube is made. For each required height scale rho>=tau, record:

- its coarse tube ancestor T_tau;
- its dyadic rho-height interval I_rho;
- its dyadic spatial rho-cell Q_rho.

A bounded-slope tau-tube restricted to a height interval of length rho has horizontal diameter at most C_d(rho+tau)<=C_d rho. Therefore it meets at most C_d spatial rho-cells. This is an elementary graph-box count, valid including rho=tau, with a fixed constant depending on the chosen tube enlargement and slope bound.

Apply the finite compatible selector inside each T_tau, with the spatial tree now the HEIGHT-INTERVAL tree and the states the spatial cells Q_rho. A label has a unique terminal spatial state, so G=1; all extension bounds are at most C_d. The output retains at least C_d^(-J) of the input original incidence mass and has one nested selected Q(T_tau,I_rho) for every occupied coarse-tube/height-interval pair. In particular,

    all retained points shaded by T_tau in one I_rho lie in the SAME spatial rho-node.

The construction is simultaneous over all T_tau. A physical point with several original fine-tube incidences keeps whichever original incidence labels survive; none is added or relabelled. The per-tube choices need not agree between different coarse tubes, because the final construction chooses one such tube for rescaling.

Insert this bounded-branch selection after constructing the fixed compatible field and rich-layer class bounds, but BEFORE the final combined self-uniform call. Its C_d^(-J) loss only multiplies the retention r in (F); the previously recorded grain-class upper bounds remain true for this subset. Add any required coarse-tube fiber relations to the final self-uniform list. Thus the final same-label uniformity and grain richness are retained together.

The working spatial scale list must include every rho used in the height tree, including tau. For rho>=tau, the selected spatial node and (D) now give

    |f(p)-f(p')| <= C_d rho

whenever the two retained points belong to the same T_tau and height interval. A finite Grassmannian coordinate-chart pigeonhole, performed before the final self-uniform call, can ensure one fixed well-conditioned graph chart for all selected planes; it costs only a dimensional factor. One need not assert that charts chosen independently at different roots agree.

At the final height resolution tau, choose one actual retained point in each occupied tau-height interval and use its plane as the representative f_Ttau(z). All other retained planes in that interval differ from it by O_d(tau). For two final height bins in the same required rho-interval, the representative points share Q(T_tau,I_rho), so

    |f_Ttau(z)-f_Ttau(z')| <= C_d rho.

This is the actual finite mechanism for the dyadic Lipschitz assertion (127).

There is still an explicit, constant-resolution geometric representation step: replacing approximately parallel tau-thick pieces by a common representative plane at that height can move auxiliary grid representatives by O_d(tau). Keep original targets and marks on their labels, record this auxiliary projection, and cover the moved representatives by a fixed enlargement of the original tau-cubes/tubes. Do not claim that the unmoved original points suddenly lie in an exact affine plane. Establishing the exact product notation for E in Definition 17.2 uses this quantization/projection and the subsequent AD-slice construction. No new dense shading may be supplied outside the actual represented original shadings.

The subset assertion used around (124) likewise requires actual restriction: the child recurrence set is intersected with the already retained parent set. Our terminal-witness construction and all later refinements only take subsets, so that inclusion is built in.

## 8. Bounded auxiliary class and final-theorem scope

For the alternate final theorem, fixed compact-front packets can be mapped into a bounded graph class by a dyadic isotropic homothety chosen from their fixed compact bound B BEFORE the arbitrarily fine mesh is chosen. Cubical shadings map exactly; contracted actual segments may be included in unit graph tubes while only the mapped actual shadings are retained. Their density decreases by the fixed factor 1/B. Direction separation is stronger than the new physical thickness, and AD/CW change by fixed powers of B.

Those fixed losses can be absorbed in later mesh/slack choices. This avoids an unrestricted-offset normalization obligation for the proof of the original compact theorem. It does NOT prove the existing universally quantified public finite-volume axiom for unrestricted native offsets with one small-scale threshold independent of B. The bounded-class theorem must be called directly on normalized compact packets in the final closure.

## 9. Independent finite sanity check

A separate randomized implementation of the deterministic dynamic program checked 1,000 finite trees, depths one through four, unequal menus, empty extension fibers, arbitrary good terminal sets, and integer original weights. The selected score always equaled the actual backtracked retained weight and satisfied (A). This is a sanity check, not a Lean proof of the new tree lemma.

## Formal implementation scope

The finite weighted layers, compatible tuple selector, simultaneous uniform/grain
refinement, padded physical-cell witness, density ledger and native marked-line
constructor are independently formalized. See
[WZ_COMPATIBLE_GRAINS_CHECKPOINT.md](WZ_COMPATIBLE_GRAINS_CHECKPOINT.md) for exact
boundaries. This does not assert a completed global grain decomposition or final
volume theorem.
