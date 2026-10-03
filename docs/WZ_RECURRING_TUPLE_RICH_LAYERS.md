# WZ Step 5: constructing a recurring tuple and rich predecessor layers

Mathematical audit, 2026-10-03. Source: Wang–Zakharov, supplied arXiv:2609.22035 PDF, printed pp. 68–72. The combined geometry remains an audited handwritten argument; no new theorem assumption or imported estimate is introduced.

## Result

There is a constructive **one-scale** adapter from the actual conclusions of Steps 1–4 to the hypotheses of the already proved backward-fiber/grain theorem. It does not need the entire global grains definition. Its components are:

1. nonconcentration gives many genuinely transverse fine tuples;
2. a fiber bound compresses these to many coarse direction tuples;
3. a weighted double count chooses one recurring coarse tuple;
4. retain an actual transverse witness of that tuple, rather than its dyadic cell centers;
5. a common, anisotropic, shifted coordinate grid converts the approximate directional segments to exact coordinate columns;
6. bounded original mass per grid vertex and a lower reference mass in every relevant column give explicit deletion budgets and rich predecessor layers.

Everything selected is a subset of the original fine occurrence labels. Projection to grid vertices is an auxiliary map. No target, mark, tube, or original weight is replaced. This is a local construction for the universal WZ route; it does not by itself pay the original old-edge cross-cap charge.

The remaining construction after this one-scale lemma is the compatible iteration over spatial scales, WZ (119), (124)–(127). The local lemma does not assert that independently selected tuples at different scales agree.

## 1. Exact source location and inputs

The relevant statement is **Proposition 18.2, Step 5, equations (114)–(123), pp. 70–71**. It is not a separately numbered lemma. Inputs are constructed earlier:

- Step 1, p. 68: an ell-linear stopping alternative, including nonconcentration near every (ell−1)-plane and a substantial retained fraction of the original incident tubes at each retained point.
- Steps 2–3, pp. 68–69: self-uniform point-line incidence data; individual coarse tube shadings are uniform, equation (106).
- Step 4, pp. 69–70: the same extremal exponent bounds coarse and rescaled configurations, yielding matched multiplicities, equation (113).

Equations (114)–(116) make many coarse transverse tuples. Equations (117)–(118) select recurring tuples by double counting. The bad-segment deletion just before (120) creates rich layers. The transverse projection argument (123) is the stage handled by the already proved backward-fiber lemma, after the grid construction below.

The literal expression (123) names E^i in its fiber. The safe finite statement uses predecessors in E^(i−1). This is what the actual successive deletion supplies, and it is sufficient for the backward-fiber theorem plus final grain selection. There is no need to claim that later deletions preserve every earlier fiber population.

## 2. Fine transversality from the stopping alternative

Let Theta be a finite set of graph directions v(theta)=(theta,1), with |v|<=B, B depending only on dimension. Suppose that, for every (ell−1)-dimensional linear subspace W,

    #{theta : dist(v(theta),W)<=r} <= e |Theta|,

where 0<e<=1/(2 ell). Extending a smaller-dimensional span to an (ell−1)-plane shows the same upper bound for each partial span. Choose the tuple sequentially. At every step after the first, at least (1−e)|Theta| directions lie at distance >r from the preceding span. Gram–Schmidt therefore gives

    # {tuples : |v_1 wedge ... wedge v_ell| >= r^(ell−1)}
       >= (1−e)^(ell−1) |Theta|^ell
       >= (1−(ell−1)e)|Theta|^ell >= |Theta|^ell/2.

The first vector has norm at least one because its final coordinate is one.

If the nonconcentration estimate was originally stated for Theta_old and Theta retains at least s|Theta_old| directions, then the new bad fraction is at most r^eta_prev/s. Taking r=(e s)^(1/eta_prev), within the stopping range r<=rho_prev, gives the displayed hypothesis. Thus s>=delta_ell^(C eta_ell) and e=delta_ell^eta_ell give a wedge threshold

    a = delta_ell^O_d(eta_ell/eta_prev).

This is the elementary sequential proof behind (114)–(115). The required s is pointwise, not merely an average. In the source it follows after point multiplicity uniformization and the tracked refinement loss.

## 3. Compressing and selecting a common tuple, with original weights

Fix one spatial Delta-cube Q and put h=Delta^2. Let P be the original fine physical points in Q, with nonnegative original incidence weights w(p). The weights can equivalently be represented by original marked labels over p. Write W_Q=sum w(p)>0.

Let C be the set of Delta-direction cells represented by coarse tubes whose actual coarse shading contains Q. Put D=|C|. For every p assume:

- at least n fine incident directions survive;
- at least a fraction g of their ordered ell-tuples have wedge at least a;
- at most F fine incident directions belong to one Delta-direction cell.

These are concrete fine and coarse incidence counts. The previous section supplies g>=1/2. Matched multiplicities supply n,F,D. At a fixed point and fixed Delta-angular cell, only O_d(1) Delta-phase ancestors can occur: their intercept cells must meet the O(Delta)-box p_x-p_t times that angular cell. Thus a phase-ancestor fiber bound becomes the required angular fiber bound with a dimensional factor; it is not an identification of phase and angular cells.

Map a good fine tuple to its ordered Delta-cell tuple. Each fiber has at most F^ell members. Hence the number of good coarse tuples at p is at least

    g (n/F)^ell = beta D^ell,   beta := g (n/(F D))^ell.

All these tuples belong to the same menu C^ell. This common menu is justified directly: if a fine tube shades p in Q, its Delta-ancestor coarse shading, defined as the union of Delta-cells meeting its fine shading, contains Q.

For u in C^ell let P_u be the points at which u is represented by a good fine tuple. Then

    sum_u weight(P_u) = sum_p w(p) #{good coarse tuples at p}
                     >= beta D^ell W_Q.

Consequently some u has weight(P_u)>=beta W_Q. More quantitatively, at least beta D^ell/2 tuples have weight(P_u)>=beta W_Q/2: tuples below that threshold contribute at most beta D^ell W_Q/2 and each remaining tuple contributes at most W_Q.

This proves the weighted recurring-tuple construction in (117)–(118). It does not select a different root configuration or change any fine weight.

If one writes the matched bounds with a single factor A>=1,

    n >= A^(-1) delta^(-kappa),
    F <= A (delta/Delta)^(-kappa),
    D <= A Delta^(-kappa),

then beta>=g A^(-3 ell). With A=delta_ell^(-6 eta_ell), this is at least (1/2)delta_ell^(18 ell eta_ell), so the source's recurrence threshold delta_ell^(20 ell eta_ell) is available for sufficiently small delta_ell. This is a safe, slightly weaker count than the optimized exponent printed in (116)/(118).

### Keep an actual transverse witness

Choose one good fine tuple witnessing the selected u at one of its recurring points, and call its vectors v_1,...,v_ell. These fixed vectors have wedge >=a. At every other recurring point there is an actual incident tube in the same Delta-cell as v_i, so its graph direction differs from v_i by O_d(Delta).

Do **not** replace v_i by the centers of the Delta-direction cells. Delta need not be smaller than a; those cell centers can be dependent even though the actual witness is transverse. Keeping the witness avoids an unnecessary and potentially false scale condition. Over a segment of length Delta, the O(Delta) directional error creates only O(Delta^2)=O(h) transverse drift.

## 4. Local reference mass and spatial atoms

Let Omega_ref be the original fine labels in a fixed enlargement of Q, enlarged further by O(h) to include whole spatial atoms. It includes all local shading witnesses below. Its total original weight is W_ref. Write

    R = W_ref/W_Q >= 1.

No unproved doubling estimate is concealed in this definition. The exact construction works with this actual ratio. Metric lower bounds do not give R<=C K_sp for an arbitrary occupied unpadded dyadic cube. A constructive local choice is a maximal-Delta-net Voronoi cluster Q: it contains the support in the Delta/2-ball around its center and lies in its Delta-ball. Spatial self-uniformity at comparable radii then gives R<=C_d K_sp. This Q meets only O_d(1) dyadic Delta-cubes, so use the union of their coarse direction menus; the bound on D changes only by a dimensional factor. This proves the one-scale local version without assuming spatial dyadic padding. To insist on each literal dyadic Q in the source, first prove the corresponding spatial padding/refinement statement. If spatial uniformity itself has not yet been transferred from the point-line profile, R remains explicit.

Use a maximal h-separated net of the physical support and assign each point to its nearest center, breaking ties deterministically. Each atom lies in an h-ball and contains the support in the open h/2-ball about its center. The net centers are h-separated.

Suppose original weighted spatial ball counts are self-uniform at radii comparable to h and h/2. Covering one h-ball by C_d half-radius balls whose centers lie in the support compares the maxima at these scales. It follows that every atom has original mass between

    m and G m,

with G<=C_d K_sp (or the corresponding fixed power of the known profile constant). This avoids the false assertion that metric lower counts automatically imply lower mass in every occupied unpadded dyadic cell. All labels in an atom remain distinct original labels.

Only the atoms intersecting a fixed enlargement of Q need be included in Omega_ref; include each such atom in full. Lower atom mass is inherited from the global construction, not asserted for a boundary-truncated atom.

### Dense uniform tube shadings give many local atoms

At thickness h, an actual coarse tube shading has at least lambda/h occupied h-cells and is K_Y-uniform along the tube at longitudinal scale c Delta. Cover its bounded length by C_d/Delta such neighborhoods. Every occupied neighborhood then has at least

    b = c_d lambda Delta/(K_Y h) = c_d lambda/(K_Y Delta)

occupied h-cells. Replacing them by actual original shaded points and then by the spatial atoms loses only a dimensional factor, because one diameter-2h atom meets only O_d(1) h-cells.

At a recurring point p, use its incident h-tube inside the selected Delta-direction cell and its local length-c Delta shading. This constructs at least b actual reference atoms near the length-c Delta segment in the fixed direction v_i. They belong to Omega_ref. No dense shading is assigned to an arbitrary old-edge thinning.

For clarity, K_sp and K_Y are different already constructed uniformity constants; lambda is the actual coarse shading density. The argument only uses their quantitative values.

## 5. One common grid makes the approximate segments exact fibers

Let V=span(v_1,...,v_ell). Complete these vectors to a basis B of R^d by an orthonormal basis of V-perp. Since |v_i|<=B_d and their wedge is at least a,

    ||B|| <= C_d,   ||B^(-1)|| <= D := C_d/a.

The last d−ell coordinate functionals of B^(-1) are orthogonal projection to V-perp and have norm one. This stronger fact is useful: transverse physical grain thickness need not be enlarged by D.

Put z=B^(-1)x. Choose a rectangular coordinate grid with widths

    w_j = H D h   for j<=ell,
    w_j = H h     for j>ell,

where H is a sufficiently large dimension-dependent constant (ell<=d). Choose one random shift of this whole grid, independently in each coordinate over its period.

A recurring point p is good if its first ell coordinates are at distance >=C_d D h from every grid boundary, and its remaining coordinates at distance >=C_d h. Each coordinate is bad on at most C_d/H of its shifts. The union bound and weighted finite averaging select one common shift for which good recurring original labels have mass at least beta W_Q/2. This is an actual use of the proved weighted real-translation padding selector with one normalized scale. It shifts only the auxiliary coordinate grid, not the physical targets.

Let Omega_0 be these original good recurring labels. Map every reference label to the integer index q(x) in this common grid.

For direction i and p in Omega_0, every point in each of the b local reference atoms above satisfies

    x = p + s v_i + e,  |s|<=c Delta,
    |(B^(-1)e)_j| <= C_d D h for j<=ell,
    |(B^(-1)e)_j| <= C_d h for j>ell.

Here e includes the actual h-tube width, the O(Delta) direction error times length Delta, and the whole-atom diameter. The padding margin was chosen to absorb their sum. Thus for every j!=i, q_j(x)=q_j(p).

Therefore the coordinate column

    {x : q_j(x)=q_j(p) for every j!=i}

contains at least b full reference atoms and has original reference mass at least b m. These are exact coordinate fibers. The same grid works for every i.

### Upper mass at one grid vertex

A physical image of one grid cell has diameter <=C_d H D h. By h-separation, at most

    F_grid = C_d (H D)^d

net atoms can meet it (allowing the atom diameter in the constant). Consequently its original reference mass is at most

    M = F_grid G m.

This bound holds for all later subsets of original labels. It does not require lower mass in an arbitrarily cut grid cell. Moreover, each diameter-2h atom meets at most C_d grid cells: in z-coordinates its widths are O(Dh) in the first ell coordinates and O(h) in the others, smaller than the chosen periods. This last bounded-overlap fact is useful when returning a grid count to physical h-covering numbers.

The normal coordinate periods are Hh, independent of D. The inverse image of a coordinate ell-plane class is a physical O_d(h)-thick slab parallel to V. Thus the grains have the desired Delta^2 thickness, up to a fixed factor, even when the selected tuple is poorly conditioned.

## 6. Explicit construction of the rich layers

For each i let pi_i(q) erase coordinate i. Let active columns mean columns meeting q(Omega_0). Every such column has reference mass >=b m. Since these columns partition the reference labels,

    number of active i-columns <= W_ref/(b m).

Put W_0=weight(Omega_0), so W_0>=beta W_Q/2. With integer original weights choose

    k = ceil(W_0 b m/(2 ell W_ref)).

Starting from Omega_0, define Omega_i by discarding every i-column whose CURRENT original weight in Omega_(i−1) is <k. Previously retained labels are either kept with their original weights or discarded. One step loses at most

    (k−1) W_ref/(b m) < W_0/(2 ell).

After ell steps,

    weight(Omega_ell) >= W_0/2 >= beta W_Q/4.

Every label surviving step i lies in a column with at least k original weight in Omega_(i−1). Each grid vertex carries at most M original weight, so that column contains at least k/M DISTINCT predecessor vertices from q(Omega_(i−1)). In particular one can take the integer predecessor lower bound ceil(k/M), and it is at least

    L = beta b/(4 ell R F_grid G)
      >= c_d beta lambda/(ell R F_grid G K_Y Delta).

Let A_i=q(Omega_i). Then A_ell subset ... subset A_0, and every x in A_i has at least L predecessor vertices in A_(i−1) differing only in coordinate i. These are exactly the independent-coordinate hypotheses of the already proved backward-fiber theorem. They have now been CONSTRUCTED from recurring actual tube incidences.

The ceiling version remains valid when the displayed real L is less than one. It never presumes a scale inequality forcing many predecessors. Such regimes simply yield the trivial one-predecessor conclusion.

A real-weight alternative uses the threshold a times the actual reference column mass, with a=W_0/(2 ell W_ref). The total removed mass is <=a W_ref at each step. Integer weights make the fixed threshold and existing finite cardinal primitives especially convenient.

## 7. Exact quantitative output and loss accounting

With

    beta >= g A^(-3 ell),
    F_grid <= C_d (H D)^d,   D<=C_d/a,

the construction returns:

- an actual transverse tuple with wedge at least a;
- one common explicit grid and original-label subsets Omega_ell subset ... subset Omega_0;
- original retained mass at least beta W_Q/4;
- exact coordinate predecessors of size at least

      c_d beta lambda / (ell R G K_Y D^d Delta);

- physical grain normal thickness O_d(Delta^2).

The already proved fiber multiplication then gives a lower population proportional to the ell-th power of this predecessor bound in A_0. The already proved labelled weighted grain extraction selects rich plane classes while retaining a fixed fraction of the remaining original weight. The bound above is the new caller, rather than a repetition of that induction.

For returning to physical covering numbers, each original h-scale net atom maps to O_d(1) grid vertices. The number of A_0 vertices is bounded by C_d W_ref/m. Therefore the final weighted grain threshold from the existing extraction theorem is bounded below by a constant times

    (beta/R) m L^ell.

Dividing by the upper vertex mass F_grid Gm gives at least

    c_d beta L^ell/(R F_grid G)

retained grid vertices in every selected grain. A physical h-cell meets only O_d(1) grid cells for the same width reason. Thus this lower count transfers, with a dimensional loss, to physical h-covering counts. This is a positive explicit power of a,beta,lambda and the inverse uniformity factors, times Delta^(-ell), as required by (122).

If A,K_sp,K_Y,G,R,lambda^(-1) are delta_ell^(-O_d(eta_ell)), and a^(-1)=delta_ell^(-O_d(eta_ell/eta_prev)), the total loss is

    delta_ell^O_d(eta_ell/eta_prev),

the form used in (122)–(123). No fixed determinant lower bound independent of scale is assumed.

## 8. What still needs to be formalized or proved downstream

The finite recurring-tuple double count, the sequential Gram–Schmidt count, the common-grid geometry, and the weighted column-deletion budget above are independent elementary constructions. The repository includes proved padding and backward-fiber/grain extraction theorems; their exact geometric callers remain to be assembled.

The earliest adapter statements still requiring a checked geometry implementation are:

1. transfer the self-uniform point-line counts to spatial weighted ball counts at h and h/2 and to individual coarse shading uniformity/density;
2. make the actual coarse direction menu/fiber bounds from (113) into the three finite values n,F,D;
3. prove the adapted-grid column containment and grid-cell mass packing estimates in section 5.

These are concrete geometric statements, not assumptions to be added to the final theorem. A proof of the universal extremal exponent and all its admissible-family calls remains necessary to obtain (113).

After the one-scale lemma, the source additionally constructs compatible tuple choices across scales via (119), discards unsuitable child cubes in (124), and obtains the dyadic Lipschitz slope in (127). That is a separate remaining obligation. Independent one-scale choices do not imply it. The later AD-slice and planarity steps, and Propositions 17.3–17.5, also remain outside this local adapter.

## 9. Independent numerical checks

A separate randomized check tested 400 finite weighted partition-pruning instances and 600 four-dimensional adapted-grid instances, including nearly dependent tuples, all ell in {2,3,4}, and Delta both larger and smaller than the tuple conditioning scale. Every deletion-budget and exact-column-containment check passed. These checks are sanity checks; the arguments above are the mathematical justification, and no Lean verification of this full geometric adapter is claimed.

## Formal implementation scope

The finite weighted layers, compatible tuple selector, simultaneous uniform/grain
refinement, padded physical-cell witness, density ledger and native marked-line
constructor are independently formalized. See
[WZ_COMPATIBLE_GRAINS_CHECKPOINT.md](WZ_COMPATIBLE_GRAINS_CHECKPOINT.md) for exact
boundaries. This does not assert a completed global grain decomposition or final
volume theorem.
