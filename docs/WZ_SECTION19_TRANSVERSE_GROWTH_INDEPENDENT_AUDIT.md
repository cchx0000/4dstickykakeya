# Independent audit of the Section 19 transverse-growth repair

Audited on 2026-10-03 against `/tmp/WZ_SECTION19_BOX_COMPARISON_AND_GROWTH.md` and the local Wang–Zakharov source, printed pp. 77–80, with Definitions 3.5–3.9 and 17.2–17.4 checked separately. No repository files were changed.

## Verdict

The substantive finite growth argument in §7 is correct. The original-W-to-menu repair in §§5–6 is also correct under the literal quantitative inputs listed in §3 and the asserted W lower bound. It uses full-reference upper bounds against surviving-witness lower bounds and does not require a Frostman law for a selected W family or the union of coarse direction sets.

The literal §7 statement needs routine positivity hypotheses, particularly a **nonempty angular alphabet**. Without this, its menu condition is vacuous and its conclusion is false. This is irrelevant in the intended application, where surviving W witnesses produce angular labels, but it belongs in the formal statement.

This audit does not certify construction of the native configuration, its localization and scale adapters, or the entire volume theorem. The main theorem remains open. The final count uses additional full-reference direction populations, carrier ancestor populations, and a global carrier cardinality bound; none follows from the finite growth lemma alone.

## A minimal precise finite statement

Let:

* `a >= 1` be an integer; `r > 0`, `E >= 0`, `V > 0`, and `0 < h <= 1` be real numbers.
* `X` be a nonempty finite vertex set and `x : X -> R^a` its coordinate map.
* `Z` be a nonempty finite subset of `R`, of cardinality `N`.
* Every closed interval of length `r` contain at most `H` elements of `Z`, where `H >= 1`.
* `A` be a nonempty finite angular-label set, of cardinality `m`, and `phi : A -> R^a` its representation. For all labels `b,c` and coordinates `j`, `|phi(c)_j - phi(b)_j| <= V`.
* For each vertex `v`, let `M(v)` be a set of distinct menus in `Z x Z x A x A`. Each menu `s=(z,z',b,c)` in `M(v)` has some successor `w` satisfying

      ||x(w)-x(v)-(z'-z)(phi(c)-phi(b))||_infinity <= E r.

* For a fixed `beta > 0`, every vertex `v` and every proper linear subspace `L` of `R^a` satisfy

      #{(z,z',b,c) in M(v) : dist(phi(c)-phi(b),L) >= h}
        >= beta N^2 m^2.

Distance can be Euclidean distance or distance in maximum norm. The latter also gives the Euclidean lower bound used below. No distinction affects the displayed constant. The menu condition implies `beta <= 1`.

Choose one successor for each `(vertex,menu)` once and for all. Let `Reach_a(v0)` contain the vertices obtainable from `v0` by at most `a` such moves. Set

    C = 2 a! V^(a-1) (1+2aE) + 2.

Then, for any root `v0`, the number of half-open coordinate cubes of side length `r` meeting `x(Reach_a(v0))` is at least

    C^(-a) beta^a h^(a^2) (N/H)^a.

This is exactly the proposed constant after setting `r=rho^2` and `E=E0`. Boundedness of `x(X)` in a rho-cube and containment of `Z` in a rho-interval are not needed for this lemma. They are useful separately for the application and the large-rho fallback. An undirected graph is also unnecessary: the lemma is about finite menu transitions. Symmetry is needed earlier to produce a persistent rich core.

## Proof with the endpoint collision count made explicit

At each node at depth `i-1`, retain the menus whose angular difference escapes the span of that node's preceding `i-1` angular differences by at least `h`. The span is proper for `i <= a`. Every node has at least `b0=beta N^2 m^2` children, so the depth-a tree has at least `b0^a` leaves, counted as menu sequences.

Each branch has angular vectors `v_1,...,v_a` with successive distances from previous spans at least `h`. Gram–Schmidt therefore gives

    |det(v_1,...,v_a)| >= h^a.

For maximum-norm distance, use `dist_2 >= dist_infinity` first. There are at most `m^(2a)` ordered angular-label sequences. Fix one whose leaf fiber has at least `beta^a N^(2a)` leaves. Its difference vectors are now fixed and form an invertible matrix `B` with those vectors as columns.

For that fixed angular sequence, two equal ordered time-pair sequences cannot represent distinct leaves: the successor was fixed as a function of the vertex and its entire menu, so induction from the fixed root determines the same path. Thus the retained count is a count of distinct ordered time-pair sequences, with no hidden path multiplicity.

Every retained sequence satisfies

    x_end = x(v0) + B t + e_path,
    t_i = z_i' - z_i,
    ||e_path||_infinity <= a E r.

An inverse-matrix row has absolute row sum at most

    a! V^(a-1) h^(-a).

For two retained endpoints in one r-grid cube, their physical difference has maximum norm at most `r`. Therefore

    ||t-t_ref||_infinity <= R h^(-a) r,
    R = a! V^(a-1)(1+2aE).

Now fix the unprimed time vector `(z_1,...,z_a)` as well as the endpoint grid cell. Choose a reference sequence from that fiber if it is nonempty. Each primed time lies in an interval of length at most `2R h^(-a) r`. Such an interval is covered by at most `2R h^(-a)+2 <= C h^(-a)` intervals of length `r`. Hence the fiber contains at most

    (C h^(-a) H)^a

primed time vectors. Summing over the `N^a` unprimed vectors bounds the number of retained sequences per endpoint grid cell by

    N^a (C h^(-a) H)^a.

Divide the retained sequence count `beta^a N^(2a)` by this bound. This proves the claimed estimate, including approximate incidences, repeated times, zero individual time gaps, loops, and repeated terminal vertices.

## The original-W bridge

### Branch swap and persistent richness

The original definition on p. 77 has the same starting point and the same three heights in the two branches, and the terminal angular gap condition is symmetric. The map

    (p,p1,p2,p1',p2',T1,T2,T1',T2')
      -> (p,p2,p1,p2',p1',T2,T1,T2',T1')

is an actual involution on W. It swaps terminal vertices `(z'',T1')` and `(z'',T2')`. Loops and branch-symmetric tuples cause no problem.

With `B_W=C0^5 D^2 U N^2`, fix the left terminal vertex. The five point choices are, in order, `p1'`, `p1`, `p`, `p2`, `p2'`, each bounded by `C0` once its tube and height are fixed. The free tube choices are `T1` and `T2`, bounded by `D`, then `T2'`, bounded by `U` using its projected angular proximity to the fixed `T1'`. The two free times give `N^2`. This proves the ambient degree cap without replacing an incidence by a nonincident point.

If `|W| >= alpha |Vtx| B_W`, delete vertices with surviving outgoing W degree below `alpha B_W/4`. Each deletion destroys at most twice its outgoing degree, by the involution. The total loss over all possible deletions is less than `alpha |Vtx| B_W/2 <= |W|/2`. A nonempty core remains and every one of its vertices has at least `alpha B_W/4` original witnesses to the core.

All edges preserve the terminal height. Restricting to the component of any surviving root gives the common-height graph needed for the growth application, without any further density loss.

If one starts from an arbitrary selected W subfamily, branch-swap closure must be checked. Taking all original W witnesses in the refined point configuration works. The symmetric collision subfamily formed by ordered pairs of paths in the same deterministic terminal direction cell also works. A general nonsymmetric selection does not justify the peeling argument.

### Slab escape uses the full reference

For a fixed first branch and the two times, the second initial tube is incident to the same starting point as the first. Choose a unit normal annihilating a given proper subspace. The bad projected differences lie in a slab through the first initial slope. The assumed fine-point slab law bounds the choices for this second tube in the full reference family, so it also bounds them in the selected core witness set.

For Euclidean distance the width is `r`; for maximum-norm distance use a dimensional multiple of `r`. In completely explicit notation, an estimate of the form

    #bad W <= C F (C_a r)^gamma B_W

is safe. When `0 < gamma <= 1`, the usual shorthand `C_a F r^gamma B_W` is valid after changing the dimensional constant. The proposed choice of h keeps the relevant constant inside the `1/gamma` power and is sufficient.

If `rho <= c_a h`, replacing the actual slopes by their deterministic rho-grid representatives changes a difference by `O_a(rho)`. Thus coarse differences within distance h of the subspace are included in the bad actual-slope slab at a fixed dimensional multiple of h. Choosing h to make the full-reference bad count at most `alpha B_W/8` leaves at least `alpha B_W/8` escaping original W witnesses at every core vertex, for every proper subspace.

This also ensures the slab width is above the fine cutoff: `delta <= rho^2 <= rho <= c_a h` in the intended range. The slab law is never invoked below delta.

### Menu fibers and normalization

For a fixed terminal vertex and fixed menu `(z,z',coarse u1,coarse u2)`, the same five point choices cost `C0^5`. Both initial tube choices now lie in specified rho-angular fibers and cost `U` each; the terminal partner still costs `U`. Therefore the actual W fiber is bounded by

    L_W=C0^5 U^3.

Consequently there are at least

    alpha B_W/(8 L_W)
      = (alpha/8) N^2 (D/U)^2

distinct escaping menus. The exact permissible growth parameter is

    beta = (alpha/8) (D/(U m))^2,

or any smaller positive value. The quoted `beta=K^(-C) alpha` follows from the actual bounds `D/U >= K^(-C) rho^(-kappa)` and `m <= K_q rho^(-kappa)`. One must retain those K factors. This calculation never normalizes by the cardinality of the surviving W family.

A fixed original witness for each menu gives a genuine neighbor. Choosing it independently of the excluded subspace is possible because the escape condition depends only on the menu labels. This is the deterministic choice used in the tree proof.

### Approximate incidences and representative points

A terminal vertex is a tube-height pair, not an individually chosen terminal point. Fix one genuine incident point at that height. Any other incident point in the same bounded graph delta-tube differs by `O_d(delta)` at that height. Equation (150), terminal direction closeness, and replacing initial slopes by rho-labels then give

    x(w)-x(v) = (z'-z)(phi2-phi1) + O_d(rho^2+delta).

Since `delta <= rho^2`, the error has fixed constant `E0`. It accumulates at most linearly over the fixed depth a. No extra denominator for multiple terminal points is missing: their multiplicity was already counted in `C0^5`, and the graph coordinates are fixed thereafter.

## Literal degenerate counterexample

Without `m >= 1`, take `a=1`, `rho=1/100`, `r=rho^2`, a graph with one vertex at x=0, and the empty angular alphabet. Let

    Z={j/10000 : 0 <= j <= 100}, H=2, beta=h=1,
    E0=0, V_bound=1.

Every interval of length r contains at most two times, and Z lies in an interval of length rho. Every required menu count is zero because `m=0`, so the menu hypothesis holds vacuously. Yet the displayed constant is `C_growth=4`, and G1 would require the single occupied grid cell to have cardinality at least `101/8 > 1`. This is a missing nondegeneracy hypothesis, not a defect in the intended positive-menu application.

## What remains outside this lemma

1. The lower W count and its alpha loss still require the actual local incidence count. The cancellation yielding alpha with only eta loss is algebraically correct if the per-height population and tube-count inequalities in §4 hold on the same retained point configuration with entire original incidence fibers.
2. The common coarse alphabet must cover the actual projected slopes in all original W menus. Definition 17.2's common direction set gives this at its working scales, with a bounded enlargement for O(delta) errors; the working-scale rounding factor must remain explicit.
3. The final concentration count needs full fine direction populations around each selected terminal tube, and uses them at the original retained point rather than only inside the W core. It then needs actual sigma ancestors with disjoint fine carrier fibers.
4. The final division by the original global tube count explicitly uses `|T| <= K delta^(-(d-1))`, up to fixed factors. Local AD regularity alone does not imply this for a family with arbitrarily many separated parameter-space components. It follows for the intended bounded parameter family (or another established global cardinality bound), but must be supplied by that reference configuration. The finite growth lemma cannot supply it.
5. The graph argument proves a large set of actual terminal x-coordinates. Passing from its rho^2 grid count to sigma-separated points and then to tube concentration is a separate geometric count. In the bounded dyadic carrier model stated in the note, that count has the right exponents: `(rho/sigma)^(a+kappa)` sigma ancestors, box volume comparable to `rho^a sigma^b`, and fine ancestor population `(sigma/delta)^(d-1)` give the final factor `(rho/sigma)^kappa`.

There is no further counterexample to the substantive finite lemma or its stated W-to-menu bridge in this audit. They are appropriate formal targets with the positivity hypotheses and source dependencies made explicit.
