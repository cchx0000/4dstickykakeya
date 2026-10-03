# Proposition 18.2 output audit and the next usable source lemma

Handwritten mathematical audit, 2026-10-03. Primary source: Wang–Zakharov, supplied arXiv:2609.22035 PDF. Printed pages are used below. No repository writes.

## 1. Source order and current scope

**Proposition 18.2 ends with Step 6 and (140), on p. 74. There is no Step 7.** It constructs a global grains configuration as in Definition 17.2, plus convex Wolff control. It does NOT yet construct the stronger ell-linear k-planar configuration required by Proposition 17.2 (restated as Proposition 18.1).

After the grains proof, Proposition 18.1 has three additional steps, pp. 74–76:

1. AD-set alignment, using Lemma 5.3 (pp. 23–25), with dimension-raising if the extracted line exponent is nearly one;
2. repeated linear stopping/rescaling to obtain slab-Frostman directions;
3. compatibility of the two slope functions, followed by controlled thickening to make the consistency relation exact.

Thus Lemma 5.3 is the first substantive source-order geometric input beyond global grains in the d−ell>1 branch. In d=4 this is the ell=2 branch. If ell=3, the quotient is one-dimensional and that alignment step is skipped, but the slab-Frostman stopping step remains.

Lemma 19.1, p. 77, is nevertheless already USABLE from the global-grains incidence properties: its counting proof does not use slab-Frostman or tube Katz–Tao. A complete, robust finite derivation appears below. The first geometric payoff in that subsection is Claim 19.3, pp. 79–80; Lemma 19.2's expansion argument additionally needs the Frostman condition from the stronger upgrade.

The previous notes supply mathematical constructions and concrete callers; only the finite modules reported by the parent are presently kernel-certified. There is not yet a compiled assembly of all Definition 17.2 clauses or a replacement universal WZ theorem.

## 2. Independent re-audit of the coarse-height union proof

The new coarse-union derivation does not transport a lower density through an arbitrary shading cut:

- The carrier AD backbone is kept fixed; shade deletion affects its incidence set, not its parameter population.
- For every pair rho<=s, the FINAL phase/time class (s-ancestor, rho-time interval) receives its lower ORIGINAL mass from `partition_richness_of_self_uniform`, the final total incidence mass, and the original bound on the number of those classes.
- The lower coarse spatial count divides that mass first by the actual inverse-image weight of ONE coarse point/phase pair, and then by the number of coarse phase pairs at ONE coarse point. Neither denominator is silently set to one.
- The upper coarse count uses a distinct coarse incidence image and the fine carrier-net upper count. It does not require lower population in each occupied dyadic phase cell.
- The requested quotient union U_I is not replaced by a dense subset. Each original cell is assigned to a rich neighboring cell of the FULL common-slope ambient slice. Only full ambient upper AD is used for this upper estimate.
- The lower quotient estimate uses the FULL ambient lower AD and a reverse bounded-displacement map. It does not assert lower AD for the rich restriction.
- Voronoi localizations are split by the actual time-bin label. Coarse and fine floors use nested half-open grids.

One organizational requirement remains essential: all maps used in these arguments, including the phase/time pairs and new quotient fibers, must be prepared before the ONE terminal uniform refinement. A later unaccounted restriction could destroy the claimed final lower counts. The endpoint/exponent conditions in the coarse-union note remain necessary.

## 3. Definition 17.1: what the universal assertion actually says

Definition 17.1, p. 65, quantifies: for every epsilon>0 choose eta>0 and a sufficiently small scale, uniformly for (d−1)-AD tube families with convex-Wolff constant <=delta^(-eta) and aggregate delta^eta-dense shading; conclude

    |union Y|_delta >= delta^epsilon delta^(-d+kappa).

The infimum/near-extremizer construction belongs to this universal auxiliary class, with the SAME exponent applying to the coarse and rescaled families. The native compact-front packets are actual starting configurations, not arbitrary old-edge thinnings.

For the original compact theorem, a fixed bounded graph auxiliary class suffices: normalize its fixed compact bound B before choosing arbitrarily fine packets. This does not prove the pre-existing public axiom over unrestricted offsets with one scale threshold independent of B. The final closure can instead call a proved bounded-class theorem directly on normalized compact packets.

The almost-AD, density, convex-Wolff and grid constants after each real construction must be absorbed in the chosen eta. The finite uniformity theorems alone do not prove the universal volume estimate.

## 4. Definition 17.2 output checklist

### Clause (1): actual almost-AD tube family

Use the actual coarse/refined/rescaled family from the carrier closure adapter: maximal-net populations or explicit cover-cell pruning; restored separated directions where the strict native class needs them; dense actual shadings and bounded graph normalization. Subsequent shading restrictions keep the tube backbone, including empty shadings, so they do not require falsely hereditary lower AD.

Convex-Wolff control is an additional conclusion of Proposition 18.2. It can be transported through the actual affine normalization with recorded constants, or regenerated from restored separated directions and a quantitative tube-count lower bound. No new Wolff certificate is introduced.

### Clause (2): times and the slope field

Time labels are actual fine grid bins, so they are separated. Aggregate shading density plus the bounded number of cells visited by one tube in one time bin gives |Z|>=c lambda/delta. Compatible tuple selection and the second bounded spatial-branch selection give a height-only plane representative with dyadic Lipschitz control on the prescribed scale list.

Use a finite coordinate-projection chart, rather than an arbitrary lattice-destroying rotation, to make the graph matrix bounded by a dimensional constant. Fixed dyadic coordinate normalizations then give the literal bounded coordinate ranges, with fixed-factor tube/cube enlargements recorded. All such constants are fixed before the mesh is chosen.

### Clause (3): exact slices, dense fibers, and both quotient AD clauses

The injective shear-floor map gives an explicit exact fiber representation of the auxiliary slice grid, with O(delta) movement and all original labels attached. Grain/ancestor/time multiplicity cancellation supplies the horizontal fiber lower population on the same final set.

The phase/time partition argument gives the actual horizontal slice AD counts. The lattice quotient lemma gives individual Y_z AD. The two-set rich-neighbor construction gives the AD of the ACTUAL coarse-height union at every required coarse mesh. Neither of these steps assumes the conclusion of Clause (3).

If the proposed exponent d−ell−kappa is negative, the dense fiber versus ambient upper count yields the finite-scale obstruction already recorded; one must rule out the fixed positive dimension gap by choosing the slack smaller, rather than announce a negative-dimensional AD set.

### Clause (4): this requires an additional direction-side caller

Spatial slice AD and a Lipschitz plane field do not alone give the projected direction sets, their AD counts, or the common offsets xi_q. Sections 5–7 give an actual construction of these from the existing local plane approximation and matched direction counts. It must be included before claiming Proposition 18.2's entire output.

## 5. A local anchor removes the apparent loss in the direction-graph error

Write the scale before final rescaling as epsilon=tau^2, with a good tuple wedge at least a>=tau. Work before horizontal rescaling inside one coarse T_tau. At a point p, let theta_0 be an ACTUAL incident fine direction in this coarse tube. Every other retained direction theta there satisfies

    |theta-theta_0| <= C tau.

Let the original stopping direction plane have graph slope f_Sigma. Original fine directions have normal error at most C epsilon in that plane. The witness-plane slope f_V satisfies

    |f_V-f_Sigma| <= C epsilon/a.

The compatible representative slope f_z satisfies |f_z-f_V|<=C tau at the final height-bin scale. In a fixed well-conditioned graph chart, write theta=(phi,psi). Subtracting the two direction equations cancels the affine intercept and gives

    |(psi-psi_0)-f_z(phi-phi_0)|
      <= C epsilon + C(epsilon/a+tau)|phi-phi_0|
      <= C(tau^2+tau^3/a+tau^2) <= C tau^2.

After the horizontal rescaling by 1/tau this is O(tau), the new physical mesh. Define the local offset from the RESCALED actual anchor by

    xi_p = psi_0' - f_z phi_0'.

Then every retained local direction obeys

    psi' = xi_p + f_z phi' + O(tau).                            (A)

Using a faraway global transverse-tuple direction as the affine anchor would give an unnecessary tau/a error. The local direction difference of size tau is what makes (A) sharp enough. The condition a>=tau follows from a=epsilon^v with v<1/2, for a sufficiently small starting scale.

The graph-chart claim is stable: the full stopping plane contains a graph vector with time component one and bounded norm, so its intersection with the horizontal hyperplane is uniformly transverse. Its closeness to the witness plane transfers to the horizontal graph slope with the stated C epsilon/a factor.

## 6. Coherent offsets from a separate RESCALED single-witness field

Apply the already proved compatible selection theorem to PHYSICAL POINTS, weighted by their full original incidence mass. Terminal witness states are all occupied fine angular cells at that point, not only one preselected tube.

At a point there are >=c A^(-1)delta^(-kappa) fine states. In a spatial rho_j-node the common angular menu has at most C A rho_j^(-kappa) states. Conditioned on its parent's angular state, the successor menu has at most

    C A(rho_j/rho_(j−1))^(-kappa)

states, by the earlier relative common-multiplicity estimate (113). The scale powers telescope. The theorem retains an A^O(J)-fraction of ORIGINAL point weight and supplies compatible actual angular witnesses.

Immediately retain the selected points and COMPLETE their original incidence fibers: keep all old incidences at those selected points. The fiberwise sum identity shows the retained weight is exactly the selected point weight. At this stage every stored witness is an actual retained incident tube. Completion occurs BEFORE the terminal self-uniform call; completing fibers afterward would not preserve its guarantees.

For a spatial rho-cube q choose one actual direction theta_q=(phi_q,psi_q) witnessing its selected angular state, and a fixed time reference z_q. Define

    xi_q = psi_q - f(z_q)phi_q.

For every surviving p in q, its terminal witness theta_p is in the same rho-angular cell as theta_q. It satisfies (A), and the already RESCALED slope field satisfies |f(z_p)-f(z_q)|<=C rho. Therefore

    |xi_p-xi_q| <= C delta+C rho+C|f(z_p)-f(z_q)| <= C rho.      (B)

No pre-rescaling Lipschitz constant is transported through 1/tau here. The witness field and calculation are in the rescaled configuration. Later terminal thinning preserves (A)–(B), even if the marked witness itself is no longer among the remaining incidences; the offset and the valid direction graph are already fixed from actual original witnesses.

An alternative finite count also bounds the number of occupied offset rho-cells in q by C A^2: each point contributes >=c A^(-1)rho^(-kappa) angular rho-cells near its offset; a fixed angular cell can lie near only O_d(1) offset cells, while the total common angular menu has <=A rho^(-kappa) cells. A compatible offset-cell selection would therefore also work. The separate actual angular witness field above is the primary route.

## 7. Projected directions and their AD counts

Prepare equivalence relations with labels (physical fine point, angular r-cell) for every required r before the terminal uniform call. Reference directional kappa-AD and point multiplicity bounds imply that the number of such classes is at most

    C A |P_ref| r^(-kappa).

If original incidence mass is at least u_0 A^(-1)|P_ref|delta^(-kappa), and the final retention fraction is r_keep, partition richness gives every occupied final class weight at least

    c r_keep u_0/(K_U A^2) (r/delta)^kappa.

Divide by the actual weight bound of one fine direction cell at a point. Together with inherited upper counts, this re-establishes kappa-AD of the FINAL incident direction sets. No lower direction count is assumed to survive an arbitrary earlier cut.

Project directions satisfying (A) onto their first ell−1 coordinates and take their actual delta-cells. A projected delta-cell has only O_d(1) direction cells above it because the residual is O(delta) and f is bounded. Projection is bi-Lipschitz up to O(delta) on this graph, so the projected set Phi_p is kappa-AD with fixed dimensional losses and the tracked profile factors. Each projected cell has an actual remaining tube witness; retaining its original mark is automatic.

For a coarse cube q, take the ACTUAL union of its incident angular rho-cells. Its upper local count inside an angular r-cell is at most C A(r/rho)^kappa by the pointwise relative form of (113). A single fine point witnessing any occupied angular cell, together with its fine kappa-AD set, supplies the lower covering count at scale rho. Thus the union is kappa-AD at mesh rho. By (B) it lies in the O(rho)-neighborhood of the common affine graph with offset xi_q and slope f(z_q). The same projection argument gives Phi_q.

Choose Phi_q as the full coarse projected-cell image. Nested angular grids then give the required inclusion Phi_p subset Phi_q^(rho) directly, rather than losing it by selecting an unrelated separated subfamily. Endpoint radii and lacunary interpolation carry the same explicit mesh-ratio losses as the spatial counts.

If kappa>ell−1, a delta-grid in R^(ell−1) cannot have the required kappa-AD population with arbitrarily small slack. Keep the corresponding finite-scale inequality and rule out a fixed gap; do not silently assume the exponent is in range. The source's ell=1 and ell=d exclusions still require their extremal/scale endpoint arguments, or the corresponding fully checked finite dimension-gap contradiction.

## 8. The first stronger-upgrade input and its quantitative order

**Lemma 5.3**, pp. 23–25, takes a delta-separated (delta,t,delta^(-eta))-AD set A, t in [0,d], with eta sufficiently small depending on zeta. It returns scales rho<tau with

    tau/rho >= delta^(-chi(zeta)),
    chi(zeta)=c zeta^[4 ceil(1/zeta)],

and a subset retaining at least (rho/tau)^zeta of A. After local affine normalization, it is nearly aligned: an s-AD family along parallel lines, a (t−s)-AD transverse quotient, and a tube Katz–Tao upper bound of exponent s. In the d=4, ell=2 branch this is applied to the actual two-dimensional Y_z, of dimension 2−kappa.

The new mesh Delta=rho/tau obeys Delta<=delta^chi. A loss delta^(-e) becomes at worst Delta^(-e/chi). Therefore an output loss budget b requires e<=c chi b. The explicit fixed-depth tuple losses A^O(J) are compatible with this order: choose working depth J from the DESIRED output spacing first, then choose input losses much smaller than chi b/J. Do not choose J≈1 divided by the already much smaller input eta.

Lemma 5.3 is not proved merely by citing our dense-fiber quotient lemma: its extracted line dimension s need not be one, and its nearly parallel alignment construction is substantive. The source first proves Lemma 5.2's concentration-scale stopping, then on p. 24 selects an interval of scales with slow angular-menu growth and a common direction occurring in many spatial boxes. Our finite common-menu selection is useful in that latter count, but the full geometric AD alignment caller remains to be implemented.

For ell=3 in d=4, Y_z is one-dimensional, so its AD upper bound already gives tube Katz–Tao control with gamma comparable to kappa (up to loss factors). The directional slab-Frostman upgrade is still needed: two-dimensional Phi_p can be concentrated near a line while being kappa-AD.

Proposition 18.1 Step 2 repeatedly lowers the linear dimension, with (144) supplying nonconcentration at the stopping dimension. Step 3 proves the two slope functions' approximate consistency and thickens to make it exact. These are additional geometric constructions, not conclusions of Proposition 18.2 alone.

For arbitrary continuous positive g,h in Proposition 17.2, choose the finitely many stopping thresholds first. The final gamma may be weakened to the minimum of the predetermined successful planarity threshold and a predetermined slab-Frostman threshold. Thus it ranges over a finite positive list. Choose fixed output loss budgets smaller than g at all relevant values; prepare their actual scale lists explicitly. Every dimension-raising or lowering step has a fixed positive power gap, and there are only dimension-many such steps. Choose initial losses small enough for all divisions by these gaps, and the original mesh LAST so every resulting scale is below the required h(output_eta,gamma). Literal dyadic scale lists must be included; their monotonicity is not automatic merely from increasing eta.

## 9. A complete next usable lemma: robust W-tuple counting

Lemma 19.1, p. 77, only needs the incidence properties (146) and the common coarse direction menu. It can be established before the stronger Frostman/planarity upgrade.

First, the local cardinal estimates need actual occupied-cell populations. Include labels (fine height, spatial rho-cell) in the terminal uniform call, or use an explicitly padded localization. Metric AD alone does not make every occupied unpadded dyadic slice cell dense. With those populations, if t=d−1−kappa,

    |E(q)| ≍ |Z(q)|(rho/delta)^t.

Let I be the number of actual point–tube incidences in q, P=|E(q)|, T=|T(q)|, and Z=|Z(q)|. Fine point direction counts give I≍P delta^(-kappa). A tube meets at most C_d points in one discrete height slice, so T>=I/(C_d Z). The common rho-direction menu and the fine carrier upper count give

    T <= C rho^(-kappa)(rho/delta)^(d−1).

These bounds yield the second relation in (146), and I≍Z T. No per-tube assertion of Z shaded heights is required.

### Exact finite path inequality

In ANY finite point–tube bipartite graph with P nonempty points, T nonempty tubes and I incidences, let N_path count ordered paths

    p -- T_1 -- p_1 -- T_2 -- p_2.

Repeated vertices/tubes are allowed, as in the source's definition. If d(T) is the point degree of tube T, then

    N_path = sum_(p_1) [sum_(T incident p_1) d(T)]^2
           >= [sum_T d(T)^2]^2/P
           >= I^4/(P T^2).                                    (C)

This uses only average tube degree. It repairs the tempting but unjustified inference that (146)'s average height count gives every tube approximately Z choices.

Group paths by their starting point p, middle height, terminal height, and terminal tube's angular c rho-cell, with c small enough that the cell diameter is <=rho. If at most M such angular cells occur, there are at most P Z^2 M groups. Ordered pairs of paths in one group give actual W-tuples, with the two terminal directions rho-close. Cauchy–Schwarz gives

    W_count >= N_path^2/(P Z^2 M)
            >= I^8/(P^3 T^4 Z^2 M).                           (D)

With I>=mu P and I>=lambda_T Z T, (C) gives

    N_path >= mu^2 lambda_T^2 P Z^2,
    W_count >= mu^4 lambda_T^4 P Z^2/M.

Taking mu>=delta^O(eta)delta^(-kappa), lambda_T>=delta^O(eta), and M<=delta^(-O(eta))rho^(-kappa) yields exactly Lemma 19.1's

    W_count >= delta^O(eta) |E(q)| delta^(-4kappa) rho^kappa |Z(q)|^2.

The source definition imposes NO distinctness of the five points or four tubes and NO nonzero time gaps. These degenerate walks remain in (C)–(D). Choose a FIXED half-open angular grid of side c rho, with c<=1/sqrt(d−1); then any two terminal directions in the same cell are rho-close, and refining a rho-menu to this grid costs only C_d. The map from an ordered path pair to the source's nine entries is injective: both intermediate points, both terminal points, the common starting point, and all four tube labels are retained. Its angular-cell label is uniquely recoverable from the terminal tube. There is no further geometric fiber loss.

Apply this to distinct GEOMETRIC point/tube incidences. Several old marks over one geometric pair remain attached metadata; counting them as different geometric W-tuples would be incorrect.

If a later argument explicitly needs distinct time levels, that must be a separate construction. With point degree at most M and at most C_0 points per tube per height, the number of paths for which any two of the three heights agree is at most 3 C_0^2 P M^2 Z. Compare this with the lower path count mu^2 lambda_T^2 P Z^2. If Z>=6 C_0^2(M/mu)^2 lambda_T^(-2), removing these paths retains at least half, and applying Cauchy again yields W-tuples with distinct heights. For a quantitative small-gap exclusion replace the single-level bound by an actual upper bound for the number of heights in that gap. Neither removal is part of Lemma 19.1 as stated.

The finite count is valid whenever these actual menus and populations exist; the source states rho>=delta^(1/4) for its later uses. It does not use slab-Frostman transversality. Original incidence marks can be carried along each path, but this newly counted path family is not automatically the old manuscript's original occurrence measure.

## 10. The next geometric payoff in Section 19

Claim 19.3, pp. 79–80, assumes actual W-related terminal tubes and a set of heights where the slope matrices differ by O(sigma), with rho^2<=sigma<=rho. In coordinates normal/tangential to the common slope plane, its elementary content is:

- terminal slope difference has tangential component O(rho) and normal component O(sigma), from (148),(153);
- terminal base-point difference has tangential component O(rho) and normal component O(rho sigma+delta), from (150),(152).

Over a bounded unit height interval, those bounds put both terminal tubes in comparable boxes of dimensions sigma^(d−ell) by rho^(ell−1) by 1. Thus their thickened boxes mutually contain one another after a fixed dilation. This claim needs no Frostman input.

Lemma 19.2 then iterates this relation. Its quantitative tube-population payoff uses the slab-Frostman exponent gamma to find transverse difference directions, and its conclusion is

    C_CW(T) >= delta^O(eta/gamma+epsilon) (rho/sigma)^kappa.

Our explicit losses must be made small compared to gamma and the intended contradiction exponent before this is useful. Fixed depth by itself does not provide gamma. The source's Lemma 5.3/stopping upgrade supplies it; this remains separate from the finite W-tuple count.

The original final theorem is unchanged throughout. Completing these local constructions still leaves the final cases in Propositions 17.3–17.5; neither W-counting nor Claim 19.3 alone closes the four-dimensional argument.

## 11. Checks

The coarse-union proof was independently re-read for lower-density inheritance, with the requirements recorded in section 2. A separate exact-integer test checked (C) and (D) on 500 finite incidence graphs, including uneven tube degrees and repeated path vertices. Every inequality and exact path-count identity passed. These are sanity checks, not a claim that the new geometry or W lemma has already been formalized in Lean.
