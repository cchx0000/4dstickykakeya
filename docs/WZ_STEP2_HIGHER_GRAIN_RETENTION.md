# Step 2: preserving higher grains during directional rank descent

Read-only mathematical continuation, 2026-10-03. Source: WZ Proposition 18.1, Step 2, pp. 75–76, equations (143)–(144), and Definition 17.4, p. 66. No repository changes or new Lean proof claimed.

## 1. The exact reference-menu count

Let the old geometric point set be P at mesh delta. Its higher horizontal grains have rank k-1, with original labels g (including the ORIGINAL fine height z). Assume every occupied original grain has at least

    g0 delta^(-(k-1))

DISTINCT points. Thus the number G of original grain labels satisfies

    G <= g0^(-1) |P| delta^(k-1).

Each grain lies in a bounded affine horizontal (k-1)-plane, with the existing bounded coordinate chart. Hence it meets at most C tau^(-(k-1)) working spatial tau-cells. This is an actual covering estimate for the original grain, independent of later shading restrictions.

Let I0 be the old ORIGINAL incidence labels. Allow a common reference label weight w0. The same-mesh point degree and conditional ancestor-degree bounds are

    total old mass >= w0 A^(-1) delta^(-kappa) |P|,
    mass over one point inside a fixed tau-ancestor
        <= w0 A (tau/delta)^kappa.

The original coarse ancestor menu in each occupied spatial tau-cell has size at most A tau^(-kappa). In the global-grains source this follows from the actual coarse projected direction cloud and its common affine offset: one angular tau-cell permits only a dimensional number of parameter-tube tau-cells through that spatial cell. It must be proved for the ORIGINAL incidence image used here; no post-cut AD inheritance is assumed.

Append to the ONE final incidence refinement the actual partition

    (old higher-grain label g, spatial tau-cell, tau-tube ancestor).

Its ORIGINAL menu cardinality is bounded by

    M <= C g0^(-1) |P| delta^(k-1)
                   tau^(-(k-1)) A tau^(-kappa).                 (1)

This is substantially smaller than multiplying by the total number of all tube ancestors. The local ancestor menu is the key count.

Suppose all earlier permitted selections together retain fraction r of I0, and the final self-uniform comparison factor is K. Its partition-richness theorem gives every occupied class at least

    c r w0 g0/(K A^2) (tau/delta)^(k-1+kappa)                  (2)

original incidence mass. Divide by the ACTUAL conditional per-point degree, not by one. The class then contains at least

    c r g0/(K A^3) (tau/delta)^(k-1)                           (3)

DISTINCT old points. No previously assumed lower grain population has been transported through the cut; (3) is newly proved on the final set from (1).

Including the tau-ancestor label is necessary if the global uniform call occurs before selecting the packet. A bare (grain, spatial cell) partition does not by itself control the subsequent restriction to one tube ancestor.

## 2. Actual coarse/rescaled point fibers

Take delta<=rho<=tau and the actual graph-tube rescaling

    (x,z) -> ((x-b0-z theta0)/tau, z).

The new tube mesh is sigma=rho/tau. On one original higher grain g, the height z is FIXED. The horizontal map is an affine homothety, preserving that grain's horizontal slope exactly.

The inverse image of one new sigma-grid cell has horizontal diameter O(rho). Since the original points in g are delta-separated in a bounded (k-1)-plane, it contains at most

    C (rho/delta)^(k-1)

of them. Dividing (3) by this actual geometric fiber bound yields at least

    c r g0/(K A^3) (tau/rho)^(k-1) = c r g0/(K A^3) sigma^(-(k-1))    (4)

DISTINCT new point cells. Every such point has an actual surviving incidence, provided all tube/point bin deletion steps have occurred BEFORE this final original-label refinement.

Formula (4) supplies a dense higher-grain witness whenever a final class is occupied. It remains valid when different old grains coalesce in a new image: it is a lower witness count, not an injectivity claim across grain labels.

## 3. The higher field need not be Lipschitz

Definition 17.4 does NOT require dyadic Lipschitz control of the higher field f-tilde, or a coarse-height-union AD clause for the higher quotient Y-tilde. Those conditions are imposed on the lower global-grains field f and its quotient in Definition 17.2.

Therefore it is not legitimate to replace all old f-tilde(z) in a new time bin by one representative and invoke the earlier bounded-slope-difference rich-neighbor argument without first proving that difference bound.

A constructive alternative keeps ONE ACTUAL old height in each retained new time bin. At that height all old higher grains use the same genuine f-tilde(z), so (4) gives dense parallel higher-grain witnesses without any unproved continuity of f-tilde.

## 4. Choosing actual old heights with the right new density

Prepare the partitions `(tau-ancestor, original fine height)` and `(tau-ancestor)` in the same final refinement. Original tube AD gives at most C K_T tau^(-(d-1)) tau-ancestors, and there are at most C/delta old fine heights. The reference total incidence density is at least lambda w0 delta^(-d), up to its already recorded AD constant.

Every occupied `(T_tau,z)` class therefore has at least a small-loss factor times

    w0 (tau/delta)^(d-1)

old incidences. A single rho-tube contributes at most C w0 K_T(rho/delta)^(d-1) such incidences at ONE fixed old height: its fine-tube population is bounded by carrier AD and each fine tube meets only a dimensional number of point cells at that height. Thus each occupied original height supplies at least

    small-loss factor * (tau/rho)^(d-1)

distinct NEW tube incidences.

The `(T_tau)` mass lower bound, divided by the corresponding fixed-height upper bound, gives at least a small-loss factor times delta^(-1) occupied old heights. A sigma-time bin contains at most C sigma/delta such heights, so at least a small-loss factor times sigma^(-1) bins are occupied. Keep one of three residue classes of time-bin indices and choose one actual old height in each remaining bin. The chosen heights are sigma-separated and every one has the preceding new-incidence lower bound.

Consequently the selected NEW configuration has dense shading at mesh sigma. This is change-of-mesh normalization; it is not a claim of a subpower retention fraction of ALL old fine-height incidences. Its incidence image retains a subpower fraction of the full coarse image because a sigma-tube has only O(sigma^(-1)) point bins, while both the new tube count and the selected incidence lower bound have the same mesh powers. This distinction is legitimate for the universal auxiliary theorem and would not be legitimate as an old-occurrence hereditary charge.

## 5. Keeping the reconstructed lower grains at those heights

Selecting an old height after an uncontrolled grain refinement could destroy its new horizontal fibers. Prepare the NEW lower-grain labels paired with the ORIGINAL fine-height label before the same final call as well.

There is a precise cancellation in the Step 6 geometry: adding the original fine height increases the reference class menu by at most

    new time mesh / old time mesh,

while fixing that old height removes that factor from the original-point-to-new-point inverse-image bound. In the actual square-scale construction, old mesh=tau^2 and new mesh=tau. A space-time ell-grain population tau^(-ell) becomes tau^(-(ell-1)) after adding the fine-height label; the former 1/tau time-collision denominator becomes one. The resulting new horizontal rank ell-1 population is unchanged.

This uses actual grid maps with fixed old height, not a generic inheritance principle. The old higher-grain labels already include that fine height; the newly constructed lower-grain labels must explicitly include it. All reference counts are computed before the final selection. Every occupied final grain-height class is then rich, so choosing a height retains its entire relevant class and preserves both families of witness counts.

## 6. Quotient AD and the remaining geometric callers

The full new horizontal slice AD counts must be obtained on these SAME selected old-height slices. The earlier phase/time proof adapts by using `(s-ancestor, original fine height, T_tau)` classes. There is no extra time-fiber divisor because the height is fixed. Its reference phase upper counts and the same-set conditional multiplicity profiles give exponent d-1-kappa by the same cancellation already used in Step 6.

Combining that full ambient AD with (4) allows the dense-fiber or nearby-rich quotient lemma to rebuild the higher quotient at each selected height. No lower AD of an arbitrary old shading restriction is asserted. At a fixed selected height the old higher slope is one genuine matrix, so the rich-neighbor comparison needs only the explicit O(sigma) quantization error, not any inter-height Lipschitz claim.

The native callers still must supply the actual common-plane field BEFORE coarse point identification, the exact phase/height menu estimates just stated, and the fixed-height bin maps. These are specific finite geometry/count tasks, not a final product certificate.

Finally, independent projection onto the newly reconstructed lower grains can move points O(sigma). The old higher-grain representation is initially retained up to that controlled error, with its original labels and dense witnesses. Exact simultaneous lower/higher representations require the subsequent Step 3 consistency correction. Two independently quantized representations cannot both be declared exact on the same final points without that correction.

## 7. Fine-height phase menus and the lower field's coarse-union clause

Here is the explicit denominator for the selected-height coarse-union argument. Use epsilon for the CURRENT old grid mesh, tau for the parent tube scale, and sigma=epsilon/tau for the new mesh in a PURE rescaling stage. If a previous thickening has occurred, epsilon is its actual point/tube incidence-image mesh; do not confuse it with the earlier finer mesh delta.

Let D=d-1, N_epsilon be the current old tube count, and W>=lambda w0 N_epsilon/epsilon the original incidence mass. At each epsilon<=s<=tau, carrier covering gives

    #T_s <= C K_T N_epsilon (epsilon/s)^D.

Append the partition `(s-ancestor, tau-parent, ORIGINAL epsilon-height)` to the same final refinement. Its original menu is at most

    C K_T N_epsilon (epsilon/s)^D / epsilon.                    (5)

The parent label has bounded multiplicity: it is uniquely determined for nested dyadic ancestors. For separate carrier nets, derive a dimensional bound from the fact that the support of one s-cluster meets only a bounded number of tau-separated parent centers; it is not the total number of all parents. The bound on the number of old heights is only O(1/epsilon). No lower occupancy or uniform height count inside a new bin is used.

After total retained fraction r and uniformity K_U, every occupied class in (5) has mass at least

    c r lambda w0/(K_U K_T) (s/epsilon)^D.                      (6)

Choose one original height globally for each new time bin and keep ALL final incidences at that height. Every occupied class (6) at a selected height survives completely.

For a new coarse mesh R in [sigma,1], put u=tau R. The old preimage of one coarse point/u-ancestor pair at a FIXED original height has weight at most

    C w0 K_T (u/epsilon)^D.                                    (7)

There is NO time factor in (7). A fine tube supplies only O(1) old point cells at that exact height, and its u-ancestor contains at most C K_T(u/epsilon)^D fine tubes.

Use the previously prepared SAME-SET conditional kappa profiles: a surviving fine point has at least A^(-1)(tau/s)^kappa distinct s-ancestors in its parent; a coarse R-point has at most A(tau/u)^kappa u-ancestors; and an S-ball has at most A(tau/s)^kappa s-ancestors, where s=tau S. These are the actual rescaled-configuration profiles from the Step 4 construction, preserved by preparing all required relations in the same final call. They are not asserted from arbitrary shading thinning.

For LOWER coarse ambient AD around a selected R-point, use the single selected old height of an actual witness point. Sum its distinct s-ancestor classes (6). Their points at this fixed height lie in a C S-ball after rescaling. Divide by (7) and the coarse point-degree upper bound. This gives, with conservative constants,

    #P_(R,I) intersect B(p,C S)
        >= c r lambda/(K_U K_T^2 A^3) (S/R)^(D-kappa).           (8)

For UPPER coarse ambient AD, use the pre-selection s-ancestor upper menu, the actual carrier descendant bound C K_T^2(s/u)^D, and the bounded number of R-point cells visited by a rescaled u-tube in one R-time interval. Every selected coarse R-point has the needed degree lower bound from one surviving fine point at its selected height, because the height choice kept that point's COMPLETE final incidence fiber. This gives

    #P_(R,I) intersect B(p,S) <= C K_T^2 A^3 (S/R)^(D-kappa).    (9)

Neither estimate requires an equal number of old heights in different new bins. Lower AD uses ONE selected-height witness; upper AD uses an inherited upper menu and a preserved whole point fiber. Grid and net ancestor overlap costs are fixed and must be included where maps are not literally nested.

The lower plane field is selected on the output time-bin tree before the height choice. Using those same sigma-grid output heights leaves all coarser dyadic ancestors unchanged. Restricting to occupied bins preserves its Lipschitz bounds. The chosen old height supplies its actual old higher plane to that output layer; snapping its time coordinate to the output grid changes tube incidence only by O(sigma), since rescaled slopes are bounded.

The dense lower-grain witnesses obtained using the fine-height partitions in section 5, together with (8)–(9), now satisfy the ACTUAL ambient hypotheses for the earlier two-set rich-neighbor quotient theorem. Applying it reconstructs the lower quotient's coarse-height-union AD clause. This uses the same selected final set and the lower field's proved binwise Lipschitz control; it does not require Lipschitz control of the higher field.

## 8. Pure rescaling, normalized density, and multiplicity

For pure rescaling, let the current old mesh be epsilon, the horizontal dilation be N=1/tau, and the new mesh sigma=N epsilon. At a fixed OLD height, the actual shear-bin map is injective on old spatial grid points. The square relation epsilon=tau^2 is unnecessary.

This injectivity is FALSE if one maps finer delta-data directly after an additional thickening to width rho>delta: fixed-height spatial fibers then have size comparable to (rho/delta)^(d-1). First pass to the actual rho-grid incidence image and set epsilon=rho, or retain that explicit spatial fiber denominator.

Choosing one global old height per output time bin with maximum retained incidence mass loses at most N in old incidence count. It preserves normalized total shading density, because sigma=N epsilon and the tube count is unchanged at the pure rescaling stage. It does NOT, by itself, preserve raw average multiplicity I/|P|: I_new>=I_old/N and |P_new|<=|P_old| would still allow a factor N loss.

Two correct multiplicity routes are available:

1. If the prepared old point degrees are K_point-comparable, the selection keeps whole point-incidence fibers and fixed-height projection is injective. Hence mu_new>=mu_old/K_point.
2. For a robust route without that comparison, perform the physical heavy-cell filter on ORIGINAL labels first. Let each retained new cell have at least m old points, let retained old incidences be at least I_old/2, and choose m>=c lambda N as in the proved heavy-bin construction. Apply the global old-height choice to those retained labels, then project. This gives I_new>=I_old/(2N), while its support lies in the heavy support, so |P_new|<=|P_old|/m. Therefore mu_new>=m/(2N) mu_old>=c lambda mu_old. If an intervening final uniform refinement retains theta, include theta in this bound.

The second route pays N exactly once. It does not first divide the heavy incidence count by N and then pay a second N for height selection: both operations are composed at the level of retained original labels, and the final fixed-height projection is injective.

Four hundred exact rational grid tests, including negative indices and nonintegral shears, checked that the square-scale bin map has inverse fibers at most N across an N-height time bin and at most one at fixed old height. The algebra proving the same assertion for general pure-rescaling N is identical. These are sanity checks, not kernel proofs.
