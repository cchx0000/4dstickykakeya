# Quantitative metric-AD coarse and rescaled closure

2026-10-03. Mathematical audit and constructive adapter. Primary source: Wang–Zakharov, arXiv:2609.22035, Definition 3.9 and Observations 3.2–3.4, pp. 17–19; Proposition 18.2 Steps 3–4, pp. 69–70.

## Result

Native carrier-ball AD lower bounds do NOT imply lower populations in every occupied dyadic ancestor. The following route avoids that inference:

1. Form maximal-net/Voronoi carrier clusters, whose populations have genuine two-sided bounds.
2. Derive O(K) coarse angular multiplicity from the cluster lower bound and the ORIGINAL fine direction separation.
3. Preserve original incidence through a heavy-cluster cut, an angular coloring, and an explicitly budgeted low-population pruning.
4. For local anisotropic rescaling, prune low-incidence new cubes before inflation. This controls the new union as well as the retained incidence, and gives the multiplicity transfer needed by extremality.

In the normalized bounded graph chart, the output AD constant is at most

    C K^3 (1+log(1/new_scale)) / lambda,

with density at least c lambda. No lower dyadic-cell population, rescaling certificate, or unknown charge is assumed. The conclusions about actual retained original incidence are stated separately from the new coarse tube count.

## 1. Starting data and native-chart normalization

Work first with finite graph parameters P={(a,b)} in a fixed bounded subset of R^3×R^3, represented by tubes around (b+t a,t), t in a fixed unit interval. Write n=|P|. Assume:

    |a_p-a_q| >= c_0 delta for distinct p,q,
    K^-1 (r/delta)^3 <= |P intersect B(p,r)| <= K (r/delta)^3

for delta<=r<=1 and p in P, with fixed-factor endpoint enlargements allowed. The phase set has bounded diameter after fixed normalization. Each tube has a cubical shading at scale comparable to delta. Normalize incidence by delta times its number of shaded fine cells, so each tube contributes at most a dimensional constant. Let I be total ORIGINAL normalized incidence and assume I>=lambda n, 0<lambda<=1. Extra original labels may be retained throughout. For weighted incidences the same proof works when each tube/cell occurrence has weight at most one; otherwise its explicit atom-weight upper bound must be included.

These data are obtained from the native actual cover packet as follows. For unit direction u, orthogonal offset v and u_4>=1/2,

    a=u_h/u_4, b=v_h-v_4 a,
    u=(a,1)/sqrt(1+|a|²),
    v_4=-(a dot b)/(1+|a|²), v_h=b+v_4 a.

On the fixed compact carrier and fixed marked-height window this change of parameters is bi-Lipschitz with a fixed constant. Thus metric ball AD estimates transfer with fixed-factor changes of radius, mesh, and K. The common slab and full fixed-height window are already supplied by `IsWangZakharovNativeFiniteInput` and the actual packet constructor.

A shading need not meet the common INNER slab. To normalize its time interval, partition the fixed full height window into a bounded number of fixed-length intervals and keep a largest ORIGINAL-incidence interval. Use graph tubes over that interval, permitting an extension of a representative central line while retaining only the selected original shading incidences. Direction counting supplies convex-Wolff for these fixed-length graph tubes. All original marked segments remain labels, and the new shadings remain within the explicitly enlarged image of the original physical target. This is an auxiliary graph-tube construction, not an assertion that extended segment endpoints were in the original front.

Important scope: a fixed horizontal-offset bound is available for the ACTUAL packet from its compact ambient carrier. The public native finite-input definition does not itself explicitly bound horizontal offsets. To claim a universal closure statement for that entire public type, one must supply a uniform localization/normalization argument or use a bounded graph-tube auxiliary class. This note does not silently identify fixed-height normalization with bounded phase coordinates. All constants below are uniform in the bounded auxiliary class; fixed actual-ambient constants can be absorbed because the packet mesh is selected afterward.

## 2. Genuine cluster populations

Fix 2delta<=rho<=c, with c a fixed small chart constant. Choose a maximal rho-separated set C subset P in the carrier metric. Assign every p to a closest center, breaking ties by a fixed ordering. Write P_c for the resulting Voronoi cluster.

Then

    P intersect B(c,rho/2) subset P_c subset P intersect closedBall(c,rho).

The first inclusion uses an open rho/2-ball, so ties cause no difficulty. Consequently

    c_d K^-1 (rho/delta)^3 <= n_c:=|P_c|
                              <= C_d K (rho/delta)^3.             (1)

The clusters are disjoint and partition P. This is a population theorem proved from metric AD, unlike an unsupported assertion about unpadded dyadic cells.

The center set itself is metric (rho,3,C K²)-AD. For R>=4rho, compare P in B(c,R-rho) and B(c,R+rho) with the disjoint clusters whose centers lie in B(c,R), and use (1). For rho<=R<4rho the lower bound follows from the center itself; the upper bound follows from the same population estimate. Fixed large radii are handled by the bounded chart and global cardinality. This proves the metric analogue of WZ Observation 3.3.

A covering fact used below follows directly from the ORIGINAL P: the number of occupied phase grid cells of side R, R>=rho, is at most

    C_d n K delta³ R^-3.                                          (2)

Proof: a maximal R-separated net has disjoint R/2-balls, each carrying at least c K^-1(R/delta)^3 original points. It therefore has at most C n K(delta/R)^3 centers. Each net ball meets boundedly many grid cells. This proof assumes no cell lower bound.

## 3. O(K) coarse direction multiplicity

Fix an angular ball of radius A rho. If c is a coarse center in it, every point of P_c has slope in the corresponding (A+C)rho-ball. Fine direction separation bounds the total number of original points in that angular ball by C_A(rho/delta)^3. Divide by the disjoint cluster lower population in (1). Thus

    #{c in C: |a_c-a_*|<=A rho} <= C_A K.                          (3)

This is the requested actual multiplicity estimate. Its input is the Voronoi population theorem, not a conjectured dense dyadic ancestor.

Connect centers whose slopes are closer than L_0 rho, where L_0 is a fixed constant large enough for the chosen tube-thickness convention. By (3), the graph has degree O(K), hence an elementary greedy coloring with J<=C K colors. Each color has L_0 rho-separated slopes.

## 4. Coarse shading construction and mass-preserving branch choice

Let I_c be the ORIGINAL normalized shading incidence on P_c. Remove clusters with

    I_c < (lambda/2)n_c.

Their total incidence is at most lambda n/2<=I/2. Every remaining cluster is heavy. Define its coarse shading by the rho-cubes corresponding to its actual fine shaded points. In a fixed graph chart, each cluster's fine tubes stay within C rho of its center line throughout the time interval.

Equivalently, one may project the retained fine points to the center line at the SAME height, then use comparable rho-cubes. This moves points by at most C rho and records the target inflation. It avoids pretending that a cube of side rho around a nearby fine line is automatically inside a too-thin coarse tube. Choose a fixed physical thickness and cell mesh for which the ordinary cube/tube containment is valid, and color directions at that physical thickness. All these factors are fixed.

The normalized coarse shading size J_c is at most C, and

    I_c <= C n_c J_c.

Thus every heavy coarse shading has J_c>=c lambda. Its density is genuinely large. This bound comes from the original fine shading/time mass and the cluster population; the coarse tube is not given an invented full shading.

Among the J coloring classes select one maximizing sum I_c. It retains at least c I/K original incidence. Keep all original occurrences belonging to those selected clusters, with their original weights and all labels. This does not resample their old targets.

Coarse shading incidence and original incidence are different quantities. The following bound tracks both. Let J_all be the sum of coarse shading sizes before the heavy cut. Since J_all<=C|C|<=C n/n_min and J_selected>=c I_selected/n_max, (1) gives

    J_selected >= c lambda K^-3 J_all.                            (4)

A large retained ORIGINAL-incidence color is therefore also a subpower-retaining coarse-shading color when K and lambda^-1 are subpower. It need not retain half of the coarse shading count.

## 5. Renewed AD by actual low-population deletion

The selected angular color need not inherit any lower AD bound. Repair this constructively.

Choose finitely many phase grids at geometric scales R from rho to the fixed chart size. Their number is L_rho<=C(1+log(1/rho)). Repeatedly delete an occupied grid cell when its current center population is less than

    a (R/rho)^3,

for a small a>0 fixed below. Each original cell can be charged only once: when it triggers, all of its current contents are deleted. At that scale, the number of possible charged cells is bounded by (2). Therefore at most

    C a n K delta³ rho^-3 L_rho

coarse centers are deleted in total. Each deleted center carries original incidence at most C n_max<=C K(rho/delta)^3. The total ORIGINAL-incidence loss is consequently at most

    C a n K² L_rho.                                               (5)

Choose

    a=c lambda/(K³ L_rho),

with c sufficiently small. Since the selected color carries at least c'lambda n/K, (5) is at most half of that selected original incidence.

At termination every occupied grid cell has the stated population. A cell containing a point, chosen at side length comparable to r and small enough to fit inside its r-ball, supplies the lower metric AD bound. At radii within a fixed factor of rho, use the point itself and a<=1. The upper metric bound follows from the separated directions and is C(r/rho)^3. Thus the actual surviving center family is

    (rho,3, C K³ L_rho/lambda)-AD.                                (6)

Every retained coarse center was heavy and its shading was untouched, so shading density remains >=c lambda. The original incidence retained by the complete coarse construction is >=c I/K. The coarse shading incidence retained is >=c lambda K^-3 J_all, by the same proof as (4) using the final retained original mass.

Finally its cardinality is at least I_retained/(C n_max), and n delta³>=c K^-1. Hence

    |C_final| >= c lambda K^-3 rho^-3.

Separated-direction convex geometry gives

    C_CW(C_final) <= C K³/lambda.                                 (7)

The repository's proved `separated_directions_convex_geometric_count` and normalization theorem are precisely the type of result needed for this last step. This completes coarse admissibility, including the AD repair and the exact mass ledger.

## 6. Local restriction and anisotropic rescaling

Fix ANY heavy Voronoi cluster P_c. Its original shading incidence satisfies I_c>=(lambda/2)n_c. Put sigma=delta/rho and apply the explicit physical affine map

    F_c(x,t)=((x-b_c-t a_c)/rho,t).

Its graph parameters are ((a-a_c)/rho,(b-b_c)/rho), in a fixed bounded box. Original fine directions become c sigma-separated, and the rescaled tube width is comparable to sigma. Original incidence labels are transported bijectively.

The restricted cluster's lower AD is NOT automatic. However its total count is >=c K^-1 sigma^-3, its upper counts inherit K(r/sigma)^3, and the number of occupied rescaled carrier cells of side r is at most C K² r^-3. To prove the last assertion, select r rho-separated original points of P_c, use ORIGINAL P lower counts in disjoint r rho/2-balls, and bound their union by ORIGINAL P inside B(c,C rho). No lower bound on P_c's boundary balls is used.

Before renewing AD, address a second issue: anisotropic images of fine delta-cubes have time thickness delta, whereas a sigma-cubical shading has time thickness sigma=delta/rho. Blindly filling them can cost rho^-1 in union size, which is unacceptable for extremality.

### Rich-cube pruning controls this inflation

Assign every original physical fine delta-cell to the sigma-cube containing its transformed representative point. Use this assignment consistently for all tube incidences through that same physical cell. Fixed enlargements handle cell boundaries and the bounded affine shear.

Each rescaled tube meets at most C/sigma possible new cubes. Each new cube receives at most C/rho fine cells from any single fine tube. Discard a tube/new-cube pair when it contains fewer than

    theta/rho original shaded fine cells, with theta=c lambda.

For small enough c, the total discarded ORIGINAL incidence is at most half I_c: there are at most C n_c/sigma pairs and delta*(theta/rho)*(C n_c/sigma)=C theta n_c. This is an actual deletion of incidences with unchanged weights. For weights <=1, the same weighted threshold works.

Now every surviving new shaded cube contains at least theta/rho distinct ORIGINAL fine physical cells, witnessed by one surviving tube. Therefore

    |U_new|_sigma <= C (rho/lambda) |U_old|_delta.                 (8)

This is a union estimate, not merely an incidence estimate.

### Renew local AD while preserving the rich cubes

Delete low-population rescaled carrier grid cells exactly as in section 5. There are at most C K² r^-3 cells at scale r, so a lower threshold a(r/sigma)^3 deletes at most C a K² L_sigma sigma^-3 tubes. Each tube carries at most C original normalized incidence. Since n_c>=c K^-1 sigma^-3 and at least c lambda n_c original incidence survived the rich-cube cut, choosing

    a=c lambda/(K³ L_sigma)

preserves at least half of that remaining incidence. Delete entire tubes at this step, leaving all rich shading pairs on surviving tubes untouched. Consequently (8) remains valid.

The final family has

    AD constant <= C K³ L_sigma/lambda,
    C_CW <= C K/lambda,
    shading density >= c lambda.

It retains at least a fixed fraction c I_c of ORIGINAL incidence. Its new sigma-incidence count satisfies

    I_new,sigma >= c rho I_old,delta,

because a new tube/cube pair holds at most C/rho original cells. Combining with (8) gives the crucial multiplicity transfer

    mu_old(P_c,Y) <= C lambda^-1 mu_new.                           (9)

Thus a universal upper multiplicity estimate on the actually constructed rescaled family gives an upper estimate on the original cluster, with only lambda^-1 loss. This closes the otherwise hidden rho^-1 inflation problem.

For the coarse family, (4) and union inclusion similarly transfer an upper multiplicity estimate back with at most C K³/lambda loss, provided coarse shadings are compared at the same fixed-factor scale. These are the comparison statements needed in the extremal argument, not just assertions that some admissible family exists.

## 7. Exact scale ranges and exponent bookkeeping

Let the initial bounds be K<=delta^-eta_K and lambda>=delta^eta_lambda. Fixed constants and logarithms can be absorbed into delta^-zeta for every chosen zeta>0 once delta is sufficiently small.

For coarse output at scale rho, require rho<=delta^c. Then

    delta^-a <= rho^(-a/c).

For rescaled output at sigma=delta/rho, require sigma<=delta^c, equivalently rho>=delta^(1-c). To obtain BOTH simultaneously, use

    delta^(1-c) <= rho <= delta^c,    0<c<=1/2,

together with the harmless fixed-factor condition rho>=C delta.

The AD/CW constants above are then controlled at their respective new scales by exponent

    eta_new=(3 eta_K+eta_lambda+zeta)/c.

The density c lambda is at least the corresponding new-scale power with exponent (eta_lambda+zeta)/c. Coarse original-incidence retention c/K and coarse shading-incidence retention c lambda/K³ are also explicit subpower losses. With eta_K=eta_lambda=eta, the main constant loss is (4eta+zeta)/c.

These are power-separated scale requirements. One cannot treat rho near 1, or delta/rho near 1, as if delta^-eta were a small loss in that new scale. Such endpoint regimes need their own trivial bounds or a different choice of scales, exactly as in WZ's extremal construction.

The fixed common graph length and bounded chart changes contribute constants only. They must be fixed before choosing the sufficiently fine original packet. Any dependence of those constants on the hypothetical input family must be accounted for in a universal auxiliary-class statement.

## 8. What is closed, and what is not

Closed here as a mathematical construction:

* native metric-AD data in a fixed graph chart -> genuine cluster populations;
* coarse metric AD and O(K) angular multiplicity;
* actual incidence-preserving direction selection and renewed AD;
* dense coarse and rescaled shadings;
* subpower transfer of old multiplicity, including control of anisotropic cubical inflation;
* explicit power-separated conversion of all losses to the new scale.

These arguments do not yet appear as a combined Lean adapter. The scalar thresholds, finite partitions, original-incidence restrictions, and metric covering counts should be constructed explicitly; (6) and (9) must not be introduced as certificate fields.

Still separate: normalization of the unrestricted public native input type to a uniformly bounded auxiliary class; compatibility of the different refinements with the particular self-uniform family used for the matched lower bounds; the global infimum/near-extremizer Lean construction; and the transverse-tuple/grain geometry in Proposition 18.2 Step 5. No arbitrary marked old-edge charge follows merely from the new coarse shadings. The actual original compact front theorem remains unchanged.

## 9. Sharper direct grid callers for the rich-bin lemma

The separately formalized finite heavy-bin transfer works with a globally consistent old-cell -> new-cell map. Its two numerical hypotheses have particularly elementary physical callers here.

**Exact global fiber bound.** Use old half-open delta-cell centers, F_c as above, new half-open sigma-cubes, and rho=1/N dyadic so sigma=N delta. A new time interval contains exactly N old time-center levels. At each such time, a new cube's horizontal preimage is a translated half-open box of side rho sigma=delta, which contains exactly one old grid center per coordinate. The full-grid map therefore has exactly N preimages for each new cube; on the actual finite old cells its fiber size is at most

    L=N=1/rho.

This bound does not require tube geometry or a determinant estimate.

**New bins per tube.** After F_c, old shaded-cell centers lie within E sigma, coordinatewise, of a graph with slope norm at most one. In any new time interval of length sigma, each horizontal coordinate ranges over an interval of length at most (1+2E)sigma. Its floor index has at most ceil(1+2E)+2 possibilities. The time interval has length O(1), hence O(1/sigma) bins. Thus

    M <= C_(d,E)/sigma.

For d=4, E=4 and a normalized unit time interval with fixed endpoint padding, 6912/sigma is a safe explicit bound. The exact numerical constant is immaterial but must be fixed before delta is chosen.

Choosing the integer heavy threshold m=ceil(theta L), theta=c lambda, avoids any assumption theta L>=1. Since m-1<theta L, the discarded count is <=theta L M n. Since m>=theta L, the new-union bound old_U/m still gives the desired C rho/lambda factor. This is valid also when m=1.

## 10. Convex-Wolff constants and refinement compatibility

Keep input metric-AD K and input convex-Wolff C_W conceptually separate. The bound (7) REGENERATES convex-Wolff from the output's restored separated directions:

    #C_final(U) <= C rho^-3 volume(U),
    N' >= c lambda n delta³/(K² rho³),
    C_W,out <= C K²/(lambda n delta³) <= C K³/lambda.

It does not assume C_W=1 and does not use the input C_W estimate. If one instead works in WZ's broader class without fine direction separation and transports its original convex-Wolff estimate, the corresponding bound is C C_W K³/lambda (K^4/lambda when C_W=K). The angular-coloring argument in this note explicitly uses the native direction separation, so it does not silently prove closure for that broader class.

For the global near-extremizer, keep the original fine tube family P as its AD backbone when deleting incidences. The native definition permits empty shadings. Thus fine AD and direction separation remain unchanged, while shading density and near-extremal multiplicity lose only the tracked incidence fraction. Coarse and rescaled retained families can be constructed as auxiliary witnesses for upper bounds and transferred back by (4) and (9). Dropping all zero-shading tubes prematurely would create an avoidable lower-AD obligation.

## Formal status at this checkpoint

See [WZ_LOCAL_GEOMETRY_PROGRESS.md](WZ_LOCAL_GEOMETRY_PROGRESS.md) for the exact
proved module boundaries and remaining handwritten geometric adapters. The
final finite volume theorem and the original main theorem are not completed.
