# WZ Step 6: coarse-height quotient unions from the actual incidence image

Handwritten mathematical audit, 2026-10-03. Primary source: Wang–Zakharov, supplied arXiv:2609.22035 PDF. The required conclusion is Definition 17.2(3), printed p. 65: for an occupied coarse height interval of size rho, the union of its Y_z is AD at mesh rho, with dimension d−ell−kappa. The relevant Step 6 inputs are (127)–(129), pp. 72–73, the coarse counts in (132)–(135), p. 73, and the quotient estimates (136)–(140), pp. 73–74.

This note constructs that caller using the actual coarse incidence IMAGE. It does not infer the conclusion from the AD regularity of individual fine slices. It also avoids the incorrect assertion that every coarse quotient cell inherits a dense fiber.

All retained occurrences keep their original labels and weights. Auxiliary coarse point representatives move by O(rho), with their original targets recorded. The requested quotient union itself is counted without pruning or replacement. This is the alternate universal finite-volume route, not an old-root hereditary charge.

## 1. Fine data and the actual coarse maps

Let tau be the fine mesh of the already constructed rescaled configuration, D=d−1, k=ell−1, n=d−ell, and t=D−kappa. Fine physical points and tube incidences come from the actual final shading. Its fine tube backbone T has N tubes and metric carrier AD constant K. Geometry uses bounded graph slopes in a fixed bounded slab.

Let Omega be the original retained label set, with physical point p(omega), fine tube T(omega), and original integer weight. One actual geometric fine pair (p,T) has total original weight at most u_0. The total retained weight satisfies

    W >= lambda u_0 N/tau.

For the native packet u_0=1 at the geometric incidence level. If original finer labels have already been grouped, equality of the fine point/phase-pair map is included in the terminal uniform refinement; its common fiber mass is the unit u_0, with its comparison factor absorbed into A and lambda. This is an explicit weight-to-geometric-pair conversion.

For dyadic tau<=rho<=s<=1 define:

- q_rho(p): the actual half-open rho-spacetime cell containing p;
- c_rho(T): the actual rho-phase ancestor of the fine tube;
- z_rho(p): the actual half-open rho-time interval containing p.

The coarse incidence set is the DISTINCT finite image

    I_rho = {(q_rho(p(omega)),c_rho(T(omega))): omega in Omega}.       (1)

No multiplicity of original labels is interpreted as several coarse incidences. Keep the full inverse-image label list and original weight over every member of (1).

Over one time interval I of length rho, let P_(rho,I) be the spatial rho-cell representatives occurring in (1). This is the actual coarse horizontal support whose AD bounds will be proved.

Use standard dyadic time labels throughout. A Voronoi spatial localization of diameter O(rho) can meet O(1) time bins; split by z_rho explicitly or include that label in the partition. A one-time-bin assertion is made only after this actual split.

## 2. Geometry of the image fibers, including endpoints

A single fine bounded-slope tau-tube visits at most C_d rho/tau fine point cells inside a rho-spacetime cube. This follows from O(rho/tau) tau-time bins and O_d(1) spatial tau-cells in each bin. It remains true for the injectively shear-quantized fine points: they are still tau-separated and lie in fixed enlargements of the original tubes.

An occupied rho-phase cell contains at most C_d K(rho/tau)^D fine tubes. Therefore every coarse pair in (1) has ORIGINAL inverse-image weight at most

    U_rho = C_d u_0 K(rho/tau)^(D+1).                            (2)

This is the precise denominator used below. It is neither one nor the number of coarse points. If pair-fiber uniformity is also included in the terminal call, all occupied pair weights are comparable to their maximum, but the proof below needs only the actual upper bound (2).

The fine carrier lower AD estimate gives

    # occupied s-phase ancestors <= C_d K N(tau/s)^D.             (3)

It also gives the local coarse-cell bound

    # rho-phase ancestors inside one s-phase ancestor
       <= C_d K^2(s/rho)^D.                                    (4)

For (3), take a maximal s-separated net of actual fine carriers. Its disjoint small balls each contain at least c K^(-1)(s/tau)^D fine carriers; sum these populations and cover the net balls by O_d(1) s-phase cells. For (4), take a maximal rho-separated net among fine carriers in the s-parent. Their disjoint small balls, even when crossing that parent's boundary, lie in its fixed enlargement. Lower counts at radius rho and an upper fine count at radius O(s) give K^2(s/rho)^D. Each net ball meets only O_d(1) rho-phase cells.

For rho<4tau or s<4tau, use the trivial injection of occupied cells into their fine witnesses and the fine upper count; the ratio is then bounded by a dimensional constant. No lower population of every occupied unpadded dyadic phase cell is assumed. The bounds concern the number of cells, not each cell's individual population.

## 3. Same-final-set phase/time populations

Include, for EVERY required pair rho<=s, the fixed equivalence relation

    omega ~_(s,rho) omega' iff
      c_s(T(omega))=c_s(T(omega')) and
      z_rho(p(omega))=z_rho(p(omega')).

These are O(m^2) additional partitions for m working scales, prepared before the single final self-uniform call. Let their comparison factor be K_H.

The image of this map has at most

    C_d K N(tau/s)^D / rho

classes, by (3) and the bounded time slab. `partition_richness_of_self_uniform` therefore gives, for every OCCUPIED class (R_s,I),

    weight{omega:c_s(T(omega))=R_s, z_rho(p(omega))=I}
       >= c_d lambda u_0/(K K_H) (s/tau)^D (rho/tau).             (5)

All counts in (5) refer to the final labels. An arbitrary earlier slice AD estimate is not transported through a later shading cut.

The earlier common multiplicity construction supplies concrete bounds, with A>=1:

- each occupied fine point carries at least u_0 A^(-1)tau^(-kappa) original weight;
- weight at one fine point inside a fixed s-phase ancestor is at most u_0 A(s/tau)^kappa;
- at most C_d A r^(-kappa) r-phase ancestors shade a physical r-spacetime cube, for every working r.

The first bound is re-established on the final set by its point-fiber relation and tracked total retention. The two upper bounds are inherited from the original common-multiplicity configuration because labels are only removed. They are the concrete incidence forms of (111)–(113), not a substitute name for the desired coarse AD conclusion.

A single occupied fine point consequently has at least

    A^(-2)s^(-kappa)

distinct incident s-ancestors. In particular every occupied coarse rho-point cell has at least A^(-2)rho^(-kappa) incident rho-ancestors, because it contains one such fine point. Its upper coarse degree is at most C_d A rho^(-kappa).

## 4. AD of the full coarse horizontal support

Fix an occupied rho-time interval I and one coarse point cell Q in P_(rho,I). Choose an actual retained fine point p in Q.

### Lower bound at radius s

There are at least A^(-2)s^(-kappa) s-ancestors incident to p. For each, (5) supplies original incidence weight in the SAME rho-time interval. All those points lie within horizontal distance C_d s of p, because they share an s-phase cell and their heights differ by at most rho<=s.

The different s-ancestors give disjoint original incidence classes. A single coarse rho-point cell can hold at most

    U_rho times (C_d A rho^(-kappa))

of that original weight: use (2) for each distinct coarse point/phase pair, then the coarse point-degree upper bound. Dividing gives

    # [P_(rho,I) intersect B(Q,C_d s)]
       >= c_d lambda/(K^2 K_H A^3) (s/rho)^(D−kappa).            (6)

Both denominators are explicit: original weight per coarse PAIR, followed by the number of coarse PHASE pairs at one coarse POINT.

### Upper bound at radius s

At most C_d A s^(-kappa) s-ancestors meet the horizontal s-ball in the interval I. This uses only O_d(1) physical s-cubes; the dyadic time containment follows from rho<=s and nested grids.

Each s-ancestor contains at most C_d K^2(s/rho)^D rho-ancestors by (4). A rho-tube visits at most C_d rho-point cells in a single rho-time interval. Thus the number of distinct coarse incidence pairs meeting the ball is at most

    C_d A K^2 s^(-kappa)(s/rho)^D.

Every occupied coarse point has at least A^(-2)rho^(-kappa) such pairs. Divide to get

    # [P_(rho,I) intersect B(Q,s)]
       <= C_d A^3 K^2 (s/rho)^(D−kappa).                        (7)

This upper bound counts the actual image (1), not its original weighted preimage.

Using a nearby smaller working radius in (6), and handling the bottom endpoint by nonemptiness/grid packing, proves that P_(rho,I) is (rho,t,K_coarse)-AD with

    K_coarse <= C_d R_mesh^D K^2 K_H A^3/lambda.                 (8)

Here R_mesh is the maximum successive ratio in the prescribed finite scale list. If all dyadic radii are available it is fixed. For a lacunary list, its power must be retained. This bound is uniform in rho; there is no extra power loss depending on tau/rho.

The same proof also works after the coarse representatives have moved by O_d(rho), with fixed changes of constants. For physical radii beyond one, use a fixed bounded-domain cover to extend only the needed UPPER estimate; do not request the fine AD hypothesis outside its stated range.

## 5. The varying fine planes and the actual requested quotient union

The fine, same-final-set slice representation is

    A_z = {(x,y+f_z x): y in Y_z, x in X_(y,z)},

with x on the common translated tau-lattice, ||x||_infinity<=B, ||f_z||_infinity<=F, and

    |X_(y,z)| >= lambda_f tau^(-k)

for every occupied fine fiber. The same-final-set construction in the previous note obtains this density from the fixed grain/ancestor/time partitions.

For the occupied rho-height interval I choose an actual reference value f_I=f_(z_*) fixed before terminal refinement. Height compatibility gives

    ||f_z-f_I||_infinity <= L rho

for all surviving z in I, where L is a fixed controlled constant. The reference z_* need not remain in the final set; its original witness and the bound are fixed beforehand.

Define the REQUESTED coarse union as the actual finite rho-cell set

    U_I = D_rho (union_(z in I) Y_z).

Use its rho-grid representatives. Do not replace U_I by a rich subset.

Take the actual coarse physical grid points P_(rho,I), apply the already proved injective shear-floor map with slope f_I, and let V_I be its full quotient-coordinate image. This produces a full ambient set

    A_I^hat = {(x,b+f_I x): b in V_I, x in X_b^I}.

By (8), injective bounded movement, and the fixed chart shear, its unsheared coordinates are (rho,t,C_(d,F)K_coarse)-AD. The old physical coarse grid points are distinct; the shear-floor step contributes no duplicate vertices.

## 6. Bounded displacement of the two quotient sets

For an original fine point (x,y+f_z x,z), let (x_rho,v_rho) be its physical rho-grid representative, and let

    b = rho floor((v_rho-f_I x_rho)/rho).

Then

    |b-y|_infinity <= (2+kF+kBL)rho.

The terms come respectively from the physical normal-coordinate rounding, residual-coordinate flooring, the x-rounding in f_I x, and the change f_z-f_I. With eta=rho floor(y/rho), enlarge the constant once more to obtain

    |b-eta|_infinity <= E rho,
    E = 3+kF+kBL.

Thus U_I and V_I have mutual distance at most E grid cells. Each assignment between neighbors has at most

    M = (2 ceil(E)+1)^n

preimages, by actual integer-grid packing. This is a cardinality statement about quotient cells, independent of original incidence weights.

Use the actual half-open time label I throughout. At a boundary, a fine point belongs to exactly one I; no adjacent interval is silently included. Normal-coordinate floors and negative integer indices are treated by the same floor identities as the certified shear map.

## 7. Every original coarse cell has a rich NEIGHBOR

Fix eta in U_I and choose one actual fine fiber (y,z), z in I, witnessing it. The translated tau-grid has exactly (rho/tau)^k possible fine x-coordinates in one half-open rho-x-cell, because rho/tau is an integer. Hence the fine fiber occupies at least

    lambda_f rho^(-k)

distinct coarse x-cells.

For all those points, the common-slope coarse quotient b lies within E rho of eta. There are at most M possible b-values. Therefore some neighboring b in V_I has

    |X_b^I| >= (lambda_f/M) rho^(-k).                           (9)

Choose one such neighbor h(eta). The map h:U_I->V_I has fibers of cardinality at most M, since h(eta) is within E grid cells of eta. Its image consists of genuinely rich fibers of the FULL ambient A_I^hat.

This does NOT assert that eta itself carries a rich fiber. Exact boundary test: tau=1/64, rho=1/8, k=n=1, a fine fiber y=−tau with all x in [0,1]∩tau Z, f_I=0 and f_z=rho. Its original coarse quotient cell is −1. The common-slope coarse image has only one x-bin over −1, but eight over its neighbor 0. The witness cell is sparse and its neighbor is rich.

No point or label is discarded in this construction. The assignment is used only to prove the count of U_I.

## 8. AD of the original coarse union, using full ambient bounds

Assume beta=t−k=d−ell−kappa>=0. Let K_A=C_(d,F)K_coarse.

**Upper bound.** If eta' lies within radius r of eta in U_I, then h(eta') lies within r+E rho of eta in V_I. Bounded assignment multiplicity gives an extra factor M. Above each such rich quotient cell, (9) supplies at least (lambda_f/M)rho^(-k) points of the FULL ambient A_I^hat.

Cover the bounded x-domain by O(r^(-k)) r-boxes and apply the full ambient upper AD estimate in each nonempty product box. Exactly as in the certified quotient upper lemma,

    # [U_I intersect B(eta,r)]
       <= C_(d,F,L,B) K_A/lambda_f (r/rho)^beta.                (10)

No lower AD bound on the restriction to rich fibers is used.

**Lower bound.** The full ambient lower AD estimate and the trivial local x-fiber upper bound give a lower quotient count for V_I, even if its individual fibers are sparse. Choose a point of V_I within E rho of eta, take an inner ball, and map each of its quotient cells back to a nearby actual U_I cell. This reverse assignment also has multiplicity at most M. For r>=4(E+1)rho, this gives

    # [U_I intersect B(eta,r)]
       >= c_(d,F,L,B) K_A^(-1) (r/rho)^beta.                   (11)

For rho<=r<4(E+1)rho, nonemptiness and grid packing supply the bounds with fixed E-dependent constants. Thus the original U_I is

    (rho, d−ell−kappa,
       C_(d,F,L,B) R_mesh^D K^2 K_H A^3/(lambda lambda_f))-AD. (12)

This is exactly the coarse-height union clause, on its actual occupied rho-cells.

For the integer-grid formalization, the ambient upper lemma may be called through radius 2(N+C) after a neighbor shift C. If only upper radii through 2N are stated, first extend the upper estimate using the fixed bounded-domain total count, or split the large-radius endpoint explicitly. At coarse meshes with N<4(C+1), the entire bounded quotient domain has only O_(d,F,L,B)(1) cells, so AD follows directly from nonemptiness and grid packing. Such large-mesh endpoints cannot be omitted because Definition 17.2 includes rho up to one.

If beta<0, retain the earlier finite-scale obstruction from the dense fine fibers, rather than declaring a negative-dimensional AD set. It gives k−t<=log(C K_slice/lambda_f)/log(1/tau); a fixed positive gap is ruled out by choosing the input slack smaller. No new final theorem assumption k<=t is introduced silently.

## 9. Quantitative loss and reusable formal pieces

If

    K<=tau^(-u_K), K_H<=tau^(-u_H), A<=tau^(-u_A),
    lambda>=tau^v, lambda_f>=tau^(v_f), R_mesh<=tau^(-u_m),

then (12), apart from fixed constants, costs exponent

    D u_m + 2u_K + u_H + 3u_A + v + v_f.

The AD constant is measured in the ORIGINAL fine tau, as required by Definition 17.2(3); it need not be rewritten as rho^(-eta). There is no new power-separated rho/tau condition merely to establish this structural clause.

The new phase/time maps add O(m^2) equivalence relations to the one terminal self-uniform call. They should be present before claiming its final density or grain richness. This change remains within the proved finite self-uniform theorem's allowed relation count.

Already available components are: `UniformGrainPartitions.partition_richness_of_self_uniform` for (5), the actual carrier maximal-net constructor and finite partition counts for (3)–(4), the tube-bin geometry for (2) and the coarse per-time-bin bound, the injective shear-floor map for A_I^hat, and the proved lattice quotient estimates for the full ambient lower bound and rich-fiber upper bound. The nearby-rich extension being formalized must allow TWO quotient sets U_I and V_I; the requested union need not equal the full quotient of the common-slope coarse image.

The remaining Lean callers are the concrete carrier-net count (4), graph-cell localization used in (6)–(7), and the map comparisons in sections 6–7. No P5/P6 or global grains decomposition is an input to these arguments.

## 10. Independent checks

400 exact-rational tests of coarse physical quantization, variable fine slopes, original quotient cells, rich-neighbor assignments and bounded assignment fibers passed. The explicit boundary example produced coarse fiber sizes {-1:1, 0:8}, confirming why same-cell density would be an invalid inference. These tests are sanity checks; the derivations above are the mathematical proof, and no Lean verification of the complete caller is claimed.
