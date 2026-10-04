# WZ Lemma 13.7 from the existing balanced BSG API

This is a constructive proof program for the bounded finite caller of WZ Lemma 13.7. The key point is that its new growth chain always uses graphs with EQUAL sides; the existing balanced BSG theorem is applied only after finding a slow-growth stage. Generalizing the last balanced API to unequal cardinalities by itself would retain an unacceptable power of their ratio.

Primary source checked: Tao–Vu, *Additive Combinatorics*, Section 2.6, Theorem 2.35 and Corollary 2.36, printed pp. 83–90; WZ Lemma 13.7, printed p. 54. The source's symmetry-set iteration motivates the finite construction below. We avoid an additional approximate-group interface by working with an explicit difference set and the existing Pluennecke–Ruzsa theorem.

## 1. What the existing code does and does not provide

The installed `LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean` contains:

* `graph_pair_dependentRandomChoice`, which already accepts unequal finite sides;
* `graph_dependentRandomChoice_payoff_pointwise` and `dense_bipartite_has_path3_rectangle`, whose current statements impose equal side cardinality;
* `graph_balogSzemerediGowers_restricted_sumset_explicit`, with equal sides and polynomial constants;
* `balog_szemeredi_gowers_asymmetric_explicit`, despite its name an equal-cardinality theorem, with explicit polynomial constants.

The path-three rectangle can be generalized to unequal sides by retaining the two separate cardinalities. Its multiplicity becomes c nu^5 |X||Y|. But the cubic representation estimate then bounds a sumset by

    C nu^(−C) |S|^3/(|X||Y|).

When the restricted sumset has size comparable to the larger |Y|, this is |Y|^2/|X| up to density factors. Thus this direct generalization alone does not yield the small-power ratio loss required by 13.7. Artificially balancing by deleting or replicating labels does not fix that loss.

The actual useful existing API is the balanced theorem applied to B_j,B_j at a slow stage of the DIFFERENCE chain below.

## 2. Bounded approximate energy reduces to exact integer energy

Let 0<delta<=1 and let nonempty X,Y subset [-1,1] be delta-separated, with cardinalities N,M. Suppose there are at least nu N^2 M ordered quadruples satisfying

    |x−y−x'+y'|<=delta,       0<nu<=1.

Round each ORIGINAL point by floor(value/delta). This map is injective on each set: two points in one half-open cell have distance strictly less than delta. Write the integer images as Xbar,Ybar.

For a near quadruple, the integer discrepancy is one of −2,−1,0,1,2. Indeed each fractional part is in [0,1), so the difference of the two positive and two negative fractional parts lies strictly between −2 and 2. The normalized real residual lies in [−1,1], making the integer discrepancy strictly between −3 and 3.

Let r(k) count actual pairs of integer labels with xbar−ybar=k. For each fixed integer c, finite Cauchy–Schwarz and translation of the summation index give

    sum_k r(k) r(k+c) <= sum_k r(k)^2.

Therefore the exact rounded energy is at least one fifth of the original approximate energy. The zero-shift difference-convolution energy equals `Finset.addEnergy Xbar Ybar`, by swapping the two Y labels in the additive-energy quadruple. Set a1=nu/10; the exact input is then

    E(Ybar,Xbar)>=2a1 M N^2.

The parent owns the formal rounding adapter; this section specifies its precise endpoint and does not assume it as a final theorem hypothesis.

## 3. Literal symmetry sets and their actual good pairs

For a finite nonempty large set A, define

    r_A(h)=#{a in A: a−h in A},
    Sym_a(A)={h in A−A: r_A(h)>=a|A|},       0<a<=1.

The total identity sum_h r_A(h)=|A|^2 gives the strong bound

    a |Sym_a(A)|<=|A|.                                    (B1)

If S subset Sym_a(A), count actual incidences (y,s) with y,s in A,S and y−s in A. Their number is at least a|A||S|. Cauchy on the y variable, or directly Mathlib's `card_sq_le_card_mul_addEnergy`, yields

    E(A,S)>=a^2|A||S|^2.                                  (B2)

More generally, if E(A,S)>=2b|A||S|^2, the actual good-pair set

    G={(s,t) in S^2:r_A(s−t)>=b|A|}

has |G|>=b|S|^2. This follows by bounding each bad pair's overlap by b|A| and each good pair's by |A|. Its ACTUAL difference image lies in Sym_b(A). Thus (B2) supplies the next threshold b=a^2/2, with no assumption on the resulting difference image.

These are now the concrete declarations in `SymmetrySetDifferenceStep.lean`: literal overlap/symmetry sets, the actual original good-pair set, the cardinal lower bound, difference-image inclusion, and equality with Mathlib additive energy. The worker reports strict and imported standard-axiom verification of all nineteen declarations.

## 4. Whole-fiber dyadic selection

Let E subset S^2 be the actual graph just constructed, |E|>=p|S|^2. Every difference fiber has at most |S| elements. Group the DIFFERENCE VALUES by the dyadic range of their ORIGINAL fiber cardinalities, and keep all original edges over one chosen group. With

    ell=1+floor(log_2 |E|) <= 1+2log_2 |S|,

one obtains E' subset E, D=image(E',subtraction), with

    |E'|>=|E|/ell,
    |D|>=|E'|/|S|,
    #{(s,t) in E':s−t=d}>=|E'|/(2|D|)    for every d in D. (B3)

The last estimate uses the factor-two comparability of the selected ORIGINAL fibers. Retaining whole fibers is essential: it gives their exact populations after selection. The actual implementation `DyadicOriginalFiberSelection.lean` now proves this construction with the displayed log(|E|) denominator, saturating every selected difference fiber in the entire original S x S. Its sixteen declarations have strict and imported standard-axiom verification.

## 5. The chain and the exact slow-growth stage

Use A=Ybar and B0=Xbar. The energy-only good-pair step followed by (B3) gives B1 subset Sym_(a1)(A). For j>=1 set

    a_(j+1)=a_j^2/2.

Apply the symmetry good-pair step and (B3) to B_j to construct an actual E_j subset B_j^2 and B_(j+1)=image(E_j,subtraction). Write n_j=|B_j| and let sigma_j be the derived edge-density lower bound; it is at least a_(j+1)/ell_j for j>=1, and a1/ell_0 initially. Then

    B_j subset Sym_(a_j)(A),                       j>=1,
    sigma_j n_j^2<=|E_j|,
    sigma_j n_j<=n_(j+1),
    n_j<=M/a_j,
    fiber_Ej(d)>=sigma_j n_j^2/(2n_(j+1)).                (B4)

All sets are nonempty since each displayed real lower population is positive. They consist of actual iterated differences with original pair witnesses. They need not be nested as sets; only these quantitative populations are used.

Let L=max(1,M/N), and fix a depth J before choosing delta. Telescoping gives

    product_(j=1)^J n_(j+1)/n_j
      = n_(J+1)/n_1 <= L/(a_(J+1) sigma_0).

Hence there exists an actual j in {1,...,J} such that

    n_(j+1)/n_j <= Q,
    Q=[L/(a_(J+1)sigma_0)]^(1/J).                        (B5)

By Cauchy on the actual difference fibers of E_j,

    E(B_j,B_j)>=|E_j|^2/n_(j+1)
                  >=kappa n_j^3,
    kappa=sigma_j^2/Q.                                   (B6)

Here 0<kappa<=1, since Q>=1 and the derived sigma_j<=1. Equation (B6) is an actual energy bound on EQUAL sets, exactly the premise of the existing explicit balanced BSG theorem. No unequal-side theorem is needed at this stage.

For fixed J, the a_j are fixed powers of nu times fixed constants, and every ell_j is bounded by a fixed multiple of 1+log(1/delta)+log(1/nu). Thus all the additional losses in (B4)–(B6) have the form

    C_J nu^(−C_J) [1+log(1/delta)]^(C_J),

apart from the explicit factor L^(1/J). Powers of log(1/nu) can be bounded by powers of nu^(−1), uniformly for 0<nu<=1.

## 6. The existing balanced theorem supplies the actual growth set

Apply `balog_szemeredi_gowers_asymmetric_explicit` to B_j,B_j and kappa. It returns two subsets C,D of size at least kappa n_j/16, with

    |C−D|<=C_BSG(kappa)n_j.

Its displayed rational constant obeys, for 0<kappa<=1,

    C_BSG(kappa)<=2^92 kappa^(−28).

Ruzsa triangle gives

    |C−C| |D|<=|C−D|^2,
    |C−C|<=K |C|,
    K=[16 C_BSG(kappa)/kappa]^2<=2^192 kappa^(−58).        (B7)

Define the ACTUAL finite set H=C−C. It is symmetric, contains zero, and |C|<=|H|<=K|C|. A chosen c0 in C gives C subset H+c0. The existing Pluennecke–Ruzsa subtraction theorem gives, for every integer m>=0,

    |mH|=|mC−mC|<=K^(2m)|C|<=K^(2m)|H|.                (B8)

Thus a formal approximate-group existence theorem is unnecessary. The only properties of H later used are these literal sumset counts and its genuine overlap with B_j.

The new `BalancedBSGIterationCore.lean` adapter uses the existing balanced theorem, Ruzsa triangle, and Pluennecke–Ruzsa to construct C and prove all iterated-difference bounds with the displayed rational constant. It and the polynomial-constant bound have now passed strict compilation and separate imported standard-axiom readbacks.

## 7. Pull the small set back to the ORIGINAL X

Suppose at stage i+1 one has |B_(i+1) intersect(H+x)|>=beta n_(i+1). Using the actual minimum fiber in (B4), at least

    beta sigma_i n_i^2/2

original edges of E_i have difference in H+x. Fixing their second endpoint by finite averaging gives an ORIGINAL t in B_i such that

    |B_i intersect(H+x+t)|>=beta sigma_i n_i/2.            (B9)

Start at stage j with beta=kappa/16, using C subset B_j intersect(H+c0). Iterate (B9) backward. The result is an actual translate x0 and

    X'=Xbar intersect(H+x0),
    |X'|/N>=(kappa/16) product_(i<j)(sigma_i/2).           (B10)

Only the sigma factors multiply during this pullback. The small L-exponent from the slow stage occurs ONCE through kappa; it is not multiplied by J. This is the crucial feature missing from size-balancing or one-step graph-BSG.

## 8. Retain the ORIGINAL large set and all iterated sums

Since C subset Sym_(a_j)(A) and |C|>=|H|/K, there are at least

    eta_cover |A||H|,       eta_cover=a_j/K,

actual pairs (a,h) whose translated H point sends a back into A. Equivalently, since C subset H+c0, averaging actual overlaps |A intersect(H+x)| over x in A+c0 gives a set X0 subset A+c0 of centers with

    |X0|>=eta_cover |A|/2,
    |A intersect(H+x)|>=eta_cover |H|/2   for x in X0.

Choose a maximal family of pairwise disjoint ORIGINAL translates H+x, x in X0; call its centers Z0. Their disjointness and the lower overlap imply

    |Z0|<=2|A|/(eta_cover |H|).

Maximality gives X0 subset Z0+(H−H). By (B8), |H−H|=|2H|<=K^4|H|. Thus

    Y'=A intersect(Z0+H),
    |Y'|>=eta_cover^2 |A|/(4K^4)
          =a_j^2 |A|/(4K^6).                             (B11)

For s=n+m>=1, the actual inclusions X' subset x0+H and Y' subset Z0+H, together with (B8), give

    |Y'+nX'−mX'|
      <=|Z0| |(s+1)H|
      <=2a_j^(−1) K^(2s+3) |A|.                         (B12)

The case s=0 is simply |Y'|<=|A|. This supplies the entire iterated-sumset conclusion while both output sets remain subsets of the ORIGINAL rounded X and Y.

## 9. Loss audit and return to original real labels

From (B5)–(B7), K has at worst a factor L^(58/J). Therefore:

* the small-set retention (B10) loses at worst L^(−1/J);
* the large-set retention (B11) loses at worst L^(−348/J);
* the iterated-sumset factor for s>=1 loses at worst L^(290s/J).

All omitted factors here are explicit fixed-depth powers of nu^(−1) and log(1/delta), as described after (B6). Choose J sufficiently large in the desired epsilon, for example with 1000/J<epsilon/4, before choosing the mesh. Since bounded delta-separated sets have M<=3/delta and N>=1,

    L<=3/delta.

Consequently the stated ratio losses are arbitrarily small powers of delta. The remaining fixed powers of log(1/delta) can be absorbed into another epsilon/4 loss, with constants depending only on the fixed depth; log(1/nu) terms have already been absorbed into a fixed power of nu^(−1).

This proves the desired type of output

    |X'|>=c_epsilon delta^epsilon nu^K |X|,
    |Y'|>=c_epsilon delta^epsilon nu^K |Y|,
    |Y'+nX'−mX'|_delta
       <=C_(epsilon,n,m)(delta^epsilon nu^K)^(−n−m)|Y|.

The additional hypothesis |Y|<=|X|^C is not needed for this bounded finite caller: the direct ratio bound L<=3/delta already supplies the required small mesh power. In particular Claim 13.8's polynomial cardinal lower bound is not needed merely to justify the asymmetric energy invocation in the native C={1} route.

Finally take the unique original preimages of the selected rounded labels. Their cardinalities are unchanged. An original iterated sum differs from its rounded integer sum times delta by less than (n+m+1)delta. Thus it occupies at most C_(n,m) neighboring delta-cells per integer sum. This is the explicit final covering-number conversion, and it preserves all original X,Y labels.

The full finite construction in Sections 3–8 is now formally proved. The public theorem `AsymmetricOriginalSubsetAssembly.finite_asymmetric_original_subsets` starts only from original nonempty finite X,Y, the literal Mathlib additive-energy lower bound, a>0, and a chosen positive depth J. It constructs the actual slow stage, both ORIGINAL subsets, their displayed quantitative retention, the polynomial balanced constant, and every iterated sum-difference bound on the same subsets. Strict compilation and a separate imported axiom readback report only `propext`, `Classical.choice`, and `Quot.sound`.

The formal native wrappers for approximate energy and original-real iterated cover transfer are owned by the parent. The remaining source-format packaging is the explicit delta/nu exponent absorption below. The independent radial/A.3 positive-power expansion frontier remains open.


## 10. One common finite density budget

The code uses `threshold a 0=a`, `threshold a (i+1)=threshold a i^2/2`, so the mathematical a_j above is code `threshold a (j-1)`. At depth J, put t=threshold(a,J). If an integer R satisfies

    |X|<=2^R,       |Y|/t<=2^R,

then every constructed B_i, i<=J, has size at most 2^R. Thresholds decrease; for i>=1 use |B_i|<=|Y|/threshold(a,i-1). Thus the ACTUAL good-pair menu has at most 2^(2R) edges, its dyadic level count is at most 2R+1, and all used edge densities and thresholds are at least

    p=t/(2R+1),       0<p<=1.

This is a derived input-cardinality budget, not an assumption about refined output graphs. The deterministic choice R=1+floor(log_2(max(|X|,ceil(|Y|/t)))) always supplies it.

Writing L=max(1,|Y|/|X|), the exact losses simplify to

    kappa >= p^4 L^(−1/J),
    K <= 2^192 p^(−232) L^(58/J),
    |X'|/|X| >= 2^(−J−4) p^(J+4) L^(−1/J),
    |Y'|/|Y| >= 2^(−1154) p^1394 L^(−348/J).

For s=n+m>=1,

    |Y'+nX'−mX'|/|Y| <= 2^(961s) p^(−1161s) L^(290s/J).

For example, the second retention uses a_j>=p and K^6<=2^1152 p^(−1392)L^(348/J). The sumset bound uses 2s+3<=5s and 1+232(2s+3)<=1161s. No density loss is repeated J times through the slow ratio; only the ordinary p factors recur.

For the native mesh delta=2^(−n), actual X subset [-4,4] and Y subset [-1,1] give |X|<=9*2^n and |Y|<=3*2^n. Set a=nu/10, D=2^J, so t=2(nu/20)^D. A convenient explicit budget is

    R=n+4+D*ceilNat(20/nu).

Indeed 2^ceil(20/nu)>=ceil(20/nu)>=20/nu, and the extra factor 16 dominates both original cardinal constants. For 0<nu<=1,

    R<=C_J(n+5)/nu,
    p>=c_J nu^(D+1)/(n+5).

This avoids any log(1/nu) case distinction. Choose J with 1000/J<epsilon/4 first; absorb the fixed power of n+5 into a further small power of 2^n. Every remaining nu loss is a fixed polynomial depending only on J. The parent’s original-real transfer uses at most 2(n+m)+3 output floor cells per actual integer sum, which is absorbed into the source constant depending on n,m.

## 11. Frozen finite modules and exact scope

Verified strict source plus independent imported standard-axiom readback:

* `SymmetrySetDifferenceStep.lean` (19 declarations): original overlaps, literal symmetry sets, good pairs and exact energy identification
* `DyadicOriginalFiberSelection.lean` (16): original full-fiber dyadic selection
* `SymmetryDifferenceGrowthChain.lean` (26): constructed chain, telescoping and actual slow stage
* `BalancedBSGIterationCore.lean` (2) and `BalancedBSGPolynomialLoss.lean` (3): existing balanced API to one real core, all iterated differences, explicit polynomial loss
* `OriginalDifferenceTranslatePullback.lean` (2), `IteratedDifferenceTranslatePullback.lean` (1), and `ChainOriginalCorePullback.lean` (1): actual backwards original-label capture
* `SlowSymmetryBalancedCore.lean` (4): actual difference-collision injection and the selected balanced stage
* `RichSymmetryTranslateCenters.lean` (8): actual symmetry incidences generate rich ORIGINAL translated centers
* `DisjointRichTranslateCover.lean` (3): actual maximal-disjoint translate family and original large-set selection
* `DifferenceCoreIteratedCover.lean` (4): all iterated original output sumsets from the literal difference core
* `AsymmetricOriginalSubsetAssembly.lean` (2): closed exact finite asymmetric endpoint, with no intermediate certificates as input

The uniform finite p-budget and root-factor arithmetic are now also verified: `SymmetryChainUniformDensity.lean` has 8 proved declarations, including its original-cardinality-only common-density constructor; `SymmetrySlowFactorBudget.lean` has 4, including the actual chain kappa bound and cross-multiplied K cost. `OriginalRealAsymmetricConstruction.lean` has one verified end-to-end real theorem, starting from original separated real points and actual closed approximate energy, ending with original real subsets and all actual floor-grid iterated cover bounds. All have strict and independent imported standard-only readbacks.

The exact real caller allows every nu>0. The source-format exponent-absorption wrapper is being proved separately for the native 0<nu<=1 range. No broader nu quantifier is claimed for that unfinished analytic wrapper. Three `ScratchBridge` copies of the parent's rounding modules change imports only; they are not additional proofs and should map to the original canonical modules in repository integration. This audit does not claim the native WZ configuration is assembled, Theorem 13.5 is fully proved, or the original compact theorem is closed; A.3 remains a genuine independent dependency.


Frozen at 2026-10-03 21:01 UTC. Later work on the actual energy-preserving bin selection following equation (89) is recorded separately in `WZ_ENERGY_PRESERVING_DYADIC_BIN.md`; do not infer that caller merely from this BSG endpoint.

## Integrated native dyadic endpoint

The subsequently verified `AsymmetricDyadicAbsorption.original_real_dyadic_bsg`
now provides the uniform exponent absorption mentioned above. Its mesh
threshold precedes nu and all sum multiplicities. The original real inputs
are bounded and separated; only their actual closed near-difference energy
is assumed. It needs no cardinality-power balance hypothesis. Thus the
preliminary Claim13.8 lower bound is unnecessary solely to enter BSG in this
native route; its later four-cycle/radial mechanism remains separate.
See `WZ_ORIGINAL_ASYMMETRIC_BSG.md` and the checkpoint evidence for precise
verified scope.
