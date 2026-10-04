# Original common-C and directional-count continuation

This continues the unnumbered argument immediately after Eq169 in Theorem21.2, paper p91. Eq170 is a different geometric step in the later proof of Lemma21.1 on p92. The thirteen new implementation modules leave the frozen nine-module vector BSG batch unchanged. All thirteen implementation modules passed strict Lean 4.33.1 source checks. A fresh imported readback verified all forty public theorem/lemma declarations, using only propext, Classical.choice and Quot.sound. OriginalCommonGrowth.manifest records the frozen status, exact source/object hashes, full public ledger and logs; the nine frozen vector source hashes were verified unchanged.

## Exact finite construction

Start with the ACTUAL Eq169 output A' and F subset B×C. Suppose A' retains fraction r of the original A population N, F has original-pair density tau, and the actual eta-grid cover of A'+v(F)-v(F) is at most Q N, where v(b,c)=c•b.

1. Define literal common original scalar fibers Cbb'={c in C:(b,c) in F and (b',c) in F}. Finite Cauchy and exact collision-fiber counting construct rich original pairs of density at least tau²/2 in B², each with at least (tau²/2)|C| common labels. Original pair weights are never replaced by distinct product-value counts.
2. Given an actual original radial graph H with missing-pair fraction mu, and original B ball fraction kappa at secant length d, remove short secants. If mu+kappa<=tau²/4, the intersection with the rich common-fiber graph has density at least tau²/4, and every remaining original secant has native norm at least d.
3. The identity c b-c b'=(b-b')c gives literal set containment A'+(b-b')Cbb' subset A'+v(F)-v(F), without rounding or representative perturbation. The inherited actual output cover yields original line collision energy at least nu |A'||C|², where nu=r tau⁴/(4Q).
4. If A' is eta-separated and every original C ball of radius t has at most chi|C| points, the actual collisions with scalar gap at most t number at most 16 chi |A'||C|². For 32chi<=nu, at least half the energy remains.
5. If s+eta<=d t, every remaining collision gives an original A pair with norm gap at least s and homogeneous directional relation |det(b-b',a-a')|<=2eta||b-b'||. Original scalar separation deltaC bounds collision multiplicity over each A pair by Mpack|C|, where Mpack=2eta/(d deltaC)+2. Thus each retained original B pair has at least [nu/(2Mpack)]|A'||C| such A pairs.
6. Two original secants incident to the same displacement of norm at least s lie in one actual original physical pair tube of width 8eta/s. The existing original-strip-to-Euclidean-physical-tube bridge supplies an actual affine-line witness. Therefore an original-pair tube cap cap|B| bounds all such directional B-pair incidences by cap|B|². No independently chosen direction carrier or supplied Frostman certificate is used.
7. Exact double counting of the SAME original A/B pair incidences gives

       cap |A'| >= [r tau^6/(32 Q Mpack)] |C|.

Every new selection is an actual finite filter or image of the original carriers. Common scalar fibers continue to refer to the original F and C.

## Original-G caller and uniform quantifiers

OriginalGraphRadialGrowth.original_graph_growth_of_original_radial_cap invokes the frozen VectorOriginalGraphBSG.original_ABC_dyadic_bsg itself. It starts with literal G subset A×B×C, density beta, and actual delta-grid output cover at most M|A|. For epsilon>0 it chooses K,n0 BEFORE beta,M,A,B,C,G and all native cap parameters. For delta=2^-n, n>=n0, set

    Hlevels = levelCount(B×C),
    alpha = beta²/(392 M Hlevels²),
    r = alpha^K delta^epsilon,
    tau = r(beta²/M)/(196 Hlevels),
    Q = 49 delta^(-2epsilon)/alpha^(2K).

With eta=delta/2 and original C separation delta, Mpack=1/d+2 and the required physical pair tube width is 4delta/s. The caller obtains the growth inequality for the ORIGINAL A by the proved inclusion A' subset A. The retained F is exactly the graph-weighted whole-fiber BSG output; no substitute high-density product subset is assumed.

## Precise remaining dependency

The finite growth comparison consumes an explicit ORIGINAL-B physical-pair tube population cap at width 4delta/s, on an actual original pair graph with the stated missing-pair budget. It does not claim to construct the currently unproved all-scale radial profile of Theorem13.2/A.1.

If that genuine radial profile supplies cap=D(4delta/s), the finite comparison gives

    |A| >= [r tau^6 s/(128 D Q Mpack delta)] |C|.

For d<=1, Mpack<=3/d, giving the weaker convenient coefficient r tau^6 d s/(384 D Q delta). Formal selection of all small scale/exponent parameters is a further caller step.

The currently certified initial A.2 radial graph only supplies a single-scale cap of the form delta^chi. It can be used at the covered widths, but gives its correspondingly weaker growth bound. It does not supply the needed linear dependence on the tube width. The main ABC growth endpoint is therefore still open until the genuine small-s A.3/all-scale A.1 input and parameter specialization are completed.

## Verification ledger policy

The new batch contains thirteen implementation modules and forty public theorem/lemma declarations. Definitions, abbreviations, and private helpers are excluded from that proof count. The all-public readback imports OriginalGraphRadialGrowth and checks every public proof closure. The existing nine-module/45-proof vector batch remains frozen and is tracked separately.
