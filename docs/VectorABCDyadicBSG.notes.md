# Genuine vector ABC energy-bin / BSG reduction

Work is in persistent proof-work only, with canonical repository imports. All nine implementation modules have passed strict source compilation. A fresh imported readback has audited all 45 public theorem/lemma declarations; every proof closure uses only propext, Classical.choice and Quot.sound. VectorABCDyadicBSG.manifest records the frozen verification status, exact source and object hashes, complete public ledger, compiler version and logs. Definitions and the private helper are excluded from the public-proof count.

## Source and exact finite interface

Paper: Wang–Zakharov, Theorem21.2, p91. The printed S_j subset delta Z cannot be read literally when b is planar: this implementation keeps a SINGLE coupled value code in Z² for each actual original pair (b,c).

Let delta=2^-n, eta=delta/2, W=B×C and v(b,c)=c•b. Inputs are actual nonempty finite A,B subset[-1,1]², C subset[-1,1], A separated by delta/2 in native sup norm, G subset A×W, and the literal original counts

    |G| >= beta|A||W|,
    # round_delta({a+v(w):(a,w) in G}) <= M|A|,

with beta,M>0. Euclidean delta separation of A implies the required native delta/2 separation through the canonical ActualPlanarRoundedEnergy API. B/C separation and nonconcentration are not needed for this finite energy/BSG step; they remain available for the later radial part of Theorem21.2.

For every epsilon>0, the canonical planar BSG theorem chooses K>0 and n0 BEFORE beta,M,A,B,C,G. For n>=n0 set

    H = levelCount W = floor(log2 |W|)+1,
    nu = beta²/M,
    alpha = nu/(392 H²),
    r = alpha^K delta^epsilon.

The strictly checked endpoint original_ABC_dyadic_bsg constructs an actual original whole multiplicative-value fiber bin j, A' subset A and F subset W, with

    |A'| >= r|A|,
    |F| >= [r nu/(196H)] |W|,
    # round_eta(A' + v(F) - v(F))
      <= 49 delta^(-2epsilon) alpha^(-2K) |A|.

F lies in that original dyadic bin and contains EVERY original W pair sharing the selected coupled vector code. It does not replace original pair populations by the number of distinct vector values. Neither coordinate of the product is independently selected.

## Derived energy chain

1. Existing finite Cauchy on G, followed by same-cell to literal coordinate-near inclusion, derives original labelled near-energy >=nu|A||W|² from the two source counts. No energy certificate is supplied.
2. The canonical planar49-discrepancy rounding theorem rounds A and each v(w) at eta while keeping every W label. Original A separation makes its rounding injective.
3. GraphWeightedOriginalFiberBin partitions ACTUAL rounded-G collision histograms and selects by their energy, while its population weights are the WHOLE original W value fibers. It reuses PartitionedCollisionEnergy, HeavyEnergyBinSelection and OriginalFiberEnergyCollapse. It constructs one whole original W bin, with

       nu|W| <= 98H|W_j|,
       nu|A||S|² <= 392H² addEnergy(round_eta(A), S),
       S = round_eta(v(W_j)) subset Z².

   Every original fiber over s in S has population between 2^j and 2^(j+1), and equals its full original W fiber. The selected ORIGINAL graph bin is proved nonempty and its actual collision energy is retained; an unrelated full-source high-energy bin is not substituted.
4. The actual additive-energy upper cap derives alpha<=1; positivity is immediate. Thus the BSG energy parameter is not assumed admissible.
5. X=synthesis_eta(S) is eta-separated and lies in[-4,4]². Integer energy injects into TRUE original coordinate-near energy of X×A. Invoke canonical PlanarOriginalDyadicBSG.coordinate_planar_dyadic_bsg with X=product grid bin, Y=original A. Its |X|²|Y| orientation matches exactly alpha|S|²|A|.
6. Lift selected X' back to ALL original W_j pairs in its coupled fibers. Uniform dyadic weights lose at most2 in transferring the selected label fraction, producing r nu/(196H) original-pair retention.
7. Selected grid values are NOT equated with original products. Their rounding codes agree exactly; canonical PlanarRoundedSumsetCover transfers the actual triple set at cost49. The reported cover is of ACTUAL v(F), at half mesh eta.

The generic original_vector_graph_dyadic_bsg also supports arbitrary original labels W and a bounded planar value map, without losing its original label multiplicities.

## Connection to the actual Section 21 producer

NativePlanarABCInput.exists_actual_planar_ABC_input constructs the actual finite A, B, C and G needed here. Its output has common mesh mu=rho/8, graph density beta/L and output-cover constant

    Mout = (L/beta)(4E/rho+8)^2,

where L is the proved graphMassLoss and E is the original endpoint error. Its planarCells map is the same componentwise floor grid as roundPoint after unfolding, its norm bounds imply the coordinate boxes, and its mu-separation implies mu/2-separation.

At a dyadic mesh mu=2^-n with n at least the BSG threshold, substitution therefore gives

    nu = beta^3 / [L^3 (4E/rho+8)^2],
    alpha = nu / (392H^2),
    H = levelCount(B×C).

These are actual output sets and their original graph counts. The remaining composition is a specialization of mesh and parameters, without an additional energy or cover assumption.

## Remaining scope

This is the initial BSG reduction corresponding to Eq169. It does not assert the final Theorem21.2 lower bound |A|>=delta^(zeta-1)|C|. Original radial good pairs, common C-fibers, separation exclusions and directional double counting remain later source steps. Likewise the physical Section21 box normalization and prior graph/target-cover construction are caller work, not supplied as fake energy assumptions here.
