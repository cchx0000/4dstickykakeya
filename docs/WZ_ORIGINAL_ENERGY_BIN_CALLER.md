# Verified original-label energy bin caller after WZ (89)

Frozen 2026-10-03 21:30 UTC. This implements the singleton-C scalar caller on printed pp.54–55, preserving the original pair labels through floor rounding, dyadic selection, and later label restriction. It does not claim the general C-family version of Theorem13.5 or the separate vector adapter needed in Proposition21.2.

## Closed native input and output

Let A be a nonempty finite delta-separated real set, with separation **at least** delta, delta>0. Let W be any nonempty finite set of original labels and v:W→R any actual real-value map. No injectivity or separation is required of v. In the native source, W=B×B and v(b,b′)=(b−b′)(F(b)−F(b′)). Suppose the actual closed near-sum collision count obeys

    #{((a,p),(a′,p′))∈(A×W)^2:
        |a+v(p)−a′−v(p′)|≤delta} >= nu |A| |W|²,   nu>0.

Put L=1+floor(log₂|W|), f(p)=floor(v(p)/delta), and let W_j be the actual original whole-fiber bin at fiber size [2^j,2^(j+1)). `OriginalRealEnergyBinCaller.exists_original_real_bsg_bin` constructs an actual j<L such that, for S=f(W_j), X=delta*S:

* W_j and X are nonempty; X is delta-separated
* nu |W| <= 10L |W_j|
* nu |A| |X|² <= 40L² E_near(X,A;delta)

The last count is the ACTUAL original-real near-difference energy with the closed boundary <=delta, exactly the input of the previously verified real asymmetric construction. No intermediate energy, output-cardinality, or fiber-cap certificate is assumed.

## Why original multiplicities survive

The integer histogram keeps each original label p separately. Rounding only the A coordinate is injective, by its actual separation. The five discrepancy classes compare original real near-energy to the labelled integer histogram energy. Thus repeated values of f are not prematurely collapsed.

For the actual dyadic partition, Cauchy gives E_total<=L sum_j E_j. Translation cancellation injects each labelled collision into (p,p′,a), proving E_j<=|A| |W_j|². Together with the exact sum_j |W_j|=|W|, this constructs the same bin with both original mass and energy retention.

Each selected f-fiber is literally a full ORIGINAL fiber, of size between h=2^j and 2h. Collapsing the histograms then gives E_j<=4h² E(Abar,S), while |W_j|>=h|S|. The resulting unweighted integer energy is

    nu |A| |S|² <= 40L² E(Abar,S).

Finally, every exact collision in E(Abar,S) lifts to a closed near-collision of original A and literal X=delta*S. The two A fractional errors lie in [0,delta), so their difference has absolute value <delta. This reverse energy transfer adds NO loss. The grid map is injective, preserves cardinality, and has separation at least delta.

## The later original-pair graph

For ANY T subset S, define the actual lift

    W(T)={p∈W:f(p)∈T}.

`OriginalBinLabelLift.original_bin_lift` proves W(T) subset W_j, f(W(T))=T, and

    |W_j| |T| <= 2 |S| |W(T)|.

Therefore a subsequent BSG label subset retaining fraction alpha of S retains at least alpha/2 of W_j, and hence at least alpha*nu/(20L) of the original W. This constructs the actual pair graph G(c) used on p55. It keeps ALL matching original pairs, not one numerical representative per value.

The later dense four-cycle count, identity(90), and the radial good-quadruple comparison remain necessary. Claim13.8 is unnecessary solely for satisfying the old |Y|<=|X|^C entry condition of Lemma13.7: the verified bounded dyadic asymmetric route absorbs the actual cardinality ratio into delta^epsilon without that condition. This premise removal does not remove the later four-cycle/radial step.

## Verification manifest

All 23 declarations below have strict source compilation and separate imported axiom readbacks containing only propext, Classical.choice, Quot.sound:

* `PartitionedCollisionEnergy.lean` — 4 proofs; original histogram partition, exact menu, Cauchy energy decomposition, actual translation injection
* `HeavyEnergyBinSelection.lean` — 3; simultaneous original mass/energy selection
* `OriginalFiberEnergyCollapse.lean` — 5; actual histogram collapse to ordinary additive energy
* `EnergyPreservingOriginalFiberBin.lean` — 1; closed exact energy-preserving bin endpoint
* `LabelledRealEnergyBin.lean` — 3; label-preserving real rounding, actual real energy cap, real original bin construction
* `OriginalBinLabelLift.lean` — 2; all-original-pair lift and relative density
* `IntegerBinRealNearEnergy.lean` — 4; literal grid injection/cardinality/separation and actual reverse energy transfer
* `OriginalRealEnergyBinCaller.lean` — 1; closed source-level native caller

Canonical source checks and the combined imported axiom ledger are recorded in [the verified phase/bin checkpoint](../verification/wz-phase-bins-checkpoint.json).

`LabelledRealEnergyBin` imports `ActualRoundedAdditiveEnergyScratchBridge`, which is only an import-path copy of the parent's original verified rounding source. Repository integration should replace this with the canonical ActualRoundedAdditiveEnergy module, consistently with the canonical TwoTubePathCollisionCount. The bridge copy is not an additional proof.

AppendixA.3's positive-power Furstenberg gain remains a genuine independent open dependency. The native WZ configuration and the original compact packing-three theorem are not claimed complete by these finite additive constructions.
