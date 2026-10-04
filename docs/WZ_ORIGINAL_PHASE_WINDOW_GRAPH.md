# Original Section21 phase-window continuation (2026-10-04 UTC)

## Verified construction

Official Lean 4.33.1, strict `-j1 -DautoImplicit=false -DwarningAsError=true`.
The repository checkpoint strictly checks the canonical modules and every public theorem.

1. `OriginalCoreMenuDensity.lean` (recovered source; now compiled unchanged): original W mass constructs an actual persistent rich core; original menu fibers cost C^5 U^3; the menu lower bound is `(alpha/4) D^2 |Z|^2 <= U^2 |M(v)|`. Both exact original heights and actual angular alphabet are retained.
2. `OriginalPhaseWindowGraph.lean`: literal 2D grain-floor cells, nine neighboring cells, maximal occupied phase-label cell, one chosen real state per phase label, literal phase/menu graph. It proves `|A_enlarged| <= 9 |A_central|` and `degree |A_enlarged| <= 9 |G|`; every menu successor lies in A_enlarged. No state-count maximum is substituted for a phase-label maximum.
3. `NativeOriginalPhaseWindowGraph.lean`: directly composes original rich-core construction and original scalar successor grain drift. Constructs an actual original height z in Z, the actual representative phase labels, the graph and its density, from original incidence mass/fibers and primitive geometric errors. No output-density certificate, phase-population assumption, representative assumption, or successor assumption.
4. `NativeOriginalPhaseWindowPopulation.lean`: the same enlarged phase set is the phase image of the original retained states lying in the neighbor cells; its original grain-coordinate distance from the central lower corner is <=2 width. Under `r<=Delta` and `4 width + A r <= Delta`, the original single Delta-cell offset field proves local population
   `|A_enlarged intersect B(center,R)| <= H(2R/mesh+2)`,
   `H=27(2 Cxi Delta/tau+2)^2`.
5. `NativeOriginalPhaseWindowEdges.lean`: every actual graph edge carries the genuine original W witness, genuine incidence representatives and correct original terminal heights/tubes. Its signed anisotropic normalized relation is proved with error `max(3+12 IncErr,3+8 DirErr) rho` and the graph's own exact menu coordinates.
6. `OriginalPhaseWindowDensity.lean`: normalized actual full-alphabet graph density is beta/9 whenever `4 beta U^2 |angles|^2 <= alpha D^2`. Original Z is used in the alphabet; no arbitrary retained-height denominator.
7. `OriginalPhaseGridError.lean`: when `r=mesh*rho` and `tau=mesh*Lip*rho`, the original reflected phase label is exactly the floor of the anisotropically normalized phase; grid corner error <=mesh. Two endpoint roundings add <=2mesh.
8. `NativeOriginalPhaseGridEdges.lean`: actual original graph edges satisfy that quantized relation, with error `max(3+12 IncErr,3+8 DirErr)rho+2mesh`.

## Natural scale specialization (not silently assumed)

Let `Cgrain=(4B+1)Lip+(12+4A)max(DirErr,2IncErr)` and choose positive width >= Cgrain*rho^2. Taking mesh=rho gives r=rho^2, tau=Lip*rho^2 and edge error `(max(3+12IncErr,3+8DirErr)+2)rho`. The working physical field scale must satisfy Delta >= max(r,4width+A*r), with Delta/tau bounded explicitly. If Delta<=G*tau, then H<=27(2Cxi G+2)^2. Macro-only field consistency still does not imply this.

## Remaining Section21 caller work

The graph is currently labeled by original menus `(z0,z1,angle0,angle1)`. It is a genuine densely populated graph in the actual enlarged A times the full original menu alphabet. Further fixing/coarsening menu coordinates into the desired B,C product, retaining density through finite projection/coarse-height selection, and assembling the ABC/deep projection input remain separate. No completed Lemma21.1 or Proposition17.4 claim is made.

## Validation

The [combined imported readback](../verification/WZPhaseBinsReadback.lean), [axiom log](../verification/wz-phase-bins-axioms.log), and [checkpoint](../verification/wz-phase-bins-checkpoint.json) cover all public proofs, including the 24 theorems in the eight continuation modules and their 16 earlier prerequisites. Definitions are not counted.
