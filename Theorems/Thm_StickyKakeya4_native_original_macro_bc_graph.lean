import Theorems.Thm_StickyKakeya4_native_original_macro_phase_window
import Theorems.Thm_StickyKakeya4_original_actual_window_bc_graph
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000
noncomputable section
namespace NativeOriginalMacroBCGraph
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open OriginalWGrainDrift OriginalMacroGrainReadback OriginalLiteralGrainProfiles
open OriginalLiteralMacroDensity OriginalLiteralDenseMacroHeight OriginalWeightedMacroSelection
open OriginalPhaseCellPopulation NativeTangentGridCoarsening OriginalWPhysicalDisplacement
open OriginalLiteralHeightWindow OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open NativeOriginalMacroSourceDensity NativeOriginalMacroPrintedCore NativeOriginalMacroPhaseWindow
open OriginalMacroDirectionCells OriginalPhaseWindowGraph OriginalWCoreDynamics NativeOriginalPhaseWindowGraph
/-- Literal original source laws construct the actual phase A, actual
 height-bin B and unchanged original Phi graph. Every output edge carries
 an original full-direction W witness and an original target in A. -/
theorem exists_original_macro_BC_graph {P : Type*} [DecidableEq P] {n : ℕ}
    {D : FiniteScaleSource n} {eta delta q K kappa C0 DirErr Cxi L IncErr : ℝ}
    (hD : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (parent : Parent)
    (E : Finset P) (I0 : Finset (P × Fin n)) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (raw : P → Finset ℝ)
    (hd : 0 < delta) (hscale : delta ≤ (N:ℝ)*D.thickness) (hdq : delta ≤ q) (hq4 : 4*q ≤ 1)
    (hK : 1 ≤ K) (hkappa : 0 ≤ kappa) (hsmall : K*q ≤ 1/8)
    (hC : 0 ≤ C0) (hDir : 0 ≤ DirErr) (hXi : 0 ≤ Cxi) (hL : 0 ≤ L) (hInc : 0 ≤ IncErr)
    (hZbox : ∀ z ∈ E.image height, |z| ≤ 1)
    (hZsep : ∀ z ∈ E.image height, ∀ w ∈ E.image height, z ≠ w → delta ≤ |z-w|)
    (hZmass : 1 ≤ K*delta*((E.image height).card:ℝ))
    (hx : ∀ p ∈ E, |x p| ≤ 1)
    (hMat : ∀ z ∈ E.image height, |(F z 1).1| ≤ 1 ∧ |(F z 1).2| ≤ 1)
    (hosc : ∀ z ∈ E.image height, ∀ z0 ∈ E.image height,
      ⌊z/q⌋=⌊z0/q⌋ → ‖F z-F z0‖ ≤ L*q)
    (hsep : ∀ p ∈ E, ∀ p0 ∈ E, p ≠ p0 → delta ≤
      dist (OriginalTubeSliceOccupancy.embedding height x y p) (OriginalTubeSliceOccupancy.embedding height x y p0))
    (hYbox : ∀ z ∈ E.image height, ∀ g ∈ grains E height (grainCoordinate height x y F) z, ‖g‖ ≤ 1)
    (hY : ∀ z ∈ E.image height, LiteralCoverAD (grains E height (grainCoordinate height x y F) z) delta K (2-kappa))
    (hX : ∀ z ∈ E.image height, ∀ g ∈ grains E height (grainCoordinate height x y F) z,
      1 ≤ K*delta*((scalarCells (tangentFiber E height (grainCoordinate height x y F) z g) x delta).card:ℝ))
    (hUnion : ∀ j : ℤ, (window E height q j).Nonempty →
      LiteralCoverAD ((window E height q j).image (grainCoordinate height x y F)) q K (2-kappa))
    (hRawNe : ∀ p ∈ E, (raw p).Nonempty)
    (hRawAD : ∀ p ∈ E, NativeScalarCoverAD.CoverADBounds (raw p) delta K kappa)
    (hRawBox : ∀ p ∈ E, ∀ phi ∈ raw p, |phi| ≤ 1)
    (hSource : ∀ p ∈ E, ∀ phi ∈ raw p, ∃ t, (p,t) ∈ I0 ∧
      |NativeRescaledMacroTubeCount.scalarSlope D cells a N parent t-phi| ≤ C0*delta)
    (hDirEq : ∀ p t, (p,t) ∈ I0 →
      ‖NativeRescaledMacroTubeCount.normalSlope D cells a N parent t-offset p-
        F (height p) (NativeRescaledMacroTubeCount.scalarSlope D cells a N parent t)‖ ≤ DirErr*delta)
    (hIncU : ∀ p t, (p,t) ∈ I0 →
      ‖incidenceResidual height x (baseU D cells a N parent)
        (NativeRescaledMacroTubeCount.scalarSlope D cells a N parent) p t‖ ≤ IncErr*delta)
    (hIncV : ∀ p t, (p,t) ∈ I0 →
      ‖incidenceResidual height y (baseV D cells a N parent)
        (NativeRescaledMacroTubeCount.normalSlope D cells a N parent) p t‖ ≤ IncErr*delta)
    (hMacro : ∀ k ∈ E.image (physicalCell q height x y), ∃ xi : ℝ × ℝ, ∃ Psi : Finset ℝ,
      NativeScalarCoverAD.CoverADBounds Psi q K kappa ∧ (∀ b ∈ Psi, |b| ≤ 1) ∧
      (∀ p ∈ localPoints E (physicalCell q height x y) k, ‖offset p-xi‖ ≤ Cxi*q) ∧
      (∀ p ∈ localPoints E (physicalCell q height x y) k, ∀ phi ∈ raw p,
        ∃ b ∈ Psi, dist phi b ≤ q))
    (hdq2 : delta ≤ q^2) (hCK : C0 ≤ K) (r tau : ℝ) (sigma : ℝ) :
    ∃ k ∈ E.image (physicalCell q height x y), ∃ fine : P → Finset ℝ,
      ∃ Phi : Finset ℝ, ∃ source : P → ℝ → Fin n, ∃ angle : Fin n → ℝ,
      let Q := localPoints E (physicalCell q height x y) k
      let J := OriginalSelectedAngularIncidences.incidences Q fine source
      let Z := localHeights E (physicalCell q height x y) height k
      let u := NativeRescaledMacroTubeCount.scalarSlope D cells a N parent
      let v := NativeRescaledMacroTubeCount.normalSlope D cells a N parent
      let rho := q+C0*delta
      let width := (9*L+16*max DirErr (2*IncErr)+1)*rho^2
      Q.Nonempty ∧ J ⊆ I0 ∧ J.Nonempty ∧ TwoTubePathCollisionCount.points J=Q ∧
      Phi ⊆ Q.biUnion raw ∧ Separated Phi q ∧ (∀ b ∈ Phi, |b| ≤ 1) ∧
      ADBounds Phi q (192*K^2) kappa ∧ Phi.Nonempty ∧
      OriginalAngularSourcePopulation.ballCap delta q (192*K^2) kappa (2*C0)*(Phi.card:ℝ)/
        OriginalAngularSourcePopulation.degree delta (192*K^2) kappa C0 ≤ 512*(192*K^2)^3*(1+C0)^3 ∧
      (∀ t ∈ TwoTubePathCollisionCount.tubes J, angle t ∈ Phi ∧ |u t-angle t| ≤ rho) ∧
      q ≤ 124416000*K^5*(2*L+4)^2*delta*(Z.card:ℝ) ∧
      ∃ p0 ∈ Q, ∃ S : Finset (ℝ × Fin n), ∃ hSV : S ⊆ vertices J height, S.Nonempty ∧
        ((witnesses J height (directionCell (q/8) u v)).card:ℝ) ≤
          2*((RichWitnessCore.retained (witnesses J height (directionCell (q/8) u v))
            (fun w => endpoint height w.1) (fun w => endpoint height w.2) S).card:ℝ) ∧
        ∃ z ∈ Z, ∃ g : GrainLabel, ∃ pick : OriginalPhaseGridPopulation.Label → Core S,
          let Ecore := heightSlice S z
          let grain := fun s => grainCell width (grainCoordinate height x y F (rep J height S hSV s))
          let phase := fun s => phaseLabel r tau (x p0) (offset p0) x offset (rep J height S hSV s)
          let A := expanded Ecore grain phase g
          let G0 := menuGraph (occupied Ecore grain phase g) pick (M J height (directionCell (q/8) u v) angle S)
          let f := OriginalActualWindowBCGraph.heightBin sigma
          A.Nonempty ∧ ∃ anchor ∈ Z ×ˢ Phi, ∃ j < DyadicOriginalFiberSelection.levelCount Z,
            let Zj := DyadicOriginalFiberSelection.bin Z f j
            let B := Zj.image f
            let G := OriginalHeightGraphCoarsening.coarseGraph
              (OriginalHeightGraphCoarsening.edgeBin (OriginalMenuSection.sectionGraph G0 anchor) Z f j) f
            Zj.Nonempty ∧ B.Nonempty ∧ G.Nonempty ∧ G ⊆ A ×ˢ (B ×ˢ Phi) ∧
            rawMenuCoefficient delta q K kappa C0 DirErr Cxi L IncErr Phi.card*(Z.card:ℝ) ≤
              9*(DyadicOriginalFiberSelection.levelCount Z:ℝ)*(Zj.card:ℝ) ∧
            rawMenuCoefficient delta q K kappa C0 DirErr Cxi L IncErr Phi.card*
              (A.card:ℝ)*(B.card:ℝ)*(Phi.card:ℝ) ≤
              18*(DyadicOriginalFiberSelection.levelCount Z:ℝ)*(G.card:ℝ) ∧
            (∀ b ∈ B, DyadicOriginalFiberSelection.fiber Zj f b=DyadicOriginalFiberSelection.fiber Z f b ∧
              2^j ≤ (DyadicOriginalFiberSelection.fiber Z f b).card ∧
              (DyadicOriginalFiberSelection.fiber Z f b).card < 2^(j+1)) ∧
            ∀ a b c, (a,(b,c)) ∈ G → ∃ t ∈ Zj, f t=b ∧
              (a,((anchor.1,t),(anchor.2,c))) ∈ G0 ∧
              pick a ∈ Ecore ∧ grain (pick a)=g ∧ phase (pick a)=a ∧
              phase (next J height (directionCell (q/8) u v) angle S (pick a) ((anchor.1,t),(anchor.2,c))) ∈ A ∧
              ∃ w ∈ witnesses J height (directionCell (q/8) u v),
                menu height angle w=((anchor.1,t),(anchor.2,c)) ∧
                endpoint height w.1=(pick a).val ∧
                endpoint height w.2=(next J height (directionCell (q/8) u v) angle S
                  (pick a) ((anchor.1,t),(anchor.2,c))).val := by
  obtain ⟨k,hk,fine,Phi,source,angle,hQne,hJsub,hJne,hJpts,hPhiSub,hPhiSep,hPhiBox,hPhiAD,hPhiNe,
    hRatio,hNear,hHeight,p0,hp0,S,hSV,hS,hhalf,z,hz,g,pick,hWindow⟩ := exists_original_macro_phase_window
      hD cells a N hN parent E I0 height x y offset F raw hd hscale hdq hq4 hK hkappa hsmall
      hC hDir hXi hL hInc hZbox hZsep hZmass hx hMat hosc hsep hYbox hY hX hUnion
      hRawNe hRawAD hRawBox hSource hDirEq hIncU hIncV hMacro hdq2 hCK r tau
  let Q := localPoints E (physicalCell q height x y) k
  let Z := localHeights E (physicalCell q height x y) height k
  let J := OriginalSelectedAngularIncidences.incidences Q fine source
  let u := NativeRescaledMacroTubeCount.scalarSlope D cells a N parent
  let v := NativeRescaledMacroTubeCount.normalSlope D cells a N parent
  let rho := q+C0*delta
  let width := (9*L+16*max DirErr (2*IncErr)+1)*rho^2
  let Ecore := heightSlice S z
  let grain := fun s => grainCell width (grainCoordinate height x y F (rep J height S hSV s))
  let phase := fun s => phaseLabel r tau (x p0) (offset p0) x offset (rep J height S hSV s)
  let A := expanded Ecore grain phase g
  let G0 := menuGraph (occupied Ecore grain phase g) pick (M J height (directionCell (q/8) u v) angle S)
  have hb : 0 < rawMenuCoefficient delta q K kappa C0 DirErr Cxi L IncErr Phi.card :=
    rawMenuCoefficient_pos hd (hd.trans_le hdq) (lt_of_lt_of_le zero_lt_one hK) hC hDir hXi hL hInc
      (Nat.cast_pos.mpr hPhiNe.card_pos)
  obtain ⟨hA,anchor,hAnchor,j,hj,hZj,hB,hG,hGsub,hRet,hDense,hFib,hWitness⟩ :=
    OriginalActualWindowBCGraph.exists_actual_window_BC_graph Ecore grain phase Z Phi
      (M J height (directionCell (q/8) u v) angle S)
      (next J height (directionCell (q/8) u v) angle S) g pick sigma hb ⟨z,hz⟩ hPhiNe hWindow
  refine ⟨k,hk,fine,Phi,source,angle,hQne,hJsub,hJne,hJpts,hPhiSub,hPhiSep,hPhiBox,hPhiAD,hPhiNe,
    hRatio,hNear,hHeight,p0,hp0,S,hSV,hS,hhalf,z,hz,g,pick,hA,anchor,hAnchor,j,hj,
    hZj,hB,hG,hGsub,hRet,hDense,hFib,?_⟩
  intro a b c he
  obtain ⟨t,ht,hbin,hmenu,hpick,hgrain,hphase,hTarget⟩ := hWitness a b c he
  obtain ⟨w,hw,hleft,hright,hMenu,_hs,_ht,_hzs,_hzt⟩ :=
    NativeOriginalPhaseWindowEdges.graph_edge_original_witness J height (directionCell (q/8) u v) angle
      S hSV (occupied Ecore grain phase g) pick a ((anchor.1,t),(anchor.2,c)) hmenu
  exact ⟨t,ht,hbin,hmenu,hpick,hgrain,hphase,hTarget,w,hw,hMenu,hleft,hright⟩
end NativeOriginalMacroBCGraph
