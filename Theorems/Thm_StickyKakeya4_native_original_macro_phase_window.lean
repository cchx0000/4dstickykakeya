import Theorems.Thm_StickyKakeya4_native_original_macro_printed_core
import Theorems.Thm_StickyKakeya4_original_actual_core_phase_window
import Theorems.Thm_StickyKakeya4_original_macro_window_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeOriginalMacroPhaseWindow
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open OriginalWGrainDrift OriginalMacroGrainReadback OriginalLiteralGrainProfiles
open OriginalLiteralMacroDensity OriginalLiteralDenseMacroHeight OriginalWeightedMacroSelection
open OriginalPhaseCellPopulation NativeTangentGridCoarsening OriginalWPhysicalDisplacement
open OriginalLiteralHeightWindow OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open NativeOriginalMacroSourceDensity NativeOriginalMacroPrintedCore OriginalMacroDirectionCells
open OriginalMacroWindowGeometry OriginalPhaseWindowGraph OriginalWCoreDynamics NativeOriginalPhaseWindowGraph
/-- Original source laws construct an actual maximal occupied phase window
 on the SAME full-direction W core. The physical height and grain properties
 are derived from its one selected original macro-cell. -/
theorem exists_original_macro_phase_window {P : Type*} [DecidableEq P] {n : ℕ}
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
    (hdq2 : delta ≤ q^2) (hCK : C0 ≤ K) (r tau : ℝ) :
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
          IsWindowGraph (heightSlice S z)
            (fun s => grainCell width (grainCoordinate height x y F (rep J height S hSV s)))
            (fun s => phaseLabel r tau (x p0) (offset p0) x offset (rep J height S hSV s))
            ((Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi))
            (M J height (directionCell (q/8) u v) angle S)
            (next J height (directionCell (q/8) u v) angle S)
            (rawMenuCoefficient delta q K kappa C0 DirErr Cxi L IncErr Phi.card*
              (Z.card:ℝ)^2*(Phi.card:ℝ)^2) g pick := by
  obtain ⟨k,hk,fine,Phi,source,angle,hQne,hJsub,hJne,hJpts,hPhiSub,hPhiSep,hPhiBox,hPhiAD,hPhiNe,
    hRatio,hNear,hHeight,S,hSV,hS,hhalf,hrich⟩ := exists_original_macro_printed_core
      hD cells a N hN parent E I0 height x y offset F raw hd hscale hdq hq4 hK hkappa hsmall
      hC hDir hXi hL hInc hZbox hZsep hZmass hx hMat hosc hsep hYbox hY hX hUnion
      hRawNe hRawAD hRawBox hSource hDirEq hIncU hIncV hMacro
  let p0 := Classical.choose hQne
  have hp0 := Classical.choose_spec hQne
  rw [add_comm (C0*delta) q] at hNear
  let Q := localPoints E (physicalCell q height x y) k
  let Z := localHeights E (physicalCell q height x y) height k
  let J := OriginalSelectedAngularIncidences.incidences Q fine source
  let u := NativeRescaledMacroTubeCount.scalarSlope D cells a N parent
  let v := NativeRescaledMacroTubeCount.normalSlope D cells a N parent
  let rho := q+C0*delta
  let width := (9*L+16*max DirErr (2*IncErr)+1)*rho^2
  have hq : 0 < q := hd.trans_le hdq
  obtain ⟨hr, hqr, _hr2, hr1, hdr⟩ := source_phase_radius hd.le hq hC hCK hsmall hq4 hdq2
  obtain ⟨hF,hcluster,hdiam⟩ := original_macro_height_geometry E height x y F k hq hqr hL hMat hosc
  have hu := original_slope_bound (TwoTubePathCollisionCount.tubes J) u angle Phi hr1 hPhiBox hNear
  have hheight : ∀ p ∈ TwoTubePathCollisionCount.points J, height p ∈ Z := by
    intro p hp
    rw [hJpts] at hp
    exact mem_image_of_mem _ hp
  have hcell : ∀ s t, directionCell (q/8) u v s=directionCell (q/8) u v t → ‖u s-u t‖ ≤ rho := by
    intro s t he
    rw [Real.norm_eq_abs]
    exact (direction_cell_gap u v (by positivity : 0 < q/8) s t he).1.trans (by dsimp [rho]; linarith)
  have hwidth : 0 < width := by dsimp [width,rho]; positivity
  have hDrift : ((4*(2:ℝ)+1)*L+(12+4*(1:ℝ))*max DirErr (2*IncErr))*rho^2 ≤ width := by
    dsimp [width]
    nlinarith [sq_nonneg rho]
  have hb : 0 < rawMenuCoefficient delta q K kappa C0 DirErr Cxi L IncErr Phi.card :=
    rawMenuCoefficient_pos hd hq (lt_of_lt_of_le zero_lt_one hK) hC hDir hXi hL hInc
      (Nat.cast_pos.mpr hPhiNe.card_pos)
  obtain ⟨z,hz,g,pick,hGraph⟩ := OriginalActualCorePhaseWindow.from_original_core J height x y offset
    (baseU D cells a N parent) u angle (baseV D cells a N parent) v F (directionCell (q/8) u v)
    Z Phi S hSV hS r tau (x p0) (offset p0) hb.le hrich
    (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤2) hInc hDir hL hd.le hr.le hr1 hdr hwidth hDrift
    (fun p t hpt => hIncU p t (hJsub hpt)) (fun p t hpt => hIncV p t (hJsub hpt))
    (fun p t hpt => hDirEq p t (hJsub hpt)) hu hF hcluster hheight hdiam hcell
  exact ⟨k,hk,fine,Phi,source,angle,hQne,hJsub,hJne,hJpts,hPhiSub,hPhiSep,hPhiBox,hPhiAD,hPhiNe,
    hRatio,hNear,hHeight,p0,hp0,S,hSV,hS,hhalf,z,hz,g,pick,hGraph⟩
end NativeOriginalMacroPhaseWindow
