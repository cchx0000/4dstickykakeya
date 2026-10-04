import Theorems.Thm_StickyKakeya4_native_original_macro_source_density
import Theorems.Thm_StickyKakeya4_original_macro_full_reference_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeOriginalMacroPrintedCore
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open OriginalWGrainDrift OriginalMacroGrainReadback OriginalLiteralGrainProfiles
open OriginalLiteralMacroDensity OriginalLiteralDenseMacroHeight OriginalWeightedMacroSelection
open OriginalPhaseCellPopulation NativeTangentGridCoarsening OriginalWPhysicalDisplacement
open OriginalLiteralHeightWindow OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open NativeOriginalMacroSourceDensity OriginalMacroDirectionCells OriginalMacroFullReferenceCore
def rawMenuCoefficient (delta q K kappa C0 DirErr Cxi L IncErr Nphi : ℝ) : ℝ :=
  menuCoefficient (densityCoefficient K C0 DirErr Cxi L IncErr) ((16*IncErr+2)^3)
    ((2*K*(directionCost C0 DirErr Cxi L)^3)*(192*K^2))
    (OriginalAngularSourcePopulation.degree delta (192*K^2) kappa C0)
    (OriginalAngularSourcePopulation.ballCap delta q (192*K^2) kappa (2*C0)) Nphi
theorem rawMenuCoefficient_pos {delta q K kappa C0 DirErr Cxi L IncErr Nphi : ℝ}
    (hd : 0 < delta) (hq : 0 < q) (hK : 0 < K) (hC : 0 ≤ C0)
    (hD : 0 ≤ DirErr) (hXi : 0 ≤ Cxi) (hL : 0 ≤ L) (hI : 0 ≤ IncErr)
    (hNphi : 0 < Nphi) : 0 < rawMenuCoefficient delta q K kappa C0 DirErr Cxi L IncErr Nphi := by
  unfold rawMenuCoefficient menuCoefficient OriginalScalarCollisionMass.collisionAlpha
    OriginalAngularSourcePopulation.degree OriginalAngularSourcePopulation.ballCap
    densityCoefficient pointCost tubeCost directionCost jointError
  positivity
/-- Literal source laws produce the same original macro-cell, its actual
 angular incidences and the persistent core with genuine full terminal
 direction coincidence. W mass and menu density are conclusions. -/
theorem exists_original_macro_printed_core {P : Type*} [DecidableEq P] {n : ℕ}
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
        ∃ b ∈ Psi, dist phi b ≤ q)) :
    ∃ k ∈ E.image (physicalCell q height x y), ∃ fine : P → Finset ℝ,
      ∃ Phi : Finset ℝ, ∃ source : P → ℝ → Fin n, ∃ angle : Fin n → ℝ,
      let Q := localPoints E (physicalCell q height x y) k
      let J := OriginalSelectedAngularIncidences.incidences Q fine source
      let Z := localHeights E (physicalCell q height x y) height k
      let u := NativeRescaledMacroTubeCount.scalarSlope D cells a N parent
      let v := NativeRescaledMacroTubeCount.normalSlope D cells a N parent
      Q.Nonempty ∧ J ⊆ I0 ∧ J.Nonempty ∧ TwoTubePathCollisionCount.points J=Q ∧
      Phi ⊆ Q.biUnion raw ∧ Separated Phi q ∧ (∀ b ∈ Phi, |b| ≤ 1) ∧
      ADBounds Phi q (192*K^2) kappa ∧ Phi.Nonempty ∧
      OriginalAngularSourcePopulation.ballCap delta q (192*K^2) kappa (2*C0)*(Phi.card:ℝ)/
        OriginalAngularSourcePopulation.degree delta (192*K^2) kappa C0 ≤ 512*(192*K^2)^3*(1+C0)^3 ∧
      (∀ t ∈ TwoTubePathCollisionCount.tubes J, angle t ∈ Phi ∧ |u t-angle t| ≤ C0*delta+q) ∧
      q ≤ 124416000*K^5*(2*L+4)^2*delta*(Z.card:ℝ) ∧
      ∃ S ⊆ vertices J height, S.Nonempty ∧
        ((witnesses J height (directionCell (q/8) u v)).card:ℝ) ≤
          2*((RichWitnessCore.retained (witnesses J height (directionCell (q/8) u v))
            (fun w => endpoint height w.1) (fun w => endpoint height w.2) S).card:ℝ) ∧
        ∀ s ∈ S, rawMenuCoefficient delta q K kappa C0 DirErr Cxi L IncErr Phi.card*
            (Z.card:ℝ)^2*(Phi.card:ℝ)^2 ≤
            ((coarseMenus J height (directionCell (q/8) u v) angle S s).card:ℝ) ∧
          coarseMenus J height (directionCell (q/8) u v) angle S s ⊆ (Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi) := by
  obtain ⟨k,hk,fine,Phi,source,hQne,hfine,hPhiSub,hPhiSep,hPhiBox,hPhiAD,hPhiNe,
    hJsub,hJne,hJpts,hSpec,hDegree,hRefBall,hNear,hRatio,_hZsep,_hPoint,_hUpper,hHeight,hDen⟩ :=
    exists_original_macro_angle_density hD cells a N hN parent E I0 height x y offset F raw
      hd hscale hdq hq4 hK hkappa hsmall hC hDir hXi hL hInc hZbox hZsep hZmass hx hMat hosc
      hsep hYbox hY hX hUnion hRawNe hRawAD hRawBox hSource hDirEq hIncU hIncV hMacro
  let Q := localPoints E (physicalCell q height x y) k
  let Z := localHeights E (physicalCell q height x y) height k
  let J := OriginalSelectedAngularIncidences.incidences Q fine source
  let u := NativeRescaledMacroTubeCount.scalarSlope D cells a N parent
  let v := NativeRescaledMacroTubeCount.normalSlope D cells a N parent
  have hq : 0 < q := hd.trans_le hdq
  have hq1 : q ≤ 1 := by linarith
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hQE : Q ⊆ E := filter_subset _ _
  obtain ⟨xi0,Psi,hPsiAD,hPsiBox,hXiQ,hCoverQ⟩ := hMacro k hk
  have hF : ∀ p ∈ E, ‖F (height p)‖ ≤ 1 := by
    intro p hp
    exact matrix_entry_operator_bound (F (height p))
      (hMat (height p) (mem_image_of_mem _ hp)).1 (hMat (height p) (mem_image_of_mem _ hp)).2
  have hJoint : ∀ p t, (p,t) ∈ J → ∃ phi ∈ fine p,
      |u t-phi| ≤ jointError C0 DirErr*delta ∧
      ‖v t-offset p-F (height p) phi‖ ≤ jointError C0 DirErr*delta := by
    have hh := OriginalSelectedFullDirection.selected_joint_direction_realization Q fine source I0 height offset F u v
      hd.le hC hDir (by norm_num : (0:ℝ)≤1) hSpec hDirEq (fun p hp => hF p (hQE hp))
    simpa only [jointError,one_mul] using hh
  obtain ⟨p0,hp0⟩ := hQne
  have hPointE : ∀ p t, (p,t) ∈ J → p ∈ E := by
    intro p t hpt
    have hp : p ∈ TwoTubePathCollisionCount.points J := mem_image_of_mem Prod.fst hpt
    rw [hJpts] at hp
    exact hQE hp
  have hOcc : ∀ t z, ((pointsAt J height t z).card:ℝ) ≤ (16*IncErr+2)^3 := by
    intro t z
    have hOld := OriginalTubeSliceOccupancy.pointsAt_card_le_of_incidenceResidual E J height x y
      (baseU D cells a N parent) u (baseV D cells a N parent) v hd hInc hPointE hsep
      (fun p t hpt => hIncU p t (hJsub hpt)) (fun p t hpt => hIncV p t (hJsub hpt)) t z
    have hRead : @pointsAt P (Fin n) ℝ (Classical.decEq P) (Classical.decEq (Fin n))
        Real.decidableEq J height t z = pointsAt J height t z := by
      exact congrArg₂ (fun (dP : DecidableEq P) (dT : DecidableEq (Fin n)) =>
        @pointsAt P (Fin n) ℝ dP dT Real.decidableEq J height t z)
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    rw [hRead] at hOld
    exact hOld
  have hheight : ∀ p ∈ TwoTubePathCollisionCount.points J, height p ∈ Z := by
    intro p hp
    rw [hJpts] at hp
    exact mem_image_of_mem _ hp
  have hDeg : ∀ p ∈ TwoTubePathCollisionCount.points J,
      OriginalAngularSourcePopulation.degree delta (192*K^2) kappa C0 ≤ ((tubesAt J p).card:ℝ) := by
    intro p hp
    rw [hJpts] at hp
    exact hDegree p hp
  have hSourceCells : q^kappa*((directionCells (TwoTubePathCollisionCount.tubes J) (q/8) u v).card:ℝ) ≤
      2*K*(directionCost C0 DirErr Cxi L)^3 := by
    have hh := OriginalMacroDirectionSource.original_full_terminal_population J height offset F u v fine Psi
      (F (height p0)) xi0 hq hq1 hdq
      (show 0 ≤ jointError C0 DirErr by unfold jointError; positivity) hXi hL
      (by norm_num : (0:ℝ)≤1) hK0.le (hF p0 (hQE hp0)) hJoint
      (fun p hp phi hphi => (hfine p (by rwa [hJpts] at hp)).2.2.2.1 phi hphi)
      (fun p hp phi hphi => by
        rw [hJpts] at hp
        obtain ⟨b,hb,hpb⟩ := hCoverQ p hp phi ((hfine p hp).2.1 hphi)
        exact ⟨b,hb,by simpa only [Real.dist_eq] using hpb⟩)
      (fun p hp => hXiQ p (by rwa [hJpts] at hp))
      (fun p hp => by
        rw [hJpts] at hp
        apply hosc (height p) (mem_image_of_mem _ (hQE hp)) (height p0) (mem_image_of_mem _ (hQE hp0))
        exact congrArg Prod.fst ((mem_filter.mp hp).2.trans (mem_filter.mp hp0).2.symm))
      hPsiAD hPsiBox
    have he : 16*(jointError C0 DirErr+Cxi+L+2*(1:ℝ)+2)+2=directionCost C0 DirErr Cxi L := by
      unfold directionCost
      ring
    simpa only [he] using hh
  have hKg : 0 < 192*K^2 := by positivity
  have hDp := OriginalAngularSourcePopulation.degree_pos (kappa := kappa) hd hKg hC
  have hUp := OriginalAngularSourcePopulation.ballCap_pos (kappa := kappa) hd hq hKg
    (show 0 ≤ 2*C0 by positivity)
  obtain ⟨S,hSV,hS,hhalf,hrich⟩ := exists_full_direction_reference_core J height u v Z Phi hJne hPhiNe
    hq hq1 (show q/8 ≤ C0*delta+q by nlinarith [mul_nonneg hC hd.le])
    (show 0 < (16*IncErr+2)^3 by positivity) hDp hUp
    (densityCoefficient_pos hK0 hC hDir hXi hL hInc).le
    (show 0 < 2*K*(directionCost C0 DirErr Cxi L)^3 by unfold directionCost jointError; positivity)
    hKg hPhiAD hNear hheight hOcc hDeg hDen hRefBall hSourceCells
  refine ⟨k,hk,fine,Phi,source,OriginalReferenceAngleSelection.angle J u Phi hPhiNe (C0*delta+q) hNear,
    ⟨p0,hp0⟩,hJsub,hJne,hJpts,hPhiSub,hPhiSep,hPhiBox,hPhiAD,hPhiNe,hRatio,?_,hHeight,S,hSV,hS,hhalf,?_⟩
  · exact OriginalReferenceAngleSelection.angle_spec J u Phi hPhiNe (C0*delta+q) hNear
  · exact hrich
end NativeOriginalMacroPrintedCore
