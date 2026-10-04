import Theorems.Thm_StickyKakeya4_native_rescaled_macro_tube_count
import Theorems.Thm_StickyKakeya4_original_macro_height_incidence_density
import Theorems.Thm_StickyKakeya4_original_selected_full_direction
import Theorems.Thm_StickyKakeya4_original_literal_dense_macro_height
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeOriginalMacroSourceDensity
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open OriginalWGrainDrift OriginalMacroGrainReadback OriginalLiteralGrainProfiles
open OriginalLiteralMacroDensity OriginalLiteralDenseMacroHeight OriginalWeightedMacroSelection
open OriginalPhaseCellPopulation NativeTangentGridCoarsening OriginalWPhysicalDisplacement
open OriginalLiteralHeightWindow OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
def jointError (C0 DirErr : ℝ) : ℝ := C0+DirErr+C0
def pointCost (K : ℝ) : ℝ := 79626240000*K^4
def directionCost (C0 DirErr Cxi L : ℝ) : ℝ := 16*(jointError C0 DirErr+Cxi+L+4)+2
def tubeCost (K C0 DirErr Cxi L : ℝ) : ℝ := 65536*K*(directionCost C0 DirErr Cxi L)^3
def densityCoefficient (K C0 DirErr Cxi L IncErr : ℝ) : ℝ :=
  (1/((192*K^2)*(2*C0+2)))/(pointCost K*tubeCost K C0 DirErr Cxi L*(16*IncErr+2)^3)
def baseU {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (parent : Parent) (t : Fin n) : ℝ := (data D cells a N parent).offset t (0:Fin 3)/32
def baseV {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (parent : Parent) (t : Fin n) : ℝ × ℝ :=
  ((data D cells a N parent).offset t (1:Fin 3)/32,(data D cells a N parent).offset t (2:Fin 3)/32)
theorem densityCoefficient_pos {K C0 DirErr Cxi L IncErr : ℝ}
    (hK : 0 < K) (hC : 0 ≤ C0) (hD : 0 ≤ DirErr) (hXi : 0 ≤ Cxi)
    (hL : 0 ≤ L) (hI : 0 ≤ IncErr) : 0 < densityCoefficient K C0 DirErr Cxi L IncErr := by
  unfold densityCoefficient pointCost tubeCost directionCost jointError
  positivity
/-- The original global height/Y/X laws and original pointwise Phi/tube
 realization select ONE whole original macro-cell and ONE actual angular
 incidence family. Its Eq146 average height/tube density is derived from
 the original native source, actual parent slopes and original geometry.
 No macro population, tube count, vertex density, or W-mass certificate is
 an input to this constructor. -/
theorem exists_original_macro_angle_density {P : Type*} [DecidableEq P] {n : ℕ}
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
      ∃ Phi : Finset ℝ, ∃ source : P → ℝ → Fin n,
      let Q := localPoints E (physicalCell q height x y) k
      let J := OriginalSelectedAngularIncidences.incidences Q fine source
      let Z := localHeights E (physicalCell q height x y) height k
      Q.Nonempty ∧
      (∀ p ∈ Q, (fine p).Nonempty ∧ fine p ⊆ raw p ∧ Separated (fine p) delta ∧
        (∀ phi ∈ fine p, |phi| ≤ 1) ∧ ADBounds (fine p) delta (192*K^2) kappa) ∧
      Phi ⊆ Q.biUnion raw ∧ Separated Phi q ∧ (∀ b ∈ Phi, |b| ≤ 1) ∧
      ADBounds Phi q (192*K^2) kappa ∧ Phi.Nonempty ∧
      J ⊆ I0 ∧ J.Nonempty ∧ TwoTubePathCollisionCount.points J=Q ∧
      (∀ p ∈ Q, ∀ phi ∈ fine p, (p,source p phi) ∈ I0 ∧
        |NativeRescaledMacroTubeCount.scalarSlope D cells a N parent (source p phi)-phi| ≤ C0*delta) ∧
      (∀ p ∈ Q, OriginalAngularSourcePopulation.degree delta (192*K^2) kappa C0 ≤ ((tubesAt J p).card:ℝ)) ∧
      (∀ p b, (((tubesAt J p).filter (fun t =>
        |NativeRescaledMacroTubeCount.scalarSlope D cells a N parent t-b| ≤ C0*delta+q)).card:ℝ) ≤
          OriginalAngularSourcePopulation.ballCap delta q (192*K^2) kappa (2*C0)) ∧
      (∀ t ∈ TwoTubePathCollisionCount.tubes J, ∃ b ∈ Phi,
        |NativeRescaledMacroTubeCount.scalarSlope D cells a N parent t-b| ≤ C0*delta+q) ∧
      OriginalAngularSourcePopulation.ballCap delta q (192*K^2) kappa (2*C0)*(Phi.card:ℝ)/
        OriginalAngularSourcePopulation.degree delta (192*K^2) kappa C0 ≤ 512*(192*K^2)^3*(1+C0)^3 ∧
      (∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → delta ≤ |z-w|) ∧
      q^(3-kappa)*(Z.card:ℝ) ≤ pointCost K*delta^(3-kappa)*(Q.card:ℝ) ∧
      (Q.card:ℝ) ≤ 155520*K*(q/delta)^(3-kappa)*(Z.card:ℝ) ∧
      q ≤ 124416000*K^5*(2*L+4)^2*delta*(Z.card:ℝ) ∧
      densityCoefficient K C0 DirErr Cxi L IncErr*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes J).card ≤
        (vertices J height).card := by
  have hq : 0 < q := hd.trans_le hdq
  have hq1 : q ≤ 1 := by linarith
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hE : E.Nonempty := by
    by_contra hn
    have he := not_nonempty_iff_eq_empty.mp hn
    simp only [he,image_empty,card_empty,Nat.cast_zero,mul_zero] at hZmass
    linarith
  obtain ⟨p00,hp00⟩ := hE
  obtain ⟨_xi00,Phi00,hAD00,hBox00,_hXi00,hCover00⟩ := hMacro (physicalCell q height x y p00) (mem_image_of_mem _ hp00)
  obtain ⟨phi00,hphi00⟩ := hRawNe p00 hp00
  obtain ⟨b00,hb00,_⟩ := hCover00 p00 (mem_filter.mpr ⟨hp00,rfl⟩) phi00 hphi00
  have hk2 : kappa ≤ 2 := (OriginalLiteralAngularReadback.cover_exponent_lt_two Phi00 ⟨b00,hb00⟩
    hq hq1 hK hsmall hAD00 hBox00).le
  obtain ⟨k,hk,hQne,hPoint,hUpper,hHeight⟩ := exists_original_macro_with_height_population E height x y F
    hd hdq hq4 hK (show 0 ≤ 2-kappa by linarith) (show 2-kappa ≤ 2 by linarith) hL
    hZbox hZmass hx hMat hosc hsep hYbox hY hX hUnion
  rw [show (2-kappa)+1=3-kappa by ring] at hPoint hUpper
  let Q := localPoints E (physicalCell q height x y) k
  let Z := localHeights E (physicalCell q height x y) height k
  let u := NativeRescaledMacroTubeCount.scalarSlope D cells a N parent
  let v := NativeRescaledMacroTubeCount.normalSlope D cells a N parent
  have hQE : Q ⊆ E := filter_subset _ _
  obtain ⟨xi0,Psi,hPsiAD,hPsiBox,hXiQ,hCoverQ⟩ := hMacro k hk
  obtain ⟨fine,Phi,hfine,hPhiSub,hPhiSep,hPhiBox,hPhiAD,source,hJsub,hJne,hJpts,hSpec,
    hDegree,_hBall,hRefBall,hNear,hPhiNe,_hPhiCard,_hRatio,hRefRatio⟩ :=
    OriginalLiteralAngularIncidences.exists_literal_angular_population_supplier Q raw I0 u Psi
      hd hdq hq1 hK hkappa hsmall hC hQne
      (fun p hp => hRawNe p (hQE hp)) (fun p hp => hRawAD p (hQE hp))
      (fun p hp => hRawBox p (hQE hp)) (fun p hp => hSource p (hQE hp))
      hPsiAD hPsiBox hCoverQ
  let J := OriginalSelectedAngularIncidences.incidences Q fine source
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
  have hoscQ : ∀ p ∈ Q, ‖F (height p)-F (height p0)‖ ≤ L*q := by
    intro p hp
    apply hosc (height p) (mem_image_of_mem _ (hQE hp)) (height p0) (mem_image_of_mem _ (hQE hp0))
    exact congrArg Prod.fst ((mem_filter.mp hp).2.trans (mem_filter.mp hp0).2.symm)
  have hFineBox : ∀ p ∈ TwoTubePathCollisionCount.points J, ∀ phi ∈ fine p, |phi| ≤ 1 := by
    intro p hp
    rw [hJpts] at hp
    exact (hfine p hp).2.2.2.2.1
  have hFineCover : ∀ p ∈ TwoTubePathCollisionCount.points J, ∀ phi ∈ fine p,
      ∃ b ∈ Psi, |phi-b| ≤ q := by
    intro p hp phi hphi
    rw [hJpts] at hp
    obtain ⟨b,hb,hpb⟩ := hCoverQ p hp phi ((hfine p hp).2.1 hphi)
    exact ⟨b,hb,by simpa only [Real.dist_eq] using hpb⟩
  have hXiJ : ∀ p ∈ TwoTubePathCollisionCount.points J, ‖offset p-xi0‖ ≤ Cxi*q := by
    intro p hp
    rw [hJpts] at hp
    exact hXiQ p hp
  have hOscJ : ∀ p ∈ TwoTubePathCollisionCount.points J, ‖F (height p)-F (height p0)‖ ≤ L*q := by
    intro p hp
    rw [hJpts] at hp
    exact hoscQ p hp
  have hTube : q^kappa*((TwoTubePathCollisionCount.tubes J).card:ℝ) ≤
      tubeCost K C0 DirErr Cxi L*(q/delta)^3 := by
    have hh := NativeRescaledMacroTubeCount.rescaled_original_macro_tube_population hD cells a N hN parent J
      height offset F fine Psi (F (height p0)) xi0 hd hscale hq1 hdq
      (show 0 ≤ jointError C0 DirErr by unfold jointError; positivity) hXi hL
      (by norm_num : (0:ℝ)≤1) hK0.le (hF p0 (hQE hp0))
      hJoint hFineBox hFineCover hXiJ hOscJ hPsiAD hPsiBox
    have he : 16*(jointError C0 DirErr+Cxi+L+2*(1:ℝ)+2)+2=directionCost C0 DirErr Cxi L := by
      unfold directionCost
      ring
    simpa only [he,tubeCost] using hh
  have hDegreeJ : ∀ p ∈ TwoTubePathCollisionCount.points J,
      OriginalAngularSourcePopulation.degree delta (192*K^2) kappa C0 ≤ ((tubesAt J p).card:ℝ) := by
    intro p hp
    rw [hJpts] at hp
    exact hDegree p hp
  have hDegreePower := OriginalMacroHeightIncidenceDensity.original_degree_power_mass J hd hDegreeJ
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
  have hPointJ : q^(3-kappa)*(Z.card:ℝ) ≤ pointCost K*delta^(3-kappa)*(TwoTubePathCollisionCount.points J).card := by
    rw [hJpts]
    exact hPoint
  have hDen := OriginalMacroHeightIncidenceDensity.original_height_density_from_source_counts J height Z hd hq
    (show 0 < pointCost K by unfold pointCost; positivity)
    (show 0 < tubeCost K C0 DirErr Cxi L by unfold tubeCost directionCost jointError; positivity)
    (show 0 < (16*IncErr+2)^3 by positivity) (show 0 ≤ 1/((192*K^2)*(2*C0+2)) by positivity)
    hPointJ hDegreePower hTube hOcc
  have hZE : Z ⊆ E.image height := image_subset_image hQE
  refine ⟨k,hk,fine,Phi,source,⟨p0,hp0⟩,?_,hPhiSub,hPhiSep,hPhiBox,hPhiAD,hPhiNe,
    hJsub,hJne,hJpts,hSpec,hDegree,hRefBall,hNear,?_,?_,hPoint,hUpper,hHeight,?_⟩
  · intro p hp
    have hf := hfine p hp
    exact ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.2.1,hf.2.2.2.2.2⟩
  · exact hRefRatio.trans_eq (by ring)
  · intro z hz w hw hzw
    exact hZsep z (hZE hz) w (hZE hw) hzw
  · exact hDen
end NativeOriginalMacroSourceDensity
