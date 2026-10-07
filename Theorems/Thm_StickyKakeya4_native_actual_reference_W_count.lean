import Theorems.Thm_StickyKakeya4_native_retained_column_pair_core
import Theorems.Thm_StickyKakeya4_native_actual_reference_W_geometry
import Theorems.Thm_StickyKakeya4_native_reference_slice_class_bounds
import Theorems.Thm_StickyKakeya4_original_height_vertex_density

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

noncomputable section
namespace NativeActualReferenceWCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeAnisotropicGlobalSourceBridge
open NativeColumnPopulationBounds NativePhaseHeightPopulation NativeActivePhasePopulation
open NativeSliceCountComparison NativeReferenceSliceClassBounds NativeFixedCompactKakeyaExponent
open NativeRetainedColumnPairCore NativeActualReferenceWGeometry OriginalWWitnessCounts
open OriginalWCoarseEscapeMenus OriginalScalarCollisionMass OriginalHeightVertexDensity
open NativeMiddleWindowBalance

lemma point_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ) (p : Parent)
    (H : Finset (Fin n × Index)) :
    TwoTubePathCollisionCount.points (NativeActualReferenceWGeometry.incidences D a m f p H)=
      (H.image (columnPair D a m f p)).image Prod.snd := by
  simp only [TwoTubePathCollisionCount.points,NativeActualReferenceWGeometry.incidences,
    image_image,Function.comp_def]

lemma tube_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ) (p : Parent)
    (H : Finset (Fin n × Index)) :
    TwoTubePathCollisionCount.tubes (NativeActualReferenceWGeometry.incidences D a m f p H)=
      activePhases D a f H := by
  simp only [TwoTubePathCollisionCount.tubes,NativeActualReferenceWGeometry.incidences,
    columnPair,activePhases,image_image,Function.comp_def]

/-- The preinstalled pair relation and actual original parent population
produce all incidence/height inputs to W counting on the retained geometric
graph. The terminal alphabet is its ACTUAL image; no desired menu exponent
or W-mass premise is imposed. -/
theorem retained_original_W_count {K : Type*} [DecidableEq K]
    {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m f : ℕ) (hm6 : 6 ≤ m) (hmf : m ≤ f) (hfL : f ≤ level)
    (hwindow : (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^f:ℕ):ℝ))
    (E H : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (p : Parent) (hH : H⊆parentEdges D a (2^m) E p) (hHn : H.Nonempty)
    (population : ℝ) (hpopulation : 0 < population)
    (hpop : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (profileLower profileUpper : ℝ) (hL : 0 < profileLower)
    (Hprofile : HasColumnPowerProfile D a m f E p profileLower profileUpper)
    (Q : ℕ) (hQ : 0 < Q)
    (HU : HasUniformFibers (parentEdges D a (2^m) E p) Q (columnPair D a m f p))
    (lambda G : ℝ) (hlambda : 0 < lambda) (hG : 0 < G)
    (hret : lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ G*H.card)
    (cell : Parent → K) :
    let I := NativeActualReferenceWGeometry.incidences D a m f p H
    let height := fun k : Index => k (3:Fin 4)
    let Z := (TwoTubePathCollisionCount.points I).image height
    let keep := lambda/(G*(Q:ℝ)^2)
    let d := keep*profileLower*(relativeWidth m f)^(-extremalExponent)
    let density := (keep*(population*D.thickness^(2*zeta)/43904))/D.thickness^(-2*zeta)
    let heightDensity := density/((heightColumnCost:ℝ)*10)
    I.Nonempty ∧ 0 < d ∧ 0 < heightDensity ∧
      (∀t z,((pointsAt I height t z).card:ℝ) ≤ heightColumnCost) ∧
      d*(TwoTubePathCollisionCount.points I).card ≤ (I.card:ℝ) ∧
      heightDensity*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card ≤ (vertices I height).card ∧
      d^3*heightDensity^4*(Z.card:ℝ)^2*(vertices I height).card ≤
        (((TwoTubePathCollisionCount.tubes I).image cell).card:ℝ)*(witnesses I height cell).card := by
  intro I height Z keep d density heightDensity
  let F := parentEdges D a (2^m) E p
  let heightWidth : ℝ := 64/((2^m:ℕ):ℝ)
  let volumeScale : ℝ := (relativeWidth m f)^(-3:ℝ)
  have hFn : F.Nonempty := hHn.mono hH
  have hFret : F⊆retained original R := (filter_subset _ _).trans hE
  have hForig : F⊆NativeCubicalIncidenceCounts.incidences original := hFret.trans (filter_subset _ _)
  have hHorig : H⊆NativeCubicalIncidenceCounts.incidences original := hH.trans hForig
  have hHp : ∀z∈H,parentLabel D a (2^m) z.1=p := fun z hz => (mem_filter.mp (hH hz)).2
  have hIp : I.Nonempty := hHn.image _
  have hIcard : (I.card:ℝ)=(H.image (columnPair D a m f p)).card := by rw [incidence_card]
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hkeep : 0 < keep := by dsimp [keep]; positivity
  have hHeightWidth : 0 < heightWidth := by dsimp [heightWidth]; positivity
  have hVolume : 0 < volumeScale := by dsimp [volumeScale]; exact Real.rpow_pos_of_pos (relativeWidth_pos m f) _
  have hPhaseCoefficient : 0 < D.thickness^(-2*zeta) := Real.rpow_pos_of_pos h.1.2.1 _
  have hThickness : 0 < D.thickness := h.1.2.1
  have hDensity : 0 < density := by dsimp [density]; positivity
  have hHdensity : 0 < heightDensity := by dsimp [heightDensity,heightColumnCost]; positivity
  have hd : 0 < d := by dsimp [d]; exact mul_pos (mul_pos hkeep hL) (Real.rpow_pos_of_pos (relativeWidth_pos m f) _)
  have hmass := retained_pair_card D a m f E H p Q hH hFn HU lambda G hG.le hret
  have hpairRet : keep*((F.image (columnPair D a m f p)).card:ℝ) ≤ I.card := by
    rw [hIcard]
    dsimp only [keep]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0<G*(Q:ℝ)^2 by positivity)).mpr
    simpa only [mul_comm] using hmass
  have hmu := retained_pair_multiplicity D a m f E H p Q hH hFn HU lambda G hlambda.le hG hQ hret
  have hdMu : d ≤ NativeIncidenceMultiplicityTower.multiplicity (H.image (columnPair D a m f p)) := by
    calc
      _ = keep*(profileLower*(relativeWidth m f)^(-extremalExponent)) := by dsimp [d]; ring
      _ ≤ keep*NativeIncidenceMultiplicityTower.multiplicity (F.image (columnPair D a m f p)) :=
        mul_le_mul_of_nonneg_left Hprofile.1 hkeep.le
      _ ≤ _ := hmu
  have hdDegree : d*(TwoTubePathCollisionCount.points I).card ≤ (I.card:ℝ) := by
    have hPoints : (0:ℝ)<(TwoTubePathCollisionCount.points I).card :=
      Nat.cast_pos.mpr (card_pos.mpr (hIp.image _))
    rw [NativeIncidenceMultiplicityTower.multiplicity,←point_image,←hIcard] at hdMu
    exact (le_div_iff₀ hPoints).mp hdMu
  have hdelta : D.thickness ≤ 64/((2^f:ℕ):ℝ) := by
    have hh : ((2^f:ℕ):ℝ)*D.thickness ≤ 1 := by
      rw [NativeLocalParentScales.relative_scale Hbackbone.2.1 hfL]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hh]
  have hOcc : ∀t z,((pointsAt I height t z).card:ℝ) ≤ heightColumnCost := by
    intro t z
    exact_mod_cast pointsAt_card_bound h original Hbackbone.1 Hbackbone.2.2.1 m f hdelta hwindow p H hHorig hHp t z
  obtain ⟨hPairLower,_hPairUpper,_hHeightLower,hHeightUpper⟩ :=
    reference_numerator_height_bounds h original R level Hbackbone m f hm6 hmf hfL hwindow E hE p hFn
      population hpopulation.le hpop
  have hNumerator : (keep*(population*D.thickness^(2*zeta)/43904))*volumeScale ≤ heightWidth*I.card := by
    calc
      _ = keep*((population*D.thickness^(2*zeta)/43904)*volumeScale) := by ring
      _ ≤ keep*(heightWidth*(F.image (columnPair D a m f p)).card) :=
        mul_le_mul_of_nonneg_left hPairLower hkeep.le
      _ = heightWidth*(keep*(F.image (columnPair D a m f p)).card) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpairRet hHeightWidth.le
  have hTubeUpper : ((TwoTubePathCollisionCount.tubes I).card:ℝ) ≤ D.thickness^(-2*zeta)*volumeScale := by
    have hPhase := (active_phase_population h original R level Hbackbone m f hmf hfL F hFret hFn p
      (fun z hz => (mem_filter.mp hz).2) population hpopulation.le hpop).2
    rw [inverse_scale_cube] at hPhase
    rw [tube_image]
    exact (Nat.cast_le.mpr (card_le_card (image_subset_image hH))).trans hPhase
  have hIncDensity : density*(TwoTubePathCollisionCount.tubes I).card ≤ heightWidth*I.card := by
    calc
      _ ≤ density*(D.thickness^(-2*zeta)*volumeScale) := mul_le_mul_of_nonneg_left hTubeUpper hDensity.le
      _ = (keep*(population*D.thickness^(2*zeta)/43904))*volumeScale := by
        dsimp [density]
        field_simp [hPhaseCoefficient.ne']
      _ ≤ _ := hNumerator
  have hZUpper : heightWidth*(Z.card:ℝ) ≤ 10 := by
    have hZsub : Z⊆(points D a m f E p).image (fun k => k (3:Fin 4)) := by
      dsimp only [Z]
      apply image_subset_image
      rw [point_image,←column_point_image]
      exact image_subset_image (image_subset_image hH)
    exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hZsub)) hHeightWidth.le).trans hHeightUpper
  have hAverage : heightDensity*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card ≤ (vertices I height).card :=
    original_average_height_density I height Z hHeightWidth.le
      (by norm_num [heightColumnCost] : (0:ℝ)<heightColumnCost) (by norm_num : (0:ℝ)<10)
      hOcc hIncDensity hZUpper
  refine ⟨hIp,hd,hHdensity,hOcc,hdDegree,hAverage,?_⟩
  exact original_incidence_population_collision_mass I height cell Z hIp
    (fun k hk => mem_image_of_mem height hk) hd.le hHdensity.le hdDegree hAverage

end NativeActualReferenceWCount
