import Theorems.Thm_StickyKakeya4_native_variable_height_population
import Theorems.Thm_StickyKakeya4_native_variable_height_numerator_upper
import Theorems.Thm_StickyKakeya4_native_reference_column_exponents
import Theorems.Thm_StickyKakeya4_native_anisotropic_pair_numerator
import Theorems.Thm_StickyKakeya4_native_phase_height_population
import Theorems.Thm_StickyKakeya4_native_slice_population_algebra

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeVariableHeightReferenceCounts
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent
open NativeAnisotropicGlobalSourceBridge NativeAnisotropicPairNumerator NativeSliceCountComparison
open NativePhaseHeightPopulation NativeActivePhasePopulation NativeSlicePopulationAlgebra
open NativeIncidenceMultiplicityTower NativeMiddleWindowBalance

open NativeHeightWindowRelations NativeVariableHeightPopulation NativeReferenceColumnExponents NativeColumnPopulationBounds

lemma column_point_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f b : ℕ)
    (E : Finset (Fin n × Index)) (p : Parent) :
    (((parentEdges D a (2^m) E p).image (NativeVariableHeightPopulation.columnPair D a m f b p)).image Prod.snd)=NativeHeightWindowRelations.points D a m f b E p := by
  simp only [NativeHeightWindowRelations.points,NativeVariableHeightPopulation.columnPair,image_image,Function.comp_def]


lemma column_multiplicity_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f b : ℕ)
    (E : Finset (Fin n × Index)) (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty) :
    multiplicity ((parentEdges D a (2^m) E p).image (NativeVariableHeightPopulation.columnPair D a m f b p))*(NativeHeightWindowRelations.points D a m f b E p).card=
      (((parentEdges D a (2^m) E p).image (NativeVariableHeightPopulation.columnPair D a m f b p)).card:ℝ) := by
  have hP : (0:ℝ)<(NativeHeightWindowRelations.points D a m f b E p).card := by exact_mod_cast card_pos.mpr (hp.image _)
  rw [NativeIncidenceMultiplicityTower.multiplicity,column_point_image]
  exact div_mul_cancel₀ _ hP.ne'


theorem reference_numerator_height_bounds {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m f b : ℕ) (hmf : m ≤ f) (hbf : b ≤ f) (hfL : f ≤ level) (hb6 : 6 ≤ b)
    (hwindow : (64/((2^m:ℕ):ℝ))*(64/((2^b:ℕ):ℝ)) ≤ 8*(64/((2^f:ℕ):ℝ)))
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty)
    (population : ℝ) (hpopulation : 0 ≤ population)
    (hret : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card) :
    let P := NativeHeightWindowRelations.points D a m f b E p
    let I := ((parentEdges D a (2^m) E p).image (NativeVariableHeightPopulation.columnPair D a m f b p)).card
    let Z := (P.image (fun q => q (3:Fin 4))).card
    let H := 64/((2^b:ℕ):ℝ)
    (population*D.thickness^(2*zeta)/43904)*(relativeWidth m f)^(-3:ℝ) ≤ H*I ∧
      H*I ≤ (NativeVariableHeightNumeratorUpper.pairUpperConstant*D.thickness^(-2*zeta))*(relativeWidth m f)^(-3:ℝ) ∧
      population/43904 ≤ H*Z ∧ H*Z ≤ 10 := by
  intro P I Z H
  let F := parentEdges D a (2^m) E p
  have hF : F⊆retained original R := (filter_subset _ _).trans hE
  have hFo : F⊆incidences original := hF.trans (filter_subset _ _)
  have hparent : ∀z∈F,parentLabel D a (2^m) z.1=p := fun _z hz => (mem_filter.mp hz).2
  have hphase := active_phase_population h original R level Hbackbone m f hmf hfL F hF hp p hparent
    population hpopulation hret
  have hphaseheight := NativeVariableHeightPopulation.phase_height_population h original R level Hbackbone m f b hmf hfL (hbf.trans hfL) F hF hp p hparent
    population hpopulation hret
  have hheight := NativeVariableHeightPopulation.parent_height_population h original R level Hbackbone m b (hbf.trans hfL)
    F hF hp p hparent population hret
  have hheightU := NativePhaseHeightPopulation.height_population_upper h original Hbackbone.1 Hbackbone.2.2.1 H
    (by positivity) (NativeCoarseShadingPruning.coarse_thickness_le_one b hb6) F hFo
  have hpair := NativeVariableHeightNumeratorUpper.parent_column_pair_upper h original Hbackbone.1 Hbackbone.2.2.1 level f m b
    Hbackbone.2.1 hb6 (hbf.trans hfL) hfL hwindow (NativeCoarseDirectionThinning.representative h R a (2^f))
    E (hE.trans (filter_subset _ _)) p
  have hJ : (phaseHeightLabels D a H f F).card ≤ I := by
    rw [←NativeVariableHeightPopulation.column_phase_height_image D a m f b E p]
    exact card_image_le
  have hJr : ((phaseHeightLabels D a H f F).card:ℝ) ≤ I := by exact_mod_cast hJ
  have hIlo : population*D.thickness^(2*zeta)*(relativeWidth m f)^(-3:ℝ) ≤ 43904*(H*I) := by
    rw [←inverse_scale_cube]
    exact (hphaseheight.trans (mul_le_mul_of_nonneg_left hJr (by positivity))).trans_eq (by ring)
  have hIhi : H*I ≤ (NativeVariableHeightNumeratorUpper.pairUpperConstant*D.thickness^(-2*zeta))*(relativeWidth m f)^(-3:ℝ) := by
    calc
      _ ≤ NativeVariableHeightNumeratorUpper.pairUpperConstant*(activePhases D a f F).card := hpair
      _ ≤ NativeVariableHeightNumeratorUpper.pairUpperConstant*(D.thickness^(-2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3) :=
        mul_le_mul_of_nonneg_left hphase.2 NativeVariableHeightNumeratorUpper.pairUpperConstant_pos.le
      _ = _ := by rw [inverse_scale_cube]; ring
  have hZ : (heightLabels D a H F).card=Z := by rw [←NativeVariableHeightPopulation.column_height_image D a m f b E p]
  rw [hZ] at hheight hheightU
  refine ⟨?_,hIhi,?_,hheightU⟩
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<43904)).mpr
    simpa only [mul_comm] using hIlo
  · apply (div_le_iff₀ (by norm_num : (0:ℝ)<43904)).mpr
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hheight

theorem reference_column_point_power_bounds {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m f b : ℕ) (hmf : m ≤ f) (hbf : b ≤ f) (hfL : f ≤ level) (hb6 : 6 ≤ b)
    (hwindow : (64/((2^m:ℕ):ℝ))*(64/((2^b:ℕ):ℝ)) ≤ 8*(64/((2^f:ℕ):ℝ)))
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty)
    (population : ℝ) (hpopulation : 0 < population)
    (hret : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (profileLower profileUpper : ℝ) (hL : 0 < profileLower) (hU : 0 < profileUpper)
    (Hprofile : profileLower*(relativeWidth m f)^(-extremalExponent) ≤
        multiplicity ((parentEdges D a (2^m) E p).image (NativeVariableHeightPopulation.columnPair D a m f b p)) ∧
      multiplicity ((parentEdges D a (2^m) E p).image (NativeVariableHeightPopulation.columnPair D a m f b p)) ≤
        profileUpper*(relativeWidth m f)^(-extremalExponent)) :
    lowerCountCoefficient D.thickness zeta population profileUpper*(relativeWidth m f)^(extremalExponent-3) ≤
        (64/((2^b:ℕ):ℝ))*(NativeHeightWindowRelations.points D a m f b E p).card ∧
      (64/((2^b:ℕ):ℝ))*(NativeHeightWindowRelations.points D a m f b E p).card ≤
        ((NativeVariableHeightNumeratorUpper.pairUpperConstant*D.thickness^(-2*zeta))/profileLower)*(relativeWidth m f)^(extremalExponent-3) := by
  have hb := reference_numerator_height_bounds h original R level Hbackbone m f b hmf hbf hfL hb6 hwindow
    E hE p hp population hpopulation.le hret
  have hh := quotient_power_bounds (by positivity : (0:ℝ)<64/((2^b:ℕ):ℝ))
    (relativeWidth_pos m f) (Nat.cast_nonneg (NativeHeightWindowRelations.points D a m f b E p).card) hL hU
    (column_multiplicity_card D a m f b E p hp) hb.1 hb.2.1 Hprofile.1 Hprofile.2
  exact hh


end NativeVariableHeightReferenceCounts
