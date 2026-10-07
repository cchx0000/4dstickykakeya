import Theorems.Thm_StickyKakeya4_native_anisotropic_pair_numerator
import Theorems.Thm_StickyKakeya4_native_phase_height_population
import Theorems.Thm_StickyKakeya4_native_slice_population_algebra

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeColumnPopulationBounds
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent
open NativeAnisotropicGlobalSourceBridge NativeAnisotropicPairNumerator NativeSliceCountComparison
open NativePhaseHeightPopulation NativeActivePhasePopulation NativeSlicePopulationAlgebra
open NativeIncidenceMultiplicityTower NativeMiddleWindowBalance

def relativeWidth (m f : ℕ) : ℝ := (64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ))

lemma relativeWidth_pos (m f : ℕ) : 0 < relativeWidth m f := by dsimp [relativeWidth]; positivity

lemma inverse_scale_cube (m f : ℕ) :
    (((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3=(relativeWidth m f)^(-3:ℝ) := by
  rw [Real.rpow_neg (relativeWidth_pos m f).le]
  rw [show (3:ℝ)=((3:ℕ):ℝ) by norm_num,Real.rpow_natCast]
  dsimp only [relativeWidth]
  field_simp

lemma column_point_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ)
    (E : Finset (Fin n × Index)) (p : Parent) :
    (((parentEdges D a (2^m) E p).image (columnPair D a m f p)).image Prod.snd)=points D a m f E p := by
  simp only [points,columnPair,image_image,Function.comp_def]

lemma column_phase_height_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ)
    (E : Finset (Fin n × Index)) (p : Parent) :
    (((parentEdges D a (2^m) E p).image (columnPair D a m f p)).image
      (fun q => (q.1,q.2 (3:Fin 4))))=
      phaseHeightLabels D a (64/((2^m:ℕ):ℝ)) f (parentEdges D a (2^m) E p) := by
  simp only [phaseHeightLabels,columnPair,image_image,Function.comp_def,column_height_readback]

lemma column_height_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ)
    (E : Finset (Fin n × Index)) (p : Parent) :
    (points D a m f E p).image (fun q => q (3:Fin 4))=
      heightLabels D a (64/((2^m:ℕ):ℝ)) (parentEdges D a (2^m) E p) := by
  simp only [heightLabels,points,image_image,Function.comp_def,column_height_readback]

lemma column_multiplicity_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ)
    (E : Finset (Fin n × Index)) (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty) :
    multiplicity ((parentEdges D a (2^m) E p).image (columnPair D a m f p))*(points D a m f E p).card=
      (((parentEdges D a (2^m) E p).image (columnPair D a m f p)).card:ℝ) := by
  have hP : (0:ℝ)<(points D a m f E p).card := by exact_mod_cast card_pos.mpr (hp.image _)
  rw [NativeIncidenceMultiplicityTower.multiplicity,column_point_image]
  exact div_mul_cancel₀ _ hP.ne'

/-- The chosen parent's ACTUAL source population supplies the three-dimensional
pair numerator and occupied-height counts. Total shading density is used
only through the proved local population inequality; no per-tube lower is assumed. -/
theorem reference_numerator_height_bounds {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m f : ℕ) (hm6 : 6 ≤ m) (hmf : m ≤ f) (hfL : f ≤ level)
    (hwindow : (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^f:ℕ):ℝ))
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty)
    (population : ℝ) (hpopulation : 0 ≤ population)
    (hret : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card) :
    let P := points D a m f E p
    let I := ((parentEdges D a (2^m) E p).image (columnPair D a m f p)).card
    let Z := (P.image (fun q => q (3:Fin 4))).card
    let H := 64/((2^m:ℕ):ℝ)
    (population*D.thickness^(2*zeta)/43904)*(relativeWidth m f)^(-3:ℝ) ≤ H*I ∧
      H*I ≤ (pairUpperConstant*D.thickness^(-2*zeta))*(relativeWidth m f)^(-3:ℝ) ∧
      population/43904 ≤ H*Z ∧ H*Z ≤ 10 := by
  intro P I Z H
  let F := parentEdges D a (2^m) E p
  have hF : F⊆retained original R := (filter_subset _ _).trans hE
  have hFo : F⊆incidences original := hF.trans (filter_subset _ _)
  have hparent : ∀z∈F,parentLabel D a (2^m) z.1=p := fun _z hz => (mem_filter.mp hz).2
  have hphase := active_phase_population h original R level Hbackbone m f hmf hfL F hF hp p hparent
    population hpopulation hret
  have hphaseheight := phase_height_population h original R level Hbackbone m f hmf hfL F hF hp p hparent
    population hpopulation hret
  have hheight := parent_height_population h original R level Hbackbone m (hmf.trans hfL)
    F hF hp p hparent population hret
  have hheightU := height_population_upper h original Hbackbone.1 Hbackbone.2.2.1 H
    (by positivity) (NativeCoarseShadingPruning.coarse_thickness_le_one m hm6) F hFo
  have hpair := parent_column_pair_upper h original Hbackbone.1 Hbackbone.2.2.1 level f m
    Hbackbone.2.1 hm6 (hmf.trans hfL) hfL hwindow (NativeCoarseDirectionThinning.representative h R a (2^f))
    E (hE.trans (filter_subset _ _)) p
  have hJ : (phaseHeightLabels D a H f F).card ≤ I := by
    rw [←column_phase_height_image D a m f E p]
    exact card_image_le
  have hJr : ((phaseHeightLabels D a H f F).card:ℝ) ≤ I := by exact_mod_cast hJ
  have hIlo : population*D.thickness^(2*zeta)*(relativeWidth m f)^(-3:ℝ) ≤ 43904*(H*I) := by
    rw [←inverse_scale_cube]
    exact (hphaseheight.trans (mul_le_mul_of_nonneg_left hJr (by positivity))).trans_eq (by ring)
  have hIhi : H*I ≤ (pairUpperConstant*D.thickness^(-2*zeta))*(relativeWidth m f)^(-3:ℝ) := by
    calc
      _ ≤ pairUpperConstant*(activePhases D a f F).card := hpair
      _ ≤ pairUpperConstant*(D.thickness^(-2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3) :=
        mul_le_mul_of_nonneg_left hphase.2 pairUpperConstant_pos.le
      _ = _ := by rw [inverse_scale_cube]; ring
  have hZ : (heightLabels D a H F).card=Z := by rw [←column_height_image D a m f E p]
  rw [hZ] at hheight hheightU
  refine ⟨?_,hIhi,?_,hheightU⟩
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<43904)).mpr
    simpa only [mul_comm] using hIlo
  · apply (div_le_iff₀ (by norm_num : (0:ℝ)<43904)).mpr
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hheight

end NativeColumnPopulationBounds
