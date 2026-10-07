import Theorems.Thm_StickyKakeya4_marked_isometric_carrier
import Theorems.Thm_StickyKakeya4_wang_zakharov_finite_interface
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable section
namespace MarkedIsometricFiniteTransport
open Classical Finset StickyKakeya4 MeasureTheory MarkedIsometricChart
open scoped BigOperators ENNReal RealInnerProductSpace

lemma line_injective (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) :
    Function.Injective (MarkedIsometricChart.line O c) := by
  intro l l' h
  have hh := congrArg (MarkedIsometricChart.line O.symm (-O c)) h
  simpa only [MarkedIsometricCarrier.line_inverse] using hh

def carrierMap (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (p : E4 × E4) : E4 × E4 :=
  (O p.1,O (p.2-c+(inner ℝ c p.1) • p.1))

def tree {n : ℕ} (D : FiniteScaleSource n) (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) : NestedCarrierTree n where
  parent := D.tree.parent
  level := D.tree.level
  parent_level := D.tree.parent_level
  carrierCell := fun i => carrierMap O c '' D.tree.carrierCell i
  nested := fun h => Set.image_mono (D.tree.nested h)

/-- The same finite indexed family, with unchanged thickness and weights.
Shadings and carrier cells are literal images; the affine marks transform. -/
def source {n : ℕ} (D : FiniteScaleSource n) (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) : FiniteScaleSource n where
  thickness := D.thickness
  line := fun i => MarkedIsometricChart.line O c (D.line i)
  line_injective := (line_injective O c).comp D.line_injective
  shading := fun i => point O c '' D.shading i
  weight := D.weight
  fibreMark := fun i => D.fibreMark i-inner ℝ c (direction (D.line i))
  tree := tree D O c
  line_in_carrier := fun i => Set.mem_image_of_mem (carrierMap O c) (D.line_in_carrier i)

lemma point_measurePreserving (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) :
    MeasurePreserving (point O c) (volume : Measure E4) volume :=
  O.measurePreserving.comp (measurePreserving_sub_right volume c)

lemma point_measurableEmbedding (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) :
    MeasurableEmbedding (point O c) :=
  (point_isometry O c).isClosedEmbedding.measurableEmbedding

/-- Equality holds for every set, so convex CW tests need no extra
measurability hypothesis. -/
theorem point_volume_preimage (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (U : Set E4) :
    volume ((point O c) ⁻¹' U)=volume U :=
  (point_measurePreserving O c).measure_preimage_emb (point_measurableEmbedding O c) U

theorem point_volume_image (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (S : Set E4) :
    volume (point O c '' S)=volume S := by
  have hh := point_volume_preimage O c (point O c '' S)
  rw [Set.preimage_image_eq S (point_isometry O c).injective] at hh
  exact hh.symm

theorem convex_preimage (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) {U : Set E4} (H : Convex ℝ U) :
    Convex ℝ ((point O c) ⁻¹' U) := by
  have hh := (H.linear_preimage O.toLinearEquiv.toLinearMap).translate_preimage_left (-c)
  simpa only [point,sub_eq_add_neg,Set.preimage_preimage,Function.comp_def] using hh

lemma point_mem_image (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (S : Set E4) (x : E4) :
    point O c x∈point O c '' S ↔ x∈S := by
  constructor
  · rintro ⟨y,hy,hyx⟩
    have he := (point_isometry O c).injective hyx
    simpa only [he] using hy
  · exact Set.mem_image_of_mem _

theorem valid_lines {n : ℕ} (D : FiniteScaleSource n) (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    (H : ∀i,IsValidLine (D.line i)) : ∀i,IsValidLine ((source D O c).line i) :=
  fun i => MarkedIsometricChart.valid_line O c (D.line i) (H i)

theorem shading_measurable {n : ℕ} (D : FiniteScaleSource n) (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    (H : ∀i,MeasurableSet (D.shading i)) : ∀i,MeasurableSet ((source D O c).shading i) :=
  fun i => (point_measurableEmbedding O c).measurableSet_image' (H i)

theorem shading_subset_tube {n : ℕ} (D : FiniteScaleSource n) (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    (H : ∀i,D.shading i⊆markedUnitTube (D.line i) D.thickness) :
    ∀i,(source D O c).shading i⊆markedUnitTube ((source D O c).line i) (source D O c).thickness := by
  intro i
  change point O c '' D.shading i⊆markedUnitTube (MarkedIsometricChart.line O c (D.line i)) D.thickness
  rw [tube_image]
  exact Set.image_mono (H i)

/-- Literal equality of the indexed contained-tube counts. -/
theorem contained_tube_count {n : ℕ} (D : FiniteScaleSource n) (O : E4 ≃ₗᵢ[ℝ] E4)
    (c : E4) (U : Set E4) :
    wzContainedTubeCount (source D O c) U=wzContainedTubeCount D ((point O c) ⁻¹' U) := by
  unfold wzContainedTubeCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _hi
  change (markedUnitTube (MarkedIsometricChart.line O c (D.line i)) D.thickness⊆U) ↔
    markedUnitTube (D.line i) D.thickness⊆(point O c) ⁻¹' U
  rw [tube_image]
  exact Set.image_subset_iff

/-- The SAME physical Convex Wolff constant, including infinite-volume
convex sets. Neither native cubical shading nor carrier AD is asserted. -/
theorem CW_transport {n : ℕ} (D : FiniteScaleSource n) (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    (C : ℝ≥0∞)
    (H : ∀U : Set E4,Convex ℝ U → (wzContainedTubeCount D U:ℝ≥0∞)≤C*volume U*n) :
    ∀U : Set E4,Convex ℝ U → (wzContainedTubeCount (source D O c) U:ℝ≥0∞)≤C*volume U*n := by
  intro U hU
  rw [contained_tube_count]
  have hh := H ((point O c) ⁻¹' U) (convex_preimage O c hU)
  rwa [point_volume_preimage] at hh

theorem shading_volume {n : ℕ} (D : FiniteScaleSource n) (O : E4 ≃ₗᵢ[ℝ] E4)
    (c : E4) (i : Fin n) : volume ((source D O c).shading i)=volume (D.shading i) :=
  point_volume_image O c (D.shading i)

theorem total_shading_volume {n : ℕ} (D : FiniteScaleSource n) (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) :
    wzTotalShadingVolume (source D O c)=wzTotalShadingVolume D := by
  unfold wzTotalShadingVolume
  apply Finset.sum_congr rfl
  intro i _hi
  exact shading_volume D O c i

theorem total_tube_volume {n : ℕ} (D : FiniteScaleSource n) (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) :
    wzTotalTubeVolume (source D O c)=wzTotalTubeVolume D := by
  unfold wzTotalTubeVolume
  apply Finset.sum_congr rfl
  intro i _hi
  change volume (markedUnitTube (MarkedIsometricChart.line O c (D.line i)) D.thickness)=_
  rw [tube_image,point_volume_image]

theorem sourceFunction_pullback {n : ℕ} (D : FiniteScaleSource n) (O : E4 ≃ₗᵢ[ℝ] E4)
    (c x : E4) : sourceFunction (source D O c) (point O c x)=sourceFunction D x := by
  unfold sourceFunction
  apply Finset.sum_congr rfl
  intro i _hi
  change (if point O c x∈point O c '' D.shading i then D.weight i else 0)=
    (if x∈D.shading i then D.weight i else 0)
  rw [point_mem_image]

theorem sourceUnion_image {n : ℕ} (D : FiniteScaleSource n) (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) :
    sourceUnion (source D O c)=point O c '' sourceUnion D := by
  ext y
  obtain ⟨x,rfl⟩ := point_surjective O c y
  rw [point_mem_image]
  change (0 < sourceFunction (source D O c) (point O c x)) ↔ 0 < sourceFunction D x
  rw [sourceFunction_pullback]

theorem sourceUnion_volume {n : ℕ} (D : FiniteScaleSource n) (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) :
    volume (sourceUnion (source D O c))=volume (sourceUnion D) := by
  rw [sourceUnion_image,point_volume_image]

theorem sourceMass_eq {n : ℕ} (D : FiniteScaleSource n) (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) :
    sourceMass (source D O c)=sourceMass D := by
  have hh := (point_measurePreserving O c).lintegral_comp_emb
    (point_measurableEmbedding O c) (sourceFunction (source D O c))
  simpa only [sourceMass,sourceFunction_pullback] using hh.symm

end MarkedIsometricFiniteTransport
