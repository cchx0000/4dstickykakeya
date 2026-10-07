import Theorems.Thm_StickyKakeya4_native_normalized_offset_time

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000

noncomputable section
namespace NativeNormalizedOffsetField
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeNormalizedCellRelativeMenu NativeHeightMetricMenu NativeTranslatedGrainHeightOverlap
open NativeTranslatedGrainHeightMetric NativeNormalizedOffsetTime

/-- Read the proved raw-height field modulus on actual incidences inside
one literal normalized physical cell. -/
theorem raw_field_variation {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    (D : FiniteScaleSource n) (a : ℝ) (N M m : ℕ) (hM : 0 < M) (p : Parent)
    (I : Finset (Fin n × Index)) (cell : Index)
    (hcell : ∀z∈I,physicalCell D a N M p z.2=cell)
    (F : ℤ → V) (metric shift : ℝ) (hmetric : 0 ≤ metric)
    (Hmetric : ∀z∈I,∀w∈I,‖F (rawHeight D m z.2)-F (rawHeight D m w.2)‖ ≤
      metric*|chartHeightCoordinate m shift (rawHeight D m z.2)-
        chartHeightCoordinate m shift (rawHeight D m w.2)|) :
    ∀k∈I.image Prod.snd,∀l∈I.image Prod.snd,
      ‖F (rawHeight D m k)-F (rawHeight D m l)‖ ≤ metric*(64/(M:ℝ)+meshWidth m/512) := by
  intro k hk l hl
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hl
  exact (Hmetric z hz w hw).trans (mul_le_mul_of_nonneg_left
    (chart_height_window D a N M m hM p z.2 w.2 shift ((hcell z hz).trans (hcell w hw).symm)) hmetric)

/-- The translated field can instead use its actual reference-height
modulus, with exactly the same rounding term. -/
theorem translated_field_variation {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    (D : FiniteScaleSource n) (a : ℝ) (N M m : ℕ) (hM : 0 < M) (p : Parent)
    (I : Finset (Fin n × Index)) (cell : Index)
    (hcell : ∀z∈I,physicalCell D a N M p z.2=cell)
    (F : ℤ → V) (metric : ℝ) (hmetric : 0 ≤ metric)
    (Hmetric : ∀z∈I,∀w∈I,‖F (translatedHeight D a m z.2)-F (translatedHeight D a m w.2)‖ ≤
      metric*|referenceHeight m (translatedHeight D a m z.2)-referenceHeight m (translatedHeight D a m w.2)|) :
    ∀k∈I.image Prod.snd,∀l∈I.image Prod.snd,
      ‖F (translatedHeight D a m k)-F (translatedHeight D a m l)‖ ≤
        metric*(64/(M:ℝ)+meshWidth m/512) := by
  intro k hk l hl
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hl
  exact (Hmetric z hz w hw).trans (mul_le_mul_of_nonneg_left
    (translated_height_window D a N M m hM p z.2 w.2 ((hcell z hz).trans (hcell w hw).symm)) hmetric)

/-- The actual mapped field retains the raw metric constant on every
later incidence subset, by its literal stage-two readback. -/
theorem mapped_raw_field_variation {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    (D : FiniteScaleSource n) (a : ℝ) (N M m ell : ℕ) (hM : 0 < M) (p : Parent)
    (plane : Index → Submodule ℝ E4) (S I : Finset (Fin n × Index))
    (hI : I⊆NativeTranslatedGrainHeightSelection.second D a m ell plane S)
    (cell : Index) (hcell : ∀z∈I,physicalCell D a N M p z.2=cell)
    (F : ℤ → V) (metric shift : ℝ) (hmetric : 0 ≤ metric)
    (Hmetric : ∀z∈I,∀w∈I,‖F (rawHeight D m z.2)-F (rawHeight D m w.2)‖ ≤
      metric*|chartHeightCoordinate m shift (rawHeight D m z.2)-
        chartHeightCoordinate m shift (rawHeight D m w.2)|) :
    ∀k∈I.image Prod.snd,∀l∈I.image Prod.snd,
      ‖mapped D a m ell plane S F (translatedHeight D a m k)-
        mapped D a m ell plane S F (translatedHeight D a m l)‖ ≤
      metric*(64/(M:ℝ)+meshWidth m/512) := by
  have H := raw_field_variation D a N M m hM p I cell hcell F metric shift hmetric Hmetric
  intro k hk l hl
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hl
  rw [mapped_readback D a m ell plane S F z (hI hz),mapped_readback D a m ell plane S F w (hI hw)]
  exact H z.2 (mem_image_of_mem _ hz) w.2 (mem_image_of_mem _ hw)

lemma window_variation_le_twice {metric rho parentWidth : ℝ}
    (hmetric : 0 ≤ metric) (hwindow : parentWidth/512 ≤ rho) :
    metric*(rho+parentWidth/512) ≤ 2*metric*rho := by nlinarith only [hmetric,hwindow]

end NativeNormalizedOffsetField
