import Theorems.Thm_StickyKakeya4_native_translated_grain_height_metric
import Theorems.Thm_StickyKakeya4_native_height_metric_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeTranslatedGrainHeightChart
open Classical Finset StickyKakeya4 NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightSelection
open NativeTranslatedGrainHeightMetric NativeHeightMetricMenu NativeCommonCubicalMesh

/-- Exact OLD chart metric on integer raw labels; the common translation
cancels but no raw label is identified with a reference label. -/
lemma raw_chart_distance (m : ℕ) (shift : ℝ) (u v : ℤ) :
    |chartHeightCoordinate m shift u-chartHeightCoordinate m shift v|=
      ((64/((2^m:ℕ):ℝ))/512)*|(u:ℝ)-v| := by
  unfold chartHeightCoordinate rawHeightCoordinate meshWidth
  rw [←sub_div,sub_sub_sub_cancel_right,←mul_sub,abs_div,abs_mul,
    abs_of_pos (by positivity : (0:ℝ)<64/((2^m:ℕ):ℝ))]
  norm_num
  ring

/-- Direct bridge from the previously normalized raw-height chart metric
to ACTUAL translated reference centers. The only NEW Lipschitz cost is3. -/
theorem mapped_chart_metric {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (S H3 : Finset (Fin n × Index))
    (h3 : H3⊆second D a m ell plane S) (F : ℤ → V) (L shift : ℝ) (hL : 0 ≤ L)
    (Hraw : ∀x∈H3,∀y∈H3,‖F (rawHeight D m x.2)-F (rawHeight D m y.2)‖ ≤
      L*|chartHeightCoordinate m shift (rawHeight D m x.2)-chartHeightCoordinate m shift (rawHeight D m y.2)|) :
    ∀t∈H3.image (fun z => translatedHeight D a m z.2),
      ∀u∈H3.image (fun z => translatedHeight D a m z.2),
        ‖mapped D a m ell plane S F t-mapped D a m ell plane S F u‖ ≤
          (3*L)*|referenceHeight m t-referenceHeight m u| := by
  intro t ht u hu
  obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hu
  by_cases he : translatedHeight D a m x.2=translatedHeight D a m y.2
  · rw [he,sub_self,norm_zero,sub_self,abs_zero,mul_zero]
  · rw [mapped_readback D a m ell plane S F x (h3 hx),mapped_readback D a m ell plane S F y (h3 hy)]
    have hgap := actual_height_metric D a m x.2 y.2 he
    have hscaled := mul_le_mul_of_nonneg_left hgap
      (by positivity : (0:ℝ) ≤ L*((64/((2^m:ℕ):ℝ))/512))
    have hraw := Hraw x hx y hy
    rw [raw_chart_distance] at hraw
    rw [referenceHeight_distance]
    nlinarith only [hraw,hscaled]

end NativeTranslatedGrainHeightChart
