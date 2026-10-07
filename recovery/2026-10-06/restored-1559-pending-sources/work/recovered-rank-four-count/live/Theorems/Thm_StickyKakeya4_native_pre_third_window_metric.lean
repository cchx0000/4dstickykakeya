import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_field
import Theorems.Thm_StickyKakeya4_native_translated_grain_height_chart

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
noncomputable section
namespace NativePreThirdWindowMetric
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeTranslatedGrainHeightSelection
open NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric NativeTranslatedGrainHeightChart
open NativeReferenceXYGridLinear NativeReferenceXYGridField NativeHeightSlopeCoordinates
open scoped Matrix.Norms.Elementwise

/-- The already proved raw graph metric supplies the exact fixed-field
Lipschitz bound needed by window capacities on the pre-third set. -/
theorem fixed_field_metric {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (Sq Spre : Finset (Fin n × Index))
    (hpre : Spre⊆second D a m ell plane Sq)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (L : ℝ) (hL : 0 ≤ L)
    (Hraw : ∀x∈Spre,∀y∈Spre,‖Fraw (rawHeight D m x.2)-Fraw (rawHeight D m y.2)‖ ≤
      L*|chartHeightCoordinate m 0 (rawHeight D m x.2)-chartHeightCoordinate m 0 (rawHeight D m y.2)|) :
    ∀x∈Spre,∀y∈Spre,
      ‖fixedField D a m ell plane Sq Fraw (translatedHeight D a m x.2)-
        fixedField D a m ell plane Sq Fraw (translatedHeight D a m y.2)‖ ≤
      (3*L)*|referenceHeight m (translatedHeight D a m x.2)-referenceHeight m (translatedHeight D a m y.2)| := by
  have HH := mapped_chart_metric D a m ell plane Sq Spre hpre Fraw L 0 hL Hraw
  intro x hx y hy
  have hxS := mem_image_of_mem (fun z : Fin n × Index => translatedHeight D a m z.2) (hpre hx)
  have hyS := mem_image_of_mem (fun z : Fin n × Index => translatedHeight D a m z.2) (hpre hy)
  rw [fixedField,totalField_on _ _ _ hxS,totalField_on _ _ _ hyS]
  exact HH _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)

end NativePreThirdWindowMetric
