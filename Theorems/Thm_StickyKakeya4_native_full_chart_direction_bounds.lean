import Theorems.Thm_StickyKakeya4_native_full_coarse_shadow
import Theorems.Thm_StickyKakeya4_marked_isometric_chart

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeFullChartDirectionBounds
open Classical StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCoarseCellSource NativeCoarseDirectionThinning NativeFullCoarseShadow
open NativeCoarseRepresentativeGeometry NativeOriginalCellChartGeometry

/-- The actual charted full-source slopes have coordinate bound2 from
unit direction and vertical component≥1/2. No preservation of the old
coordinate cube by an orthogonal map is asserted. -/
theorem full_source_slope_bound {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level b : ℕ) (E : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀ x : E4, O x (3:Fin 4)=x (3:Fin 4)) (c : E4)
    (i : Fin (R.image (parentLabel D a (2^b))).card) (j : Fin 3) :
    |slope (MarkedIsometricChart.line O c ((fullSource h R a level b E).line i)) j| ≤ 2 := by
  let t := representative h R a (2^b) (parentIndex (R.image (parentLabel D a (2^b))) i)
  have ht := zero_parent_valid_slab h a t
  have hv := MarkedIsometricChart.valid_line O c _ ht.1
  apply slope_bound _ hv
  change (1/2:ℝ) ≤ O (direction (NativeContractedUnitParent.line D a (0,0) t)) (3:Fin 4)
  rw [hO]
  exact ht.2.1

end NativeFullChartDirectionBounds
