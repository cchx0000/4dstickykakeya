import Theorems.Thm_StickyKakeya4_native_coarse_physical_containment

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeZeroParentPhysicalMap
open StickyKakeya4 NativeOriginalParentSelection NativeUnitParentNormalization
open NativeContractedUnitParent

/-- At common height zero, the second coarse-source physical map is
exactly the fixed homothety 1/512 in all four coordinates. -/
theorem zero_map {n : ℕ} (D : FiniteScaleSource n) (x : E4) :
    physicalMap D 0 (0, 0) x = (1 / 512 : ℝ) • x := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [physicalMap, contractPoint, pointMap, shift, zero_div, Int.floor_zero,
      Int.cast_zero, zero_mul, sub_zero, PiLp.smul_apply, smul_eq_mul,
      ActualSlopeSource.heightPoint_last, show (Fin.last 3 : Fin 4) = 3 by rfl]
    ring
  · simp only [physicalMap, contractPoint, pointMap, shift, zero_div, Int.floor_zero,
      Int.cast_zero, zero_mul, mul_zero, sub_zero, Pi.zero_apply,
      PiLp.smul_apply, smul_eq_mul, ActualSlopeSource.heightPoint_castSucc]
    ring

theorem zero_map_dist {n : ℕ} (D : FiniteScaleSource n) (x y : E4) :
    dist (physicalMap D 0 (0, 0) x) (physicalMap D 0 (0, 0) y) = dist x y / 512 := by
  rw [zero_map, zero_map, dist_smul₀]
  norm_num
  ring

/-- The second zero-parent map has no hidden dependence on which reference
shading was used to construct the local finite source. -/
theorem zero_map_source_independent {n n' : ℕ} (D : FiniteScaleSource n)
    (D' : FiniteScaleSource n') (x : E4) :
    physicalMap D 0 (0, 0) x = physicalMap D' 0 (0, 0) x := by
  rw [zero_map, zero_map]

end NativeZeroParentPhysicalMap
