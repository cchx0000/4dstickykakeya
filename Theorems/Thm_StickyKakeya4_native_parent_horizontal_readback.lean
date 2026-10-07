import Theorems.Thm_StickyKakeya4_native_parent_direction_difference
import Theorems.Thm_StickyKakeya4_native_local_parent_physical_map

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeParentHorizontalReadback
open Classical StickyKakeya4 NativeDirectionRankDichotomy NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeLocalParentGeometry NativeHorizontalGrainSlice

/-- Slope normalization cancels the common spatial/time contractions. -/
theorem local_slope_difference {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (p : Parent)
    (i j : Fin n) :
    ActualSlopeSource.heightPoint (localSlope D N p i-localSlope D N p j) 0=
      (N:ℝ) • (slopeVector D i-slopeVector D j) := by
  ext k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · change (0:ℝ)=(N:ℝ)*(1-1)
    ring
  · simp only [slopeVector,ActualSlopeSource.heightPoint_castSucc,PiLp.smul_apply,
      PiLp.sub_apply,smul_eq_mul]
    change ((N:ℝ)*slope (D.line i) k-(p.1 k:ℝ))-
      ((N:ℝ)*slope (D.line j) k-(p.1 k:ℝ))=
      (N:ℝ)*(slope (D.line i) k-slope (D.line j) k)
    ring

/-- On equal-height point differences the genuine parent shear vanishes.
Its remaining horizontal factor is N/512, unlike the slope factor N. -/
theorem physical_map_horizontal_difference {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (p : Parent) (x y : E4) (hxy : x (3:Fin 4)=y (3:Fin 4)) :
    NativeLocalParentPhysicalMap.physicalMap D a N p x-
      NativeLocalParentPhysicalMap.physicalMap D a N p y=(N/512:ℝ) • (x-y) := by
  ext k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · change (1/32:ℝ)*((x (3:Fin 4)-(shift D a:ℝ)*mesh D)/16)-
      (1/32:ℝ)*((y (3:Fin 4)-(shift D a:ℝ)*mesh D)/16)=
      ((N:ℝ)/512)*(x (3:Fin 4)-y (3:Fin 4))
    rw [hxy]
    ring
  · simp only [NativeLocalParentPhysicalMap.physicalMap,NativeLocalParentPhysicalMap.baseMap,
      NativeContractedUnitParent.contractPoint,PiLp.sub_apply,PiLp.smul_apply,
      ActualSlopeSource.heightPoint_castSucc,smul_eq_mul]
    rw [hxy]
    ring

/-- The horizontal grain orientation is unchanged by the actual parent
chart; its error scales by the exact physical factor. -/
theorem physical_map_horizontal_infDist {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (p : Parent) (x y : E4) (hxy : x (3:Fin 4)=y (3:Fin 4))
    (P : Submodule ℝ E4) :
    Metric.infDist (NativeLocalParentPhysicalMap.physicalMap D a N p x-
      NativeLocalParentPhysicalMap.physicalMap D a N p y) (sliceSpace P:Set E4)=
      ((N:ℝ)/512)*Metric.infDist (x-y) (sliceSpace P:Set E4) := by
  rw [physical_map_horizontal_difference D a N p x y hxy,
    NativeParentDirectionDifference.subspace_infDist_smul,abs_of_nonneg (by positivity : (0:ℝ) ≤ N/512)]

end NativeParentHorizontalReadback
