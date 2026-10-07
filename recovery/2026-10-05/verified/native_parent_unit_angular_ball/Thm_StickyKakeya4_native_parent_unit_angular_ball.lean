import Theorems.Thm_StickyKakeya4_native_paid_mesh_angular_upper

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000

noncomputable section
namespace NativeParentUnitAngularBall
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentGeometry
open scoped BigOperators

def center : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun _ => (1/2:ℝ))

/-- Every actual normalized slope in one original phase parent lies in
the same unit Euclidean ball. This follows from the literal half-open slope
box; it does not use an angular menu bound or a new direction selection. -/
lemma localSlope_in_unit_ball {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p) :
    dist (localSlope D N p i) center≤ 1 := by
  have hc (j : Fin 3) : ((localSlope D N p i-center) j)^2≤ (1/4:ℝ) := by
    have hb := (parameter_box D a N p i hp).1 j
    have hp := mul_nonneg hb.1 (sub_nonneg.mpr hb.2.le)
    change (localSlope D N p i j-1/2)^2≤ (1/4:ℝ)
    nlinarith only [hp]
  have hnorm : ‖localSlope D N p i-center‖^2≤ (3/4:ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑_j : Fin 3,(1/4:ℝ) := sum_le_sum (fun j _ => hc j)
      _ = _ := by norm_num
  rw [dist_eq_norm]
  nlinarith only [hnorm,norm_nonneg (localSlope D N p i-center)]

end NativeParentUnitAngularBall
