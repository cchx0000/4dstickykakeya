import Theorems.Thm_StickyKakeya4_native_common_direction_phase_menu
import Theorems.Thm_StickyKakeya4_native_normalized_cell_angular_menu
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeAngularBallCellCover
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentGeometry NativeReferenceXYGridAngularCap NativeReferenceXYGridMenus
open NativeNormalizedCellAngularMenu NativeTangentGridCoarsening

/-- A genuine Euclidean sigma angular ball meets at most27 standard
sigma angular cells. The center is arbitrary and need not be occupied. -/
theorem angular_ball_cell_card {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (p : Parent)
    (E : Finset (Fin n × Index)) (center : EuclideanSpace ℝ (Fin 3))
    (sigma : ℝ) (hsigma : 0< sigma)
    (H : ∀z∈E,dist (localSlope D N p z.1) center≤ sigma) :
    (E.image (fun z => localAngle D N p sigma z.1)).card≤ 27 := by
  let q : Fin 3 → ℤ := fun j => ⌊center j/sigma⌋
  have hsub : E.image (fun z => localAngle D N p sigma z.1)⊆ vectorBox q 1 := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
    apply Fintype.mem_piFinset.mpr
    intro j
    have hc : |localSlope D N p z.1 j-center j|≤dist (localSlope D N p z.1) center := by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le (localSlope D N p z.1) center j
    have hcoord := hc.trans (H z hz)
    have hcoord' : |NativeIncidentAffineAnchorGeometry.localHorizontalSlope D N p z.1 j.castSucc-center j|≤ sigma := by
      simpa only [NativeIncidentAffineAnchorGeometry.localHorizontalSlope,ActualSlopeSource.heightPoint_castSucc] using hcoord
    exact NativeCoarseScaleInterpolation.floor_close hsigma _ _ hcoord'
  exact (card_le_card hsub).trans_eq (by rw [vectorBox_card]; norm_num)

/-- Count fine angular labels in an actual ball by the verified upper for
each standard sigma cell. All incidence labels and original weights stay
on the same E; the union is counted without choosing new representatives. -/
theorem angular_ball_count {n : ℕ} (D : FiniteScaleSource n) (N M : ℕ) (p : Parent)
    (E : Finset (Fin n × Index)) (center : EuclideanSpace ℝ (Fin 3))
    (sigma : ℝ) (hsigma : 0< sigma)
    (Hball : ∀z∈E,dist (localSlope D N p z.1) center≤ sigma)
    (B : ℝ) (hB : 0≤ B)
    (H : ∀v∈E.image (fun z => localAngle D N p sigma z.1),
      (((E.filter (fun z => localAngle D N p sigma z.1=v)).image
        (fun z => angularCell D N M p z.1)).card:ℝ)≤ B) :
    ((E.image (fun z => angularCell D N M p z.1)).card:ℝ)≤ 27*B := by
  have hcount := image_card_le_real_mul_of_fiber_images E (fun z => angularCell D N M p z.1)
    (fun z => localAngle D N p sigma z.1) B H
  have hcells : ((E.image (fun z => localAngle D N p sigma z.1)).card:ℝ)≤ 27 := by
    exact_mod_cast angular_ball_cell_card D N p E center sigma hsigma Hball
  exact hcount.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcells hB)

end NativeAngularBallCellCover
