import Theorems.Thm_StickyKakeya4_original_three_dimensional_owner_tube_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
namespace OriginalThreeDimensionalOwnerQueryTube
open OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalSlabProjection OriginalTubeGraphPairGeometry
open OriginalThreeDimensionalOwnerTubeGeometry

lemma original_query_tube_movement (p q x y : Point3) (rho h : ℝ)
    (hxy : distance3 x y ≤ h) (htube : x∈physicalTube3 p q rho) :
    y∈physicalTube3 p q (rho+h) := by
  obtain ⟨t,ht⟩ := htube
  have hyx : distance3 y x ≤ h := by
    simpa only [distance3_eq_euclidean,dist_comm] using hxy
  have hh := original_distance_triangle y x (linePoint3 p q t)
  exact ⟨t,by linarith only [hh,hyx,ht]⟩

/-- Moving the pair endpoints AND the actual rich point to their original
owners preserves a physical tube, with the necessary inverse-gap cost. -/
theorem original_three_owner_tube (p q x u v y : Point3) (Delta r : ℝ)
    (hDelta : 0 < Delta) (hsmall : 32*Delta ≤ 1) (hr : 0 < r)
    (hp : ∀ j,|p j| ≤ 1) (hq : ∀ j,|q j| ≤ 1) (hx : ∀ j,|x j| ≤ 1)
    (hsep : r ≤ distance3 p q)
    (hu : distance3 p u ≤ Delta/4) (hv : distance3 q v ≤ Delta/4)
    (hy : distance3 x y ≤ Delta/4)
    (htube : x∈physicalTube3 p q (32*Delta)) :
    y∈physicalTube3 u v (200*Delta/r) := by
  have hxt := original_delta_owner_tube p q u v x Delta r hDelta hsmall hr hp hq hx
    hsep hu hv htube
  obtain ⟨t,ht⟩ := original_query_tube_movement u v x y (160*Delta/r) (Delta/4) hy hxt
  have hr4 := hsep.trans (original_box_distance_le_four p q hp hq)
  refine ⟨t,ht.trans ?_⟩
  apply (le_div_iff₀ hr).mpr
  have he : (160*Delta/r+Delta/4)*r=160*Delta+Delta*r/4 := by field_simp
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hr4 hDelta.le
  nlinarith only [hm,hDelta]

/-- Original separated graph endpoints cannot collapse onto one owner
when the owner radius is below their separation. -/
theorem original_owner_pair_separation (p q u v : Point3) (Delta r : ℝ)
    (hsep : r ≤ distance3 p q) (hsmall : Delta ≤ r)
    (hu : distance3 p u ≤ Delta/4) (hv : distance3 q v ≤ Delta/4) :
    r/2 ≤ distance3 u v := by
  have hvq : distance3 v q ≤ Delta/4 := by
    simpa only [distance3_eq_euclidean,dist_comm] using hv
  have h1 := original_distance_triangle p u q
  have h2 := original_distance_triangle u v q
  linarith only [hsep,hsmall,hu,hvq,h1,h2]

end OriginalThreeDimensionalOwnerQueryTube
