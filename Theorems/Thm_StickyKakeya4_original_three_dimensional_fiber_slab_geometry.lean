import Theorems.Thm_StickyKakeya4_original_three_dimensional_slab_projection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
noncomputable section
namespace OriginalThreeDimensionalFiberSlabGeometry
open OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection

lemma original_frame_coordinate_lipschitz (b : Frame3) (x y : Point3) (j : Fin 3) :
    |frameCoordinate b j x-frameCoordinate b j y| ≤ distance3 x y := by
  let X : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 x
  let Y : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 y
  calc
    _ = ‖(b.repr X-b.repr Y) j‖ := by simp [frameCoordinate_eq_repr,X,Y]
    _ ≤ ‖b.repr X-b.repr Y‖ := PiLp.norm_apply_le _ _
    _ = dist (b.repr X) (b.repr Y) := (dist_eq_norm _ _).symm
    _ = dist X Y := b.repr.dist_map X Y
    _ = _ := (distance3_eq_euclidean x y).symm

/-- A whole original owner fiber stays inside the expanded slab, because
its actual center is in the raw slab and the fiber has a true metric radius. -/
theorem original_full_fiber_in_expanded_slab (b : Frame3) (c rho R Delta : ℝ)
    (x p : Point3) (hp : |frameCoordinate b 2 p-c| ≤ 3*rho)
    (hx : distance3 x p ≤ R) (hsize : R+3*rho ≤ Delta) :
    |frameCoordinate b 2 x-c| ≤ Delta := by
  have ht := abs_sub_le (frameCoordinate b 2 x) (frameCoordinate b 2 p) c
  have hn := original_frame_coordinate_lipschitz b x p 2
  linarith only [ht,hn,hp,hx,hsize]

/-- An actual Delta/4 net of RAW-slab endpoints remains genuinely
Delta/8-separated after exact orthogonal projection. -/
theorem original_raw_net_projected_separation (b : Frame3) (c rho Delta : ℝ)
    (p q : Point3) (hp : |frameCoordinate b 2 p-c| ≤ 3*rho)
    (hq : |frameCoordinate b 2 q-c| ≤ 3*rho)
    (hsep : Delta/4 ≤ distance3 p q) (hsmall : 48*rho ≤ Delta) :
    Delta/8 ≤ distance2 (project b p) (project b q) := by
  have hd := original_slab_distance_comparison b c (3*rho) p q hp hq
  linarith only [hd,hsep,hsmall]

end OriginalThreeDimensionalFiberSlabGeometry
