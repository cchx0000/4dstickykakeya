import Theorems.Thm_StickyKakeya4_original_three_dimensional_literal_slab_cover
import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_slab
import Theorems.Thm_StickyKakeya4_original_pair_strip_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalSlabProjection
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover

abbrev Point2 := ℝ × ℝ

def project (b : Frame3) (x : Point3) : Point2 :=
  (frameCoordinate b 0 x, frameCoordinate b 1 x)

def euclidean2 (x : Point2) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![x.1,x.2]

def distance2 (x y : Point2) : ℝ := dist (euclidean2 x) (euclidean2 y)

def orthogonalFoot (b : Frame3) (c : ℝ) (x : Point3) : Point3 :=
  fun j => x j-(frameCoordinate b 2 x-c)*b 2 j

lemma frameCoordinate_eq_repr (b : Frame3) (x : Point3) (j : Fin 3) :
    frameCoordinate b j x=b.repr (WithLp.toLp 2 x) j := by
  rw [b.repr_apply_apply]
  simp [frameCoordinate,PiLp.inner_apply,mul_comm]

lemma distance3_eq_euclidean (x y : Point3) :
    distance3 x y=dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3)) (WithLp.toLp 2 y) := by
  rw [EuclideanSpace.dist_eq]
  simp only [distance3,Real.dist_eq,Fin.sum_univ_three,sq_abs]

lemma distance2_squared (x y : Point2) :
    distance2 x y^2=(x.1-y.1)^2+(x.2-y.2)^2 := by
  rw [distance2,EuclideanSpace.dist_sq_eq]
  simp [euclidean2,Fin.sum_univ_two,Real.dist_eq]

lemma frame_distance_squared (b : Frame3) (x y : Point3) :
    distance3 x y^2=distance2 (project b x) (project b y)^2+
      (frameCoordinate b 2 x-frameCoordinate b 2 y)^2 := by
  rw [distance3_eq_euclidean,← b.repr.dist_map (WithLp.toLp 2 x) (WithLp.toLp 2 y),
    EuclideanSpace.dist_sq_eq]
  simp only [Real.dist_eq,sq_abs,Fin.sum_univ_three,← frameCoordinate_eq_repr]
  rw [distance2_squared]
  rfl

lemma projected_distance_le (b : Frame3) (x y : Point3) :
    distance2 (project b x) (project b y) ≤ distance3 x y := by
  have h := frame_distance_squared b x y
  have hx : 0 ≤ distance3 x y := Real.sqrt_nonneg _
  have hy : 0 ≤ distance2 (project b x) (project b y) := dist_nonneg
  nlinarith only [h,hx,hy,sq_nonneg (frameCoordinate b 2 x-frameCoordinate b 2 y)]

lemma slab_normal_difference (b : Frame3) (c Delta : ℝ) (x y : Point3)
    (hx : |frameCoordinate b 2 x-c| ≤ Delta)
    (hy : |frameCoordinate b 2 y-c| ≤ Delta) :
    |frameCoordinate b 2 x-frameCoordinate b 2 y| ≤ 2*Delta := by
  have h := abs_sub_le (frameCoordinate b 2 x) c (frameCoordinate b 2 y)
  rw [abs_sub_comm c] at h
  linarith

/-- Exact original points in the slab lose at most twice its half-width
when their tangential images are used to measure distance. -/
theorem original_slab_distance_comparison (b : Frame3) (c Delta : ℝ)
    (x y : Point3) (hx : |frameCoordinate b 2 x-c| ≤ Delta)
    (hy : |frameCoordinate b 2 y-c| ≤ Delta) :
    distance3 x y ≤ distance2 (project b x) (project b y)+2*Delta := by
  have hDelta : 0 ≤ Delta := (abs_nonneg _).trans hx
  have h := frame_distance_squared b x y
  have hnormal := pow_le_pow_left₀ (abs_nonneg _) (slab_normal_difference b c Delta x y hx hy) 2
  rw [sq_abs] at hnormal
  have hd : 0 ≤ distance2 (project b x) (project b y) := dist_nonneg
  have hp : 0 ≤ distance3 x y := Real.sqrt_nonneg _
  nlinarith only [h,hnormal,hd,hp,hDelta,mul_nonneg hd hDelta]

theorem original_projected_coordinate_bounds (b : Frame3) (x : Point3)
    (hx : ∀ j,|x j| ≤ 1) : |(project b x).1| ≤ 3 ∧ |(project b x).2| ≤ 3 := by
  exact ⟨original_frame_coordinate_bound b x hx 0,original_frame_coordinate_bound b x hx 1⟩

lemma frameCoordinate_orthogonalFoot (b : Frame3) (c : ℝ) (x : Point3) (j : Fin 3) :
    frameCoordinate b j (orthogonalFoot b c x)=
      frameCoordinate b j x-(frameCoordinate b 2 x-c)*(if j=2 then 1 else 0) := by
  have hv : (WithLp.toLp 2 (orthogonalFoot b c x) : EuclideanSpace ℝ (Fin 3))=
      WithLp.toLp 2 x-(frameCoordinate b 2 x-c) • b 2 := by
    ext k
    simp [orthogonalFoot]
  rw [frameCoordinate_eq_repr,hv,map_sub,map_smul,b.repr_self]
  simp [← frameCoordinate_eq_repr]

lemma orthogonalFoot_on_plane (b : Frame3) (c : ℝ) (x : Point3) :
    frameCoordinate b 2 (orthogonalFoot b c x)=c := by
  rw [frameCoordinate_orthogonalFoot]
  simp

lemma project_orthogonalFoot (b : Frame3) (c : ℝ) (x : Point3) :
    project b (orthogonalFoot b c x)=project b x := by
  ext <;> simp [project,frameCoordinate_orthogonalFoot]

lemma distance_to_orthogonalFoot (b : Frame3) (c : ℝ) (x : Point3) :
    distance3 x (orthogonalFoot b c x)=|frameCoordinate b 2 x-c| := by
  have h := frame_distance_squared b x (orthogonalFoot b c x)
  rw [project_orthogonalFoot,orthogonalFoot_on_plane] at h
  simp only [distance2,dist_self] at h
  have hd : 0 ≤ distance3 x (orthogonalFoot b c x) := Real.sqrt_nonneg _
  nlinarith only [h,hd,abs_nonneg (frameCoordinate b 2 x-c),sq_abs (frameCoordinate b 2 x-c)]

end OriginalThreeDimensionalSlabProjection
