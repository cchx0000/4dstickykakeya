import Theorems.Thm_StickyKakeya4_original_normalized_owner_query
import Theorems.Thm_StickyKakeya4_original_physical_pair_tube

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
namespace OriginalNormalizedOwnerPhysicalBridge
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalThreeDimensionalProjectedQueryLift OriginalProjectedOwnerProfile
open OriginalNormalizedOwnerQuery PlanarFrostmanBallConversion

/-- The projected Euclidean metric is literally the distance used by the
frozen original planar A1 interface. -/
lemma original_distance2_eq_a1_euclidean (x y : Point2) :
    distance2 x y=euclideanDistance x y := by
  have h1 := distance2_squared x y
  have h2 : (euclideanDistance x y)^2=(y.1-x.1)^2+(y.2-x.2)^2 :=
    Real.sq_sqrt (by positivity)
  have hd : 0 ≤ distance2 x y := dist_nonneg
  have he : 0 ≤ euclideanDistance x y := Real.sqrt_nonneg _
  nlinarith only [h1,h2,hd,he]

lemma original_distance2_eq_a1_euclidean_reverse (x y : Point2) :
    distance2 x y=euclideanDistance y x := by
  rw [← original_distance2_eq_a1_euclidean]
  exact dist_comm _ _

/-- The two physical planar tube definitions agree exactly, including
orientation of the distance and all boundary points. -/
theorem original_a1_physical_pair_tube_iff (S : Finset Point2)
    (z : Point2 × Point2) (R : ℝ) (x : Point2) :
    x∈OriginalPhysicalPairTube.physicalPairTube S R z ↔
      x∈S ∧ EuclideanPairTube z R x := by
  rw [OriginalPhysicalPairTube.physicalPairTube,Finset.mem_filter]
  simp only [EuclideanPairTube,original_distance2_eq_a1_euclidean_reverse]

/-- A genuine original physical-tube witness projects and contracts by
exactly four, with the same actual endpoints and affine parameter. -/
theorem original_physical_tube_normalizes (b : Frame3) (p q x : Point3) (W : ℝ)
    (hx : x∈physicalTube3 p q W) :
    EuclideanPairTube (normalizedPair b p q) (W/4) (normalizedProject b x) := by
  obtain ⟨t,ht⟩ := hx
  refine ⟨t,?_⟩
  rw [← original_normalized_linePoint,original_normalized_project_distance]
  have hh := (projected_distance_le b x (linePoint3 p q t)).trans ht
  linarith only [hh]

/-- Original rich centers enter the frozen A1 physical pair tube on the
literal normalized center image. -/
theorem original_physical_tube_normalized_membership (b : Frame3) (C : Finset Point3)
    (p q x : Point3) (W : ℝ) (hxC : x∈C) (hx : x∈physicalTube3 p q W) :
    normalizedProject b x∈OriginalPhysicalPairTube.physicalPairTube
      (normalizedImage b C) (W/4) (normalizedPair b p q) := by
  apply (original_a1_physical_pair_tube_iff _ _ _ _).mpr
  exact ⟨Finset.mem_image_of_mem _ hxC,original_physical_tube_normalizes b p q x W hx⟩

end OriginalNormalizedOwnerPhysicalBridge
