import Theorems.Thm_StickyKakeya4_original_projected_owner_profile
import Theorems.Thm_StickyKakeya4_original_three_dimensional_projected_query_lift
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalNormalizedOwnerQuery
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalThreeDimensionalProjectionCells OriginalPlanarTubeParameters
open OriginalThreeDimensionalPlanarTubeProjection OriginalThreeDimensionalProjectedQueryLift
open OriginalProjectedOwnerProfile

def normalizedPair (b : Frame3) (p q : Point3) : Pair2 :=
  (normalizedProject b p,normalizedProject b q)

def normalizedChart (b : Frame3) (swap : Bool) (p : Point3) : Point2 :=
  chart swap (normalizedProject b p)

def normalizedChartPair (b : Frame3) (swap : Bool) (p q : Point3) : Pair2 :=
  (normalizedChart b swap p,normalizedChart b swap q)

lemma original_normalized_linePoint (b : Frame3) (p q : Point3) (t : ℝ) :
    normalizedProject b (linePoint3 p q t)=
      OriginalPairStripGeometry.linePoint (normalizedPair b p q) t := by
  unfold normalizedProject
  rw [project_linePoint]
  ext <;> dsimp [normalizedPair,normalizedProject,OriginalPairStripGeometry.linePoint] <;> ring

lemma original_normalized_chart_linePoint (b : Frame3) (swap : Bool)
    (p q : Point3) (t : ℝ) :
    normalizedChart b swap (linePoint3 p q t)=
      OriginalPairStripGeometry.linePoint (normalizedChartPair b swap p q) t := by
  unfold normalizedChart
  rw [original_normalized_linePoint,chart_linePoint]
  rfl

lemma original_normalized_chart_distance (b : Frame3) (swap : Bool) (p q : Point3) :
    distance2 (normalizedChart b swap p) (normalizedChart b swap q)=
      distance2 (chartProject b swap p) (chartProject b swap q)/4 := by
  rw [normalizedChart,normalizedChart,chart_distance2,chart_distance2]
  exact original_normalized_project_distance b p q

/-- Swapping the actual two tangential coordinates preserves the exact
Euclidean pair-tube witness, including its affine parameter. -/
lemma original_chart_euclidean_pair_tube_iff (swap : Bool) (z : Pair2)
    (R : ℝ) (x : Point2) :
    EuclideanPairTube (chart swap z.1,chart swap z.2) R (chart swap x) ↔
      EuclideanPairTube z R x := by
  unfold EuclideanPairTube
  constructor
  · rintro ⟨t,ht⟩
    rw [← chart_linePoint,chart_distance2] at ht
    exact ⟨t,ht⟩
  · rintro ⟨t,ht⟩
    refine ⟨t,?_⟩
    rwa [← chart_linePoint,chart_distance2]

/-- The normalized and unnormalized tubes use the SAME affine parameter.
The exact dilation factor is four, with either actual coordinate chart. -/
theorem original_normalized_chart_query_iff (b : Frame3) (swap : Bool)
    (p q x : Point3) (R : ℝ) :
    EuclideanPairTube (normalizedChartPair b swap p q) R (normalizedChart b swap x) ↔
      EuclideanPairTube (projectedPair b swap p q) (4*R) (chartProject b swap x) := by
  have he (t : ℝ) :
      distance2 (normalizedChart b swap x)
          (OriginalPairStripGeometry.linePoint (normalizedChartPair b swap p q) t)=
        distance2 (chartProject b swap x)
          (OriginalPairStripGeometry.linePoint (projectedPair b swap p q) t)/4 := by
    rw [← original_normalized_chart_linePoint,← chart_project_linePoint,
      original_normalized_chart_distance]
  constructor
  · rintro ⟨t,ht⟩
    rw [he] at ht
    exact ⟨t,by linarith only [ht]⟩
  · rintro ⟨t,ht⟩
    refine ⟨t,?_⟩
    rw [he]
    linarith only [ht]

/-- The fixed normalized owner image needs no chart-dependent replacement:
its query tube is exactly the original projected query in ANY swapped chart. -/
theorem original_normalized_query_iff (b : Frame3) (swap : Bool)
    (p q x : Point3) (R : ℝ) :
    EuclideanPairTube (normalizedPair b p q) R (normalizedProject b x) ↔
      EuclideanPairTube (projectedPair b swap p q) (4*R) (chartProject b swap x) := by
  have hchart := original_chart_euclidean_pair_tube_iff swap (normalizedPair b p q) R
    (normalizedProject b x)
  change EuclideanPairTube (normalizedChartPair b swap p q) R (normalizedChart b swap x) ↔
    EuclideanPairTube (normalizedPair b p q) R (normalizedProject b x) at hchart
  exact hchart.symm.trans (original_normalized_chart_query_iff b swap p q x R)

/-- Literal tube selection commutes with the actual normalized image, while
retaining every original center label and the same original pair endpoints. -/
theorem original_normalized_query_subset_readback (b : Frame3) (swap : Bool)
    (C : Finset Point3) (p q : Point3) (R : ℝ) :
    (normalizedImage b C).filter (EuclideanPairTube (normalizedPair b p q) R)=
      (C.filter (fun x => EuclideanPairTube (projectedPair b swap p q) (4*R)
        (chartProject b swap x))).image (normalizedProject b) := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzI,hzt⟩ := Finset.mem_filter.mp hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hzI
    exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr
      ⟨hx,(original_normalized_query_iff b swap p q x R).mp hzt⟩,rfl⟩
  · intro hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hxC,hxt⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hxC,
      (original_normalized_query_iff b swap p q x R).mpr hxt⟩

/-- Injectivity of the SAME original owner net makes the tube-selected count
exact. No global tube-cap or restricted-fiber population hypothesis is used. -/
theorem original_normalized_query_card_readback (b : Frame3) (swap : Bool)
    (C : Finset Point3) (c rho Delta : ℝ) (hDelta : 0 < Delta)
    (hsmall : 48*rho ≤ Delta)
    (hraw : ∀ x∈C,|frameCoordinate b 2 x-c| ≤ 3*rho)
    (hsep : ∀ x∈C,∀ y∈C,x≠y → Delta/4 ≤ distance3 x y)
    (p q : Point3) (R : ℝ) :
    ((normalizedImage b C).filter (EuclideanPairTube (normalizedPair b p q) R)).card=
      (C.filter (fun x => EuclideanPairTube (projectedPair b swap p q) (4*R)
        (chartProject b swap x))).card := by
  rw [original_normalized_query_subset_readback b swap C p q R]
  apply Finset.card_image_of_injOn
  intro x hx y hy he
  exact original_normalized_owner_injective b c rho Delta C hDelta hsmall hraw hsep
    (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 he

end OriginalNormalizedOwnerQuery
