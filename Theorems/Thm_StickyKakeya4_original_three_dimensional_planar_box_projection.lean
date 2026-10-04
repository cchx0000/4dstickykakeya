import Theorems.Thm_StickyKakeya4_original_three_dimensional_weighted_planar_projection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalPlanarBoxProjection
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalThreeDimensionalProjectionCells OriginalFiniteCellWeights PlanarStripIntersection

lemma boxDistance_le_distance2 (x y : Point2) : boxDistance x y ≤ distance2 x y := by
  have h := abs_coordinate_le_distance2 x y
  simpa only [boxDistance,abs_sub_comm] using max_le h.1 h.2

lemma distance2_le_two_boxDistance (x y : Point2) : distance2 x y ≤ 2*boxDistance x y := by
  have h := distance2_le_abs_add x y
  have h1 : |x.1-y.1| ≤ boxDistance x y := by
    simpa only [boxDistance,abs_sub_comm] using le_max_left |y.1-x.1| |y.2-x.2|
  have h2 : |x.2-y.2| ≤ boxDistance x y := by
    simpa only [boxDistance,abs_sub_comm] using le_max_right |y.1-x.1| |y.2-x.2|
  linarith

theorem original_slab_box_distance_comparison (b : Frame3) (c Delta : ℝ)
    (x y : Point3) (hx : |frameCoordinate b 2 x-c| ≤ Delta)
    (hy : |frameCoordinate b 2 y-c| ≤ Delta) :
    distance3 x y ≤ 2*boxDistance (project b x) (project b y)+2*Delta := by
  have h := original_slab_distance_comparison b c Delta x y hx hy
  have hp := distance2_le_two_boxDistance (project b x) (project b y)
  linarith

/-- Pair separation concerns the actual projected original endpoints. -/
theorem original_projected_pair_separation (b : Frame3) (c Delta r : ℝ)
    (x y : Point3) (hx : |frameCoordinate b 2 x-c| ≤ Delta)
    (hy : |frameCoordinate b 2 y-c| ≤ Delta)
    (hDelta : 4*Delta ≤ r) (hsep : r ≤ distance3 x y) :
    r/4 ≤ boxDistance (project b x) (project b y) := by
  have h := original_slab_box_distance_comparison b c Delta x y hx hy
  linarith

def boxBallCells (P : Finset Point3) (b : Frame3) (Delta : ℝ) (a : Point2) (r : ℝ) : Finset Cell :=
  (occupied P (cellCode b Delta)).filter (fun k => boxDistance (cellAnchor Delta k) a ≤ r)

/-- Compatibility with the exact box metric of the existing original
planar pair-strip geometry, retaining all literal cell weights. -/
theorem original_cell_weighted_box_frostman (P : Finset Point3) (b : Frame3)
    (c Delta K : ℝ) (hDelta : 0<Delta) (hK : 0 ≤ K)
    (hslab : ∀ x∈P,|frameCoordinate b 2 x-c| ≤ Delta)
    (hfr : ∀ p∈P,∀ R : ℝ,Delta ≤ R →
      ((P.filter (fun q => distance3 p q ≤ R)).card : ℝ) ≤ K*R*P.card)
    (a : Point2) (r : ℝ) :
    ∑ k∈boxBallCells P b Delta a r,pointWeight P (cellCode b Delta) k ≤
      16*K*max r Delta*P.card := by
  have hsub : boxBallCells P b Delta a r⊆ballCells P b Delta a (2*r) := by
    intro k hk
    obtain ⟨hkP,hkr⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨hkP,?_⟩
    exact (distance2_le_two_boxDistance (cellAnchor Delta k) a).trans (by linarith)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
    intro k _hk _hne
    exact pointWeight_nonneg P (cellCode b Delta) k)
  have hf := original_cell_weighted_frostman P b c Delta K hDelta hK hslab hfr a (2*r)
  have hm : max (2*r) Delta ≤ 2*max r Delta := by
    apply max_le
    · linarith [le_max_left r Delta]
    · linarith [le_max_right r Delta]
  have hmul := mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hK)
  have hmul' := mul_le_mul_of_nonneg_right hmul (Nat.cast_nonneg P.card : (0:ℝ) ≤ P.card)
  calc
    _ ≤ _ := hsum
    _ ≤ 8*K*max (2*r) Delta*P.card := hf
    _ ≤ 16*K*max r Delta*P.card := by nlinarith only [hmul']

end OriginalThreeDimensionalPlanarBoxProjection
