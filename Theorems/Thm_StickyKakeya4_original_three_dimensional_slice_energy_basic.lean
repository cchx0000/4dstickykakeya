import Theorems.Thm_StickyKakeya4_original_three_dimensional_localized_energy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalAveragedSliceEnergy
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubePairCount OriginalTubeGraphPairGeometry

def slicePotential (Q : Finset Point3) (Delta : ℝ) (p : Point3) : ℝ :=
  ∑ q∈Q,1/max (distance3 p q) Delta

def sliceEnergy (Q : Finset Point3) (Delta : ℝ) : ℝ :=
  ∑ p∈Q,slicePotential Q Delta p

theorem slice_potential_nonneg (Q : Finset Point3) (Delta : ℝ) (hDelta : 0 < Delta) (p : Point3) :
    0 ≤ slicePotential Q Delta p := by
  unfold slicePotential
  exact Finset.sum_nonneg (fun q _hq => le_of_lt (one_div_pos.mpr (hDelta.trans_le (le_max_right _ _))))

/-- The diagonal-inclusive I1 energy controls the square of the actual
slice mass on the bounded original box. -/
theorem original_slice_energy_lower (Q : Finset Point3) (Delta : ℝ)
    (hDelta : 0 < Delta) (hDelta1 : Delta ≤ 1) (hbox : ∀ p∈Q,∀ j,|p j| ≤ 1) :
    (Q.card : ℝ)^2 ≤ 4*sliceEnergy Q Delta := by
  have hpoint (p : Point3) (hp : p∈Q) : (Q.card : ℝ)/4 ≤ slicePotential Q Delta p := by
    calc
      _ = ∑ _q∈Q,(1/4:ℝ) := by simp; ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro q hq
        have hmax : max (distance3 p q) Delta ≤ 4 :=
          max_le (original_box_distance_le_four p q (hbox p hp) (hbox q hq)) (hDelta1.trans (by norm_num))
        exact one_div_le_one_div_of_le (hDelta.trans_le (le_max_right _ _)) hmax
  have hh := Finset.sum_le_sum hpoint
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  change (Q.card : ℝ)^2 ≤ 4*(∑ p∈Q,slicePotential Q Delta p)
  nlinarith only [hh]

/-- The exact potential at an original point bounds all original ball
populations at radii above the cutoff. No separated representative is
substituted for a source point. -/
theorem original_ball_count_from_slice_potential (Q : Finset Point3) (Delta r : ℝ)
    (p : Point3) (hDelta : 0 < Delta) (hr : Delta ≤ r) :
    ((Q.filter (fun q => distance3 p q ≤ r)).card : ℝ) ≤ r*slicePotential Q Delta p := by
  have hrp := hDelta.trans_le hr
  let B := Q.filter (fun q => distance3 p q ≤ r)
  have hlo : (B.card : ℝ)/r ≤ ∑ q∈B,1/max (distance3 p q) Delta := by
    calc
      _ = ∑ _q∈B,1/r := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun q hq =>
        one_div_le_one_div_of_le (hDelta.trans_le (le_max_right _ _))
          (max_le (Finset.mem_filter.mp hq).2 hr))
  have hhi : (∑ q∈B,1/max (distance3 p q) Delta) ≤ slicePotential Q Delta p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun q _hq _hqB =>
      le_of_lt (one_div_pos.mpr (hDelta.trans_le (le_max_right _ _))))
  have hh := (div_le_iff₀ hrp).mp (hlo.trans hhi)
  simpa only [mul_comm] using hh

end OriginalThreeDimensionalAveragedSliceEnergy
