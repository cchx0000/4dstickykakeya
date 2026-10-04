import Theorems.Thm_StickyKakeya4_original_three_dimensional_expanded_band_count
import Theorems.Thm_StickyKakeya4_original_three_dimensional_slice_maximizer
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalExpandedSliceMultiplicity
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalUnitSlabs OriginalThreeDimensionalUnitNormals
open OriginalThreeDimensionalCapCoordinates OriginalThreeDimensionalCapCount
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalSliceMaximizer
open OriginalThreeDimensionalExpandedBandCount

abbrev SliceLabel := DirectionLabel×ℤ

def slicesThroughPair (P : Finset Point3) (S : Finset SliceLabel) (rho Delta : ℝ)
    (p q : Point3) : Finset SliceLabel :=
  S.filter (fun z => p∈enlargedSlice P rho z.1 z.2 Delta ∧ q∈enlargedSlice P rho z.1 z.2 Delta)

/-- Original bounded direction-grid coefficients give a uniform bound
for the true normalizing length. -/
theorem original_grid_normal_length_le_five (rho : ℝ) (d : DirectionLabel)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hd : d∈normalGrid rho) : normalLength rho d ≤ 5 := by
  obtain ⟨h1,h2⟩ := actual_grid_coefficients rho d hrho hrho1 hd
  have hs1 : (rho*(d.2.1:ℝ))^2 ≤ 16 := by
    simpa only [sq_abs,show (4:ℝ)^2=16 by norm_num] using pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hs2 : (rho*(d.2.2:ℝ))^2 ≤ 1 := by
    simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) h2 2
  unfold normalLength
  apply (Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 5)).mpr
  nlinarith only [hs1,hs2]

/-- Actual expanded-slice membership gives an original unnormalized
center error, with no new or rounded endpoint. -/
theorem original_expanded_slice_raw_error (P : Finset Point3) (rho Delta : ℝ)
    (d : DirectionLabel) (k : ℤ) (x : Point3) (hrho : 0 < rho)
    (hrho1 : rho ≤ 1) (hDelta : 0 ≤ Delta) (hd : d∈normalGrid rho)
    (hx : x∈enlargedSlice P rho d k Delta) : |value rho d x-rho*k| ≤ 5*Delta := by
  have hL : 0 < normalLength rho d := lt_of_lt_of_le (by norm_num) (normal_length_one_le rho d)
  have hh := (Finset.mem_filter.mp hx).2
  change |value rho d x/normalLength rho d-rho*k/normalLength rho d| ≤ Delta at hh
  rw [← sub_div,abs_div,abs_of_pos hL] at hh
  have hb := (div_le_iff₀ hL).mp hh
  have hm := mul_le_mul_of_nonneg_left (original_grid_normal_length_le_five rho d hrho hrho1 hd) hDelta
  nlinarith only [hb,hm]

/-- Exact original-label pair multiplicity for the actual enlarged slabs.
All repeated original offsets are counted. The loss (Delta/rho)^3 is
explicit and is not replaced by source disjointness. -/
theorem original_expanded_slice_pair_multiplicity (P : Finset Point3)
    (S : Finset SliceLabel) (rho Delta : ℝ) (p q : Point3)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hDelta : rho ≤ Delta)
    (hp : ∀ i,|p i| ≤ 1) (hq : ∀ i,|q i| ≤ 1)
    (hS : ∀ z∈S,z.1∈normalGrid rho) :
    ((slicesThroughPair P S rho Delta p q).card : ℝ)*rho^3*max (distance3 p q) Delta ≤
      720000*Delta^2 := by
  let Q := slicesThroughPair P S rho Delta p q
  let T := Q.image Prod.fst
  have hDp : 0 < Delta := hrho.trans_le hDelta
  have hgrid (z : SliceLabel) (hz : z∈Q) : z.1∈normalGrid rho := hS z (Finset.mem_filter.mp hz).1
  have hrawp (z : SliceLabel) (hz : z∈Q) : |value rho z.1 p-rho*z.2| ≤ 5*Delta :=
    original_expanded_slice_raw_error P rho Delta z.1 z.2 p hrho hrho1 hDp.le
      (hgrid z hz) (Finset.mem_filter.mp hz).2.1
  have hrawq (z : SliceLabel) (hz : z∈Q) : |value rho z.1 q-rho*z.2| ≤ 5*Delta :=
    original_expanded_slice_raw_error P rho Delta z.1 z.2 q hrho hrho1 hDp.le
      (hgrid z hz) (Finset.mem_filter.mp hz).2.2
  have hT : T⊆normalGrid rho := by
    intro d hd; obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hd; exact hgrid z hz
  have hband (d : DirectionLabel) (hd : d∈T) : |value rho d q-value rho d p| ≤ 10*Delta := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hd
    have hh := abs_sub (value rho z.1 q-rho*z.2) (value rho z.1 p-rho*z.2)
    have he : (value rho z.1 q-rho*z.2)-(value rho z.1 p-rho*z.2)=value rho z.1 q-value rho z.1 p := by ring
    rw [he] at hh
    linarith only [hh,hrawp z hz,hrawq z hz]
  have ht := original_expanded_normal_band_count T rho Delta p q hrho hrho1 hDelta hp hq hT hband
  have hf : ∀ d∈T,((Q.filter (fun z => z.1=d)).card : ℝ)*rho ≤ 12*Delta := by
    intro d _hd
    let F := Q.filter (fun z => z.1=d)
    have hi : Set.InjOn Prod.snd (↑F : Set SliceLabel) := by
      intro z hz z' hz' he
      exact Prod.ext ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm) he
    have hs (k : ℤ) (hk : k∈F.image Prod.snd) : |rho*(k:ℝ)-value rho d p| ≤ 5*Delta := by
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hzQ,hzd⟩ := Finset.mem_filter.mp hz
      simpa only [hzd,abs_sub_comm] using hrawp z hzQ
    have hc := integer_interval_mass (F.image Prod.snd) rho (5*Delta) (value rho d p) hrho (by positivity) hs
    rw [Finset.card_image_of_injOn hi] at hc
    change (F.card : ℝ)*rho ≤ 12*Delta
    linarith only [hc,hDelta]
  have hc := weighted_fiber_count Q Prod.fst rho (12*Delta) hf
  have hm := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ rho^2*max (distance3 p q) Delta by positivity)
  have hn := mul_le_mul_of_nonneg_left ht (show 0 ≤ 12*Delta by positivity)
  change (Q.card : ℝ)*rho^3*max (distance3 p q) Delta ≤ 720000*Delta^2
  nlinarith only [hm,hn]

end OriginalThreeDimensionalExpandedSliceMultiplicity
