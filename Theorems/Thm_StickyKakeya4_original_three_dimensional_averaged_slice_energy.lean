import Theorems.Thm_StickyKakeya4_original_three_dimensional_expanded_slice_multiplicity
import Theorems.Thm_StickyKakeya4_original_three_dimensional_slice_energy_basic
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3400000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalAveragedSliceEnergy
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalUnitSlabs OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalSliceMaximizer OriginalThreeDimensionalExpandedSliceMultiplicity
open OriginalThreeDimensionalPairEnergy OriginalThreeDimensionalLocalizedEnergy

/-- Exact finite interchange on the original slice populations. -/
theorem original_slice_energy_sum_swap (P : Finset Point3) (S : Finset SliceLabel)
    (rho Delta : ℝ) :
    (∑ z∈S,sliceEnergy (enlargedSlice P rho z.1 z.2 Delta) Delta)=
      ∑ p∈P,∑ q∈P,((slicesThroughPair P S rho Delta p q).card : ℝ)/max (distance3 p q) Delta := by
  have hslice (z : SliceLabel) : sliceEnergy (enlargedSlice P rho z.1 z.2 Delta) Delta=
      ∑ p∈P,∑ q∈P,if p∈enlargedSlice P rho z.1 z.2 Delta ∧ q∈enlargedSlice P rho z.1 z.2 Delta
        then 1/max (distance3 p q) Delta else 0 := by
    simp only [sliceEnergy,slicePotential,enlargedSlice,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpp : |unitValue rho z.1 p-rho*z.2/normalLength rho z.1| ≤ Delta
    · simp only [hpp,if_true,Finset.mem_filter,hp,true_and]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [hq,true_and]
    · simp only [hpp,if_false,Finset.mem_filter,hp,true_and,false_and,Finset.sum_const_zero]
  calc
    _ = ∑ z∈S,∑ p∈P,∑ q∈P,if p∈enlargedSlice P rho z.1 z.2 Delta ∧ q∈enlargedSlice P rho z.1 z.2 Delta
        then 1/max (distance3 p q) Delta else 0 := Finset.sum_congr rfl (fun z _hz => hslice z)
    _ = ∑ p∈P,∑ q∈P,∑ z∈S,if p∈enlargedSlice P rho z.1 z.2 Delta ∧ q∈enlargedSlice P rho z.1 z.2 Delta
        then 1/max (distance3 p q) Delta else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _hp
      apply Finset.sum_congr rfl
      intro q _hq
      rw [← Finset.sum_filter]
      simp [slicesThroughPair,div_eq_mul_inv,mul_comm]

/-- The original two-Frostman law pays the complete enlarged-slice I1
sum, including diagonal pairs and every original normal/offset label.
The actual scale ratio is retained explicitly. -/
theorem original_averaged_slice_energy (P : Finset Point3) (S : Finset SliceLabel)
    (delta rho Delta K : ℝ) (N : ℕ)
    (hd : 0 < delta) (hdrho : delta ≤ rho) (hrho1 : rho ≤ 1) (hDelta : rho ≤ Delta)
    (hK : 1 ≤ K) (hterminal : 1 ≤ 2*dyadicRadius Delta N)
    (hbox : ∀ p∈P,∀ j,|p j| ≤ 1) (hS : ∀ z∈S,z.1∈normalGrid rho)
    (hfrostman : ∀ p∈P,∀ r : ℝ,delta ≤ r → r ≤ 1 →
      ((P.filter (fun q => distance3 p q ≤ r)).card : ℝ) ≤ K*r^2*P.card) :
    rho^3*(∑ z∈S,sliceEnergy (enlargedSlice P rho z.1 z.2 Delta) Delta) ≤
      2880000*Delta^2*((N:ℝ)+1)*K*(P.card : ℝ)^2 := by
  have hrho := hd.trans_le hdrho
  have hDp := hrho.trans_le hDelta
  have hpair (p q : Point3) (hp : p∈P) (hq : q∈P) :
      ((slicesThroughPair P S rho Delta p q).card : ℝ)/max (distance3 p q) Delta ≤
        (720000*Delta^2/rho^3)*inverseSquareKernel Delta (distance3 p q) := by
    have hM : 0 < max (distance3 p q) Delta := hDp.trans_le (le_max_right _ _)
    have hc := original_expanded_slice_pair_multiplicity P S rho Delta p q hrho hrho1 hDelta
      (hbox p hp) (hbox q hq) hS
    have hh : ((slicesThroughPair P S rho Delta p q).card : ℝ) ≤
        720000*Delta^2/(rho^3*max (distance3 p q) Delta) := by
      apply (le_div_iff₀ (mul_pos (pow_pos hrho 3) hM)).mpr
      nlinarith only [hc]
    have ht := div_le_div_of_nonneg_right hh hM.le
    calc
      _ ≤ 720000*Delta^2/(rho^3*max (distance3 p q) Delta)/max (distance3 p q) Delta := ht
      _ = _ := by
        simp only [inverseSquareKernel,div_eq_mul_inv,mul_inv_rev]
        ring
  have henergy := original_localized_pair_energy P P delta Delta K N (Finset.Subset.refl P)
    hd (hdrho.trans hDelta) hK hterminal hfrostman
  rw [original_slice_energy_sum_swap]
  have hsum : (∑ p∈P,∑ q∈P,((slicesThroughPair P S rho Delta p q).card : ℝ)/max (distance3 p q) Delta) ≤
      (720000*Delta^2/rho^3)*(∑ p∈P,∑ q∈P,inverseSquareKernel Delta (distance3 p q)) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => hpair p q hp hq))
  have h1 := mul_le_mul_of_nonneg_left hsum (show 0 ≤ rho^3 by positivity)
  have he : rho^3*(720000*Delta^2/rho^3)=720000*Delta^2 := by field_simp
  rw [← mul_assoc,he] at h1
  have h2 := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 720000*Delta^2 by positivity)
  nlinarith only [h1,h2]

end OriginalThreeDimensionalAveragedSliceEnergy
