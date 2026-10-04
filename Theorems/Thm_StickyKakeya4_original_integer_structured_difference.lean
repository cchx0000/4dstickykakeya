import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalIntegerStructuredDifference

/-- A genuine small original cross-sum and actual retained population
control the two difference sets needed by Bourgain's graph translation. -/
theorem original_difference_bounds (A B : Finset ℤ) {K lambda : ℝ}
    (hA : A.Nonempty) (_hK : 0 ≤ K) (hlambda : 0 ≤ lambda)
    (hBmass : lambda*(A.card:ℝ) ≤ B.card)
    (hsum : ((A+B).card:ℝ) ≤ K*A.card) :
    lambda*((A-A).card:ℝ) ≤ K^2*A.card ∧
    lambda*((B-A).card:ℝ) ≤ K^3*A.card ∧
    lambda^2*((A-A).card:ℝ)*(B-A).card ≤ K^5*(A.card:ℝ)^2 := by
  have hN : (0:ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  have hAA : ((A-A).card:ℝ)*(B.card:ℝ) ≤ ((A+B).card:ℝ)^2 := by
    have hh := Finset.ruzsa_triangle_inequality_sub_add_add A B A
    rw [pow_two]
    exact_mod_cast hh
  have hBB : ((B+B).card:ℝ)*(A.card:ℝ) ≤ ((A+B).card:ℝ)^2 := by
    have hh := Finset.ruzsa_triangle_inequality_add_add_add B A B
    rw [add_comm B A] at hh
    rw [pow_two]
    exact_mod_cast hh
  have hBA : ((B-A).card:ℝ)*(B.card:ℝ) ≤ ((B+B).card:ℝ)*(A+B).card := by
    exact_mod_cast Finset.ruzsa_triangle_inequality_sub_add_add B B A
  have hsquared := pow_le_pow_left₀ (Nat.cast_nonneg (A+B).card) hsum 2
  have hAAmass := mul_le_mul_of_nonneg_left hBmass
    (show (0:ℝ)≤(A-A).card from Nat.cast_nonneg _)
  have hAAbound : lambda*((A-A).card:ℝ) ≤ K^2*A.card := by
    apply (mul_le_mul_iff_left₀ hN).mp
    nlinarith only [hAAmass,hAA,hsquared]
  have hBBbound : ((B+B).card:ℝ) ≤ K^2*A.card := by
    apply (mul_le_mul_iff_left₀ hN).mp
    nlinarith only [hBB,hsquared]
  have hcross := mul_le_mul hBBbound hsum (Nat.cast_nonneg _)
    (show 0≤K^2*(A.card:ℝ) by positivity)
  have hBAmass := mul_le_mul_of_nonneg_left hBmass
    (show (0:ℝ)≤(B-A).card from Nat.cast_nonneg _)
  have hBAbound : lambda*((B-A).card:ℝ) ≤ K^3*A.card := by
    apply (mul_le_mul_iff_left₀ hN).mp
    nlinarith only [hBAmass,hBA,hcross]
  have hp := mul_le_mul hAAbound hBAbound
    (show 0≤lambda*((B-A).card:ℝ) by positivity)
    (show 0≤K^2*(A.card:ℝ) by positivity)
  refine ⟨hAAbound,hBAbound,?_⟩
  nlinarith only [hp]

end OriginalIntegerStructuredDifference
