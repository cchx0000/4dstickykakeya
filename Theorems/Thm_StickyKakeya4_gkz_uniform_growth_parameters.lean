import Theorems.Thm_StickyKakeya4_gkz_original_positive_power
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace GKZUniformGrowthParameters
open GKZOriginalPositivePower GKZOriginalGapEnergy GKZOriginalAnchorProfile
open GKZOriginalProductOverlap

/-- The explicit scalar exponent has a quantitative lower bound on every
compact subinterval of (0,1), with no pointwise-to-uniform inference. -/
lemma growthExponent_lower_on_compact {a sigma : ℝ}
    (ha : 0 < a) (hlo : a ≤ sigma) (hhi : sigma ≤ 1-a) :
    a^2/120 ≤ growthExponent sigma := by
  rw [growthExponent_formula]
  have hs : 0 < sigma := ha.trans_le hlo
  have hs1 : sigma ≤ 1 := by linarith only [ha,hhi]
  have hnum : a^2 ≤ sigma*(1-sigma) := by
    simpa only [pow_two] using mul_le_mul hlo
      (show a ≤ 1-sigma by linarith only [hhi]) ha.le hs.le
  have hden : 0 < 40*(2+sigma) := by positivity
  have hdenhi : 40*(2+sigma) ≤ 120 := by linarith only [hs1]
  apply (div_le_div_iff₀ (by norm_num : (0:ℝ) < 120) hden).mpr
  exact (mul_le_mul_of_nonneg_left hdenhi (sq_nonneg a)).trans
    (mul_le_mul_of_nonneg_right hnum (by norm_num))

/-- Uniform original occupied-cell growth for all matched scalar dimensions
in a fixed compact range. The original scalar profile is still explicit. -/
theorem original_occupied_growth_uniform (A : Finset ℝ) {delta K sigma a : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta) (hdquarter : delta ≤ 1/4)
    (ha : 0 < a) (hlo : a ≤ sigma) (hhi : sigma ≤ 1-a)
    (hcard : (A.card : ℝ)=delta^(-sigma))
    (hbox : ∀ x∈A, 1 ≤ x ∧ x ≤ 2)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|)
    (hprofile : ScalarFrostman A delta K sigma) :
    growthConstant K*delta^(-(a^2/120))*A.card ≤
      ((sumCells delta A).card : ℝ)+(productCells delta A).card := by
  have hsigma : 0 < sigma := ha.trans_le hlo
  have hsigma1 : sigma < 1 := by linarith only [ha,hhi]
  have hd1 : delta ≤ 1 := by linarith only [hdquarter]
  have hg := original_occupied_sum_product_growth A hA hd hdquarter hsigma hsigma1
    hcard hbox hsep hprofile
  have he := growthExponent_lower_on_compact ha hlo hhi
  have hpow : delta^(-(a^2/120)) ≤ delta^(-growthExponent sigma) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg he)
  have hK1 := original_profile_constant_ge_one A hA hd1 hbox hprofile
  have hconst := growthConstant_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hK1)
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hconst.le)
    (Nat.cast_nonneg A.card)).trans hg

end GKZUniformGrowthParameters
