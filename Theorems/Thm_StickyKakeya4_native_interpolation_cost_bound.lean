import Theorems.Thm_StickyKakeya4_actual_scalar_ad_profiles

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace NativeInterpolationCostBound

open ActualScalarADProfiles DyadicAlignmentParameters DyadicADInterpolation

lemma real_interpolation_cost_upper (M H : ℕ) {v : ℝ} (hv : 0 ≤ v) (hv2 : v ≤ 2) :
    realInterpolationLoss M H v ≤ (16 : ℝ) * ((2 : ℝ) ^ M) ^ (2 / (H : ℝ)) := by
  have hg : (gap M H : ℝ) ≤ (M : ℝ) / H + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg H))).le
  have hfrac : 0 ≤ (M : ℝ) / H := div_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg H)
  have hexp : v + v * (gap M H : ℝ) ≤ 4 + (M : ℝ) * (2 / (H : ℝ)) := by
    have hvg := mul_le_mul_of_nonneg_left hg hv
    have hvfrac := mul_le_mul_of_nonneg_right hv2 hfrac
    have he : (2 : ℝ) * ((M : ℝ) / H) = (M : ℝ) * (2 / (H : ℝ)) := by ring
    rw [← he]
    nlinarith only [hv2, hvg, hvfrac]
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  unfold realInterpolationLoss scalePower
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ (2 : ℝ) ^ (4 + (M : ℝ) * (2 / (H : ℝ))) := hp
    _ = (16 : ℝ) * ((2 : ℝ) ^ M) ^ (2 / (H : ℝ)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [Real.rpow_natCast]

/-- One explicit interpolation envelope works for ambient, fiber and quotient
exponents because all three lie in [0,2]. It includes the large-radius tail. -/
lemma full_interpolation_cost_upper (M H : ℕ) {v : ℝ} (hv : 0 ≤ v) (hv2 : v ≤ 2) :
    fullInterpolationLoss M H v ≤ (4096 : ℝ) * ((2 : ℝ) ^ M) ^ (2 / (H : ℝ)) := by
  have hN : (1 : ℝ) ≤ (2 : ℝ) ^ M := one_le_pow₀ (by norm_num)
  have hpow : (1 : ℝ) ≤ ((2 : ℝ) ^ M) ^ (2 / (H : ℝ)) := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hN
      (by positivity : (0 : ℝ) ≤ 2 / (H : ℝ))
  have hJ := real_interpolation_cost_upper M H hv hv2
  have htop := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 64) hv2
  norm_num at htop
  unfold fullInterpolationLoss
  apply max_le
  · exact hJ.trans (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg (by positivity) _))
  · nlinarith only [htop, hpow]

end NativeInterpolationCostBound
