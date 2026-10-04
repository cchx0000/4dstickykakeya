import Theorems.Thm_StickyKakeya4_balanced_bsg_iteration_core

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace BalancedBSGPolynomialLoss

open BalancedBSGIterationCore

theorem difference_constant_polynomial {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    differenceConstant eta * eta ^ 28 ≤ (2 : ℝ) ^ 92 := by
  have hthree : eta ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ heta.le heta1 3
  have htwentyeight : eta ^ 28 ≤ 1 := by
    simpa using pow_le_pow_left₀ heta.le heta1 28
  have hinner : (2 : ℝ) ^ 24 + 2 ^ 17 * eta ^ 3 ≤ 2 ^ 25 := by
    nlinarith only [hthree]
  have hid : differenceConstant eta * eta ^ 28 =
      (2 : ℝ) ^ 16 * (2 ^ 24 + 2 ^ 17 * eta ^ 3) ^ 3 + eta ^ 28 := by
    unfold differenceConstant
    field_simp
    ring
  calc
    differenceConstant eta * eta ^ 28 =
        (2 : ℝ) ^ 16 * (2 ^ 24 + 2 ^ 17 * eta ^ 3) ^ 3 + eta ^ 28 := hid
    _ ≤ (2 : ℝ) ^ 16 * (2 ^ 25) ^ 3 + 1 := by gcongr
    _ ≤ (2 : ℝ) ^ 92 := by norm_num

theorem growth_constant_polynomial {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    growthConstant eta * eta ^ 58 ≤ (2 : ℝ) ^ 192 := by
  have hc := difference_constant_polynomial heta heta1
  have hc0 : 0 ≤ differenceConstant eta * eta ^ 28 := by
    unfold differenceConstant
    positivity
  have hid : growthConstant eta * eta ^ 58 =
      (2 : ℝ) ^ 8 * (differenceConstant eta * eta ^ 28) ^ 2 := by
    unfold growthConstant
    field_simp
    ring
  calc
    growthConstant eta * eta ^ 58 =
        (2 : ℝ) ^ 8 * (differenceConstant eta * eta ^ 28) ^ 2 := hid
    _ ≤ (2 : ℝ) ^ 8 * ((2 : ℝ) ^ 92) ^ 2 := by gcongr
    _ = (2 : ℝ) ^ 192 := by norm_num

theorem growth_constant_le_div {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    growthConstant eta ≤ (2 : ℝ) ^ 192 / eta ^ 58 := by
  exact (le_div_iff₀ (pow_pos heta 58)).2 (growth_constant_polynomial heta heta1)

end BalancedBSGPolynomialLoss
