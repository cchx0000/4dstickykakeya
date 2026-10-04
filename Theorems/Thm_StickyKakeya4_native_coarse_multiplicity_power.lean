import Theorems.Thm_StickyKakeya4_native_coarse_power_window
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeCoarseMultiplicityPower
open StickyKakeya4
open scoped ENNReal

/-- The explicit coarse-side window converts the ORIGINAL-delta loss into
its permitted rho power. There is no claim for unrestricted rho near one. -/
lemma original_loss_to_coarse {delta rho window e : ℝ}
    (hd : 0 < delta) (hr : 0 < rho) (he : 0 ≤ e)
    (hwindow : rho ≤ delta^window) :
    rho^(7*e/32) ≤ delta^(7*(window*e/32)) := by
  have hh := Real.rpow_le_rpow hr.le hwindow (show 0 ≤ 7*e/32 by positivity)
  rw [←Real.rpow_mul hd.le] at hh
  convert hh using 1
  congr 1
  ring

lemma coarse_upper_coefficient {delta rho window e epsilon kappa : ℝ}
    (hd : 0 < delta) (hr : 0 < rho) (hr1 : rho ≤ 1) (he : 0 ≤ e)
    (heps : 0 ≤ epsilon) (heSmall : e ≤ epsilon) (hk : 0 ≤ kappa)
    (hwindow : rho ≤ delta^window) :
    (64*rho)^(-kappa-epsilon/2) ≤
      delta^(7*(window*e/32))*rho^(-kappa-epsilon) := by
  have hpos : 0 < 64*rho := by positivity
  have hbase : rho^(kappa+epsilon/2) ≤ (64*rho)^(kappa+epsilon/2) :=
    Real.rpow_le_rpow hr.le (by linarith) (by linarith)
  have hInv := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
    (Real.rpow_pos_of_pos hr _) hbase
  have hOut : (64*rho)^(-kappa-epsilon/2) ≤ rho^(-kappa-epsilon/2) := by
    simpa only [show -kappa-epsilon/2=-(kappa+epsilon/2) by ring,
      Real.rpow_neg hpos.le,Real.rpow_neg hr.le,one_div] using hInv
  calc
    _ ≤ rho^(-kappa-epsilon/2) := hOut
    _ ≤ rho^(7*e/32+(-kappa-epsilon)) :=
      Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
    _ = rho^(7*e/32)*rho^(-kappa-epsilon) := Real.rpow_add hr _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (original_loss_to_coarse hd hr he hwindow)
      (Real.rpow_pos_of_pos hr _).le

/-- Remove the proved original-scale compensation factor from the FULL
coarse multiplicity upper bound, after the requested power window and small
output-class tolerance have actually been supplied. -/
theorem cross_bound_to_rho {delta rho window e epsilon kappa : ℝ} {mu : ℝ≥0∞}
    (hd : 0 < delta) (hr : 0 < rho) (hr1 : rho ≤ 1) (he : 0 ≤ e)
    (heps : 0 ≤ epsilon) (heSmall : e ≤ epsilon) (hk : 0 ≤ kappa)
    (hwindow : rho ≤ delta^window)
    (hcross : (ENNReal.ofReal delta).rpow (7*(window*e/32))*mu ≤
      (ENNReal.ofReal (64*rho)).rpow (-kappa-epsilon/2)) :
    mu ≤ (ENNReal.ofReal rho).rpow (-kappa-epsilon) := by
  have hp : 0 < 64*rho := by positivity
  have hreal := coarse_upper_coefficient hd hr hr1 he heps heSmall hk hwindow
  have hpow : (ENNReal.ofReal (64*rho)).rpow (-kappa-epsilon/2) ≤
      (ENNReal.ofReal delta).rpow (7*(window*e/32))*(ENNReal.ofReal rho).rpow (-kappa-epsilon) := by
    simpa only [ENNReal.ofReal_mul (Real.rpow_pos_of_pos hd _).le,
      ENNReal.ofReal_rpow_of_pos hd,ENNReal.ofReal_rpow_of_pos hr,ENNReal.ofReal_rpow_of_pos hp,
      ENNReal.rpow_eq_pow] using ENNReal.ofReal_le_ofReal hreal
  have hc0 : (ENNReal.ofReal delta).rpow (7*(window*e/32))≠0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hd) ENNReal.ofReal_ne_top).ne'
  have hcT : (ENNReal.ofReal delta).rpow (7*(window*e/32))≠⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_mul_iff_right hc0 hcT).mp (hcross.trans hpow)

end NativeCoarseMultiplicityPower
