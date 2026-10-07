import Theorems.Thm_StickyKakeya4_native_conditional_angular_scale_readback
import Theorems.Thm_StickyKakeya4_native_middle_window_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeConditionalAngularPowerBudget
open NativeMiddleWindowBalance

lemma original_loss_to_rank {delta r power loss : ℝ}
    (hd : 0< delta) (hr : 0< r) (ha : 0< power) (hloss : 0≤ loss)
    (hscale : r≤ delta^power) : delta^(-loss)≤ r^(-(loss/power)) := by
  have hh := Real.rpow_le_rpow_of_nonpos hr hscale
    (neg_nonpos.mpr (div_nonneg hloss ha.le))
  rw [←Real.rpow_mul hd.le] at hh
  have he : power*(-(loss/power))= -loss := by field_simp
  rwa [he] at hh

lemma first_radix_fourth_cost {delta eta seed : ℝ}
    (hd : 0< delta) (hd1 : delta≤ 1) (heta : 0≤ eta) (F Q : ℕ) (hF : 0< F)
    (H : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta)≤ delta^(-(seed/8))) :
    (Q:ℝ)^4≤ delta^(-(seed/4)) := by
  have hh := radix_sq_le_of_transfer_cost hd hd1 heta F Q hF H
  calc
    _ = ((Q:ℝ)^2)^2 := by ring
    _ ≤  (delta^(-(seed/8)))^2 := pow_le_pow_left₀ (sq_nonneg _) hh 2
    _ = _ := by rw [←Real.rpow_mul_natCast hd.le]; congr 1; ring

lemma angular_slack_to_rank {rho sigma Delta r epsilon : ℝ}
    (hrho : 0< rho) (hsigma : 0< sigma) (hsigma1 : sigma≤ 1)
    (hDelta : 0< Delta) (hDeltaRho : Delta≤ rho) (hr : 0< r) (hrDelta : r≤ Delta^2)
    (he : 0≤ epsilon) : (rho/sigma)^(-epsilon)≤ r^(-epsilon/2) := by
  have hrhoRatio : rho≤ rho/sigma := (le_div_iff₀ hsigma).mpr
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsigma1 hrho.le)
  have h1 := Real.rpow_le_rpow_of_nonpos hrho hrhoRatio (neg_nonpos.mpr he)
  have h2 := Real.rpow_le_rpow_of_nonpos hDelta hDeltaRho (neg_nonpos.mpr he)
  have h3 := Real.rpow_le_rpow_of_nonpos hr hrDelta (show -epsilon/2≤ 0 by linarith only [he])
  rw [←Real.rpow_natCast,←Real.rpow_mul hDelta.le] at h3
  norm_num only [Nat.cast_ofNat] at h3
  have hexp : (2:ℝ)*(-epsilon/2)= -epsilon := by ring
  rw [hexp] at h3
  exact h1.trans (h2.trans h3)

/-- All first-core radix, local-admission and angular-exponent losses are
paid against the actual stopping r. The final angular exponent is exactly
kappa; no delta loss is silently identified with a rho loss. -/
theorem source_conditional_power_cost {delta r power eta seed budget epsilon kappa localThickness rho sigma Delta : ℝ}
    (hd : 0< delta) (hd1 : delta≤ 1) (hr : 0< r) (ha : 0< power)
    (hscale : r≤ delta^power) (heta : 0≤ eta) (hseed : 0≤ seed)
    (hbudget : 0≤ budget) (he : 0≤ epsilon) (hLocal : delta≤ localThickness)
    (hrho : 0< rho) (hsigma : 0< sigma) (hsigma1 : sigma≤ 1)
    (hDelta : 0< Delta) (hDeltaRho : Delta≤ rho) (hrDelta : r≤ Delta^2)
    (F Q : ℕ) (hF : 0< F)
    (H : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta)≤ delta^(-(seed/8))) :
    (Q:ℝ)^4*localThickness^(-budget)*(rho/sigma)^(-kappa-epsilon)≤ 
      r^(-((budget+seed/4)/power+epsilon/2))*(sigma/rho)^kappa := by
  have hQ := first_radix_fourth_cost hd hd1 heta F Q hF H
  have hL := Real.rpow_le_rpow_of_nonpos hd hLocal (neg_nonpos.mpr hbudget)
  have hQL : (Q:ℝ)^4*localThickness^(-budget)≤ delta^(-(budget+seed/4)) := by
    have hh := mul_le_mul hQ hL (Real.rpow_nonneg (hd.trans_le hLocal).le _) (Real.rpow_nonneg hd.le _)
    rw [←Real.rpow_add hd] at hh
    convert hh using 1
    congr 1
    ring
  have hQLRank := hQL.trans (original_loss_to_rank hd hr ha (by positivity) hscale)
  have hAngular := angular_slack_to_rank hrho hsigma hsigma1 hDelta hDeltaRho hr hrDelta he
  have hratio : 0< rho/sigma := div_pos hrho hsigma
  have hflip : (rho/sigma)^(-kappa)=(sigma/rho)^kappa := by
    rw [Real.rpow_neg hratio.le,Real.div_rpow hrho.le hsigma.le,inv_div,
      ←Real.div_rpow hsigma.le hrho.le]
  have hsplit : (rho/sigma)^(-kappa-epsilon)=(rho/sigma)^(-epsilon)*(rho/sigma)^(-kappa) := by
    rw [←Real.rpow_add hratio]
    congr 1
    ring
  rw [hsplit,hflip,←mul_assoc]
  have hh := mul_le_mul hQLRank hAngular (Real.rpow_nonneg hratio.le _) (Real.rpow_nonneg hr.le _)
  have hsum : r^(-((budget+seed/4)/power))*r^(-epsilon/2)=r^(-((budget+seed/4)/power+epsilon/2)) := by
    rw [←Real.rpow_add hr]
    congr 1
    ring
  rw [hsum] at hh
  exact mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (div_nonneg hsigma.le hrho.le) _)

end NativeConditionalAngularPowerBudget
