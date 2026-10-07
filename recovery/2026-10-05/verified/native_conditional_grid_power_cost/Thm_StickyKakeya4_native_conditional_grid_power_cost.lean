import Theorems.Thm_StickyKakeya4_native_conditional_grid_coverage
import Theorems.Thm_StickyKakeya4_native_conditional_angular_scale_readback

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000

noncomputable section
namespace NativeConditionalGridPowerCost
open NativeCommonDirectionPhaseMenu NativeConditionalGridCoverage

lemma dyadic_width_ratio {c s : ℕ} (hcs : c≤ s) :
    ((64:ℝ)/((2^c:ℕ):ℝ))/(64/((2^s:ℕ):ℝ))=((2^(s-c):ℕ):ℝ) := by
  have hp : (2^s:ℕ)=2^c*2^(s-c) := by rw [←pow_add,Nat.add_sub_of_le hcs]
  rw [hp]
  push_cast
  field_simp

lemma middle_width_dyadic (m : ℕ) (hm : 6≤ m) :
    (64:ℝ)/((2^m:ℕ):ℝ)=(2:ℝ)⁻¹^(m-6) := by
  rw [dyadic_sigma m hm,Nat.cast_pow,Nat.cast_ofNat,one_div,inv_pow]

lemma gap_cost (m K s c : ℕ) (hm : 6≤ m) (hK : 0< K)
    (H : ((s-c:ℕ):ℝ)≤ ((m-6:ℕ):ℝ)/K+1) :
    ((2^(s-c):ℕ):ℝ)≤ 2*((64:ℝ)/((2^m:ℕ):ℝ))^(-(1/(K:ℝ))) :=
  NativeFixedSizeScaleMenu.dyadic_gap_power (m-6) s c K hK (middle_width_dyadic m hm) H

/-- Interpolating both geometric scales costs only 16*r^(-2/K), using
kappa≤1 and the actual r≤Delta². The slope fiber cost is three-dimensional;
spatial cells use exact dyadic containment and introduce no cardinal factor. -/
theorem two_scale_cost {Delta r rho rho0 sigma sigma0 P kappa : ℝ} (K : ℕ)
    (hK : 0< K) (hD : 0< Delta) (hD1 : Delta≤ 1) (hr : 0< r) (hrD : r≤ Delta^2)
    (hrho : 0< rho) (hsigma : 0< sigma) (hsigma0 : 0< sigma0)
    (hRho : rho≤ rho0) (hk0 : 0≤ kappa) (hk1 : kappa≤ 1) (hP0 : 0≤ P)
    (hP : P≤ 2*Delta^(-(1/(K:ℝ))))
    (hSigma : sigma0/sigma≤ 2*Delta^(-(1/(K:ℝ)))) :
    P^3*(sigma0/rho0)^kappa≤
      16*r^(-(2/(K:ℝ)))*(sigma/rho)^kappa := by
  have hKR : (0:ℝ)<K := by exact_mod_cast hK
  let B := 2*Delta^(-(1/(K:ℝ)))
  have hp1 : 1≤ Delta^(-(1/(K:ℝ))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hD hD1 (neg_nonpos.mpr (div_nonneg (by norm_num) hKR.le))
  have hB1 : 1≤ B := by dsimp [B]; linarith only [hp1]
  have hRatio : sigma0/rho0≤ B*(sigma/rho) := by
    have hS : sigma0≤ B*sigma := (div_le_iff₀ hsigma).mp hSigma
    calc
      _ ≤ sigma0/rho := div_le_div_of_nonneg_left hsigma0.le hrho hRho
      _ ≤ (B*sigma)/rho := div_le_div_of_nonneg_right hS hrho.le
      _ = _ := by ring
  have hPow := Real.rpow_le_rpow (div_nonneg hsigma0.le (hrho.trans_le hRho).le) hRatio hk0
  rw [Real.mul_rpow (by linarith only [hB1]) (by positivity)] at hPow
  have hPow' : (sigma0/rho0)^kappa≤ B*(sigma/rho)^kappa := hPow.trans
    (mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hB1 hk1) (by positivity))
  have hP3 : P^3≤ B^3 := pow_le_pow_left₀ hP0 hP 3
  have hTotal := mul_le_mul hP3 hPow' (Real.rpow_nonneg (div_nonneg hsigma0.le (hrho.trans_le hRho).le) _) (pow_nonneg (le_trans (by norm_num) hB1) 3)
  have hB4 : B^3*(B*(sigma/rho)^kappa)=16*Delta^(-(4/(K:ℝ)))*(sigma/rho)^kappa := by
    have hBpow : B^4=16*Delta^(-(4/(K:ℝ))) := by
      dsimp [B]
      rw [mul_pow,←Real.rpow_mul_natCast hD.le]
      norm_num only [Nat.cast_ofNat]
      congr 1
      congr 1
      ring
    calc
      _ = B^4*(sigma/rho)^kappa := by ring
      _ = _ := by rw [hBpow]
  rw [hB4] at hTotal
  have hrPay := Real.rpow_le_rpow_of_nonpos hr hrD (show -(2/(K:ℝ))≤ 0 from neg_nonpos.mpr (div_nonneg (by norm_num) hKR.le))
  rw [←Real.rpow_natCast,←Real.rpow_mul hD.le] at hrPay
  norm_num only [Nat.cast_ofNat] at hrPay
  have he : (2:ℝ)*(-(2/(K:ℝ)))= -(4/(K:ℝ)) := by ring
  rw [he] at hrPay
  exact hTotal.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hrPay (by norm_num)) (by positivity))

end NativeConditionalGridPowerCost
