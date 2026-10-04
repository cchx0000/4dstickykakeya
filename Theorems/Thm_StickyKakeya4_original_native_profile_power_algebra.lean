import Theorems.Thm_StickyKakeya4_original_native_power_algebra
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
noncomputable section

namespace OriginalNativeProfilePowerAlgebra
open OriginalNativePowerAlgebra OriginalNativeProjectionBSGCore
open OriginalNativeProjectionFailureComparison OriginalWeakAlphabetSelection
open OriginalKaufmanSharedHost OriginalTwoProjectionCartesian

theorem native_alphabet_profile_upper (n : ℕ) {t h N M : ℝ}
    (ht : 0<t) (ht1 : t≤1) (hh : 0<h) (hh1 : h≤1) (hN : 0<N)
    (hM : M^2=N/t^2) (hlog : ((n:ℝ)+3)^2≤1/t) :
    originalAlphabetProfileCost n (1/t) (1/t) t (t^4/32) t N h M ≤
      ((2:ℝ)^18*3145729)/(t^24*h^2) := by
  have hs := native_strip_upper n ht ht1 hlog
  have hb := native_balance_upper ht hh hh1 hN hM
  have ht16 : t^16≤1 := by simpa using pow_le_pow_left₀ ht.le ht1 16
  have hone : 1≤1/t^16 := (le_div_iff₀ (pow_pos ht 16)).mpr (by simpa using ht16)
  have hstrip : 1+stripConstant n (1/t) ((1/t)/t) (t^4/32)≤3145729/t^16 := by
    calc
      _ ≤ 1/t^16+3145728/t^16 := add_le_add hone hs
      _ = _ := by ring
  have hprod := mul_le_mul hstrip hb
    (show 0≤balanceLoss (t^3/8) N M (fiberBound h) by unfold balanceLoss fiberBound; positivity)
    (by positivity : 0≤3145729/t^16)
  have hbound : 8*(1+stripConstant n (1/t) ((1/t)/t) (t^4/32))*
      balanceLoss (t^3/8) N M (fiberBound h)≤((2:ℝ)^18*3145729)/(t^24*h^2) := by
    calc
      _ ≤ 8*((3145729/t^16)*(32768/(t^8*h^2))) := by nlinarith only [hprod]
      _ = _ := by ring
  unfold originalAlphabetProfileCost
  refine max_le ?_ hbound
  apply (le_div_iff₀ (mul_pos (pow_pos ht 24) (sq_pos_of_pos hh))).mpr
  have ht24 : t^24≤1 := by simpa using pow_le_pow_left₀ ht.le ht1 24
  have hh2 : h^2≤1 := by simpa using pow_le_pow_left₀ hh.le hh1 2
  have hp := mul_le_mul ht24 hh2 (sq_nonneg h) (by norm_num : (0:ℝ)≤1)
  norm_num at hp ⊢
  linarith only [hp]

theorem native_retained_profile_upper (n : ℕ) {t h N M u : ℝ}
    (ht : 0<t) (ht1 : t≤1) (hh : 0<h) (hh1 : h≤1) (hN : 0<N)
    (hM : M^2=N/t^2) (hlog : ((n:ℝ)+3)^2≤1/t) (hu1 : u≤1) :
    originalAlphabetProfileCost n (1/t) (1/t) t (t^4/32) t N h M*(16/h)^u/
      originalRetention (t^3/16) N h M≤((2:ℝ)^74*3145729)/(t^44*h^11) := by
  have hKA := native_alphabet_profile_upper n ht ht1 hh hh1 hN hM hlog
  have hret := (native_density_retention_lower ht hh hh1 hN hM).2
  have hbase : 1≤16/h := (le_div_iff₀ hh).mpr (by linarith only [hh1])
  have hpow : (16/h)^u≤16/h := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase hu1
  have hnum := mul_le_mul hKA hpow (Real.rpow_nonneg (by positivity) u) (by positivity)
  have hretpos : 0<originalRetention (t^3/16) N h M :=
    (show 0<t^20*h^8/(2:ℝ)^52 by positivity).trans_le hret
  calc
    _ ≤ ((((2:ℝ)^18*3145729)/(t^24*h^2))*(16/h))/
        (t^20*h^8/(2:ℝ)^52) := div_le_div₀
          (by positivity) hnum (by positivity) hret
    _ = _ := by field_simp; ring

theorem native_coefficient_profile_upper {t h u : ℝ}
    (ht : 0<t) (hh : 0<h) (hh1 : h≤1) (hu1 : u≤1) :
    (2*(1/t)/t)*(64/h^2)^u≤128/(t^2*h^2) := by
  have hh2 : h^2≤1 := by simpa using pow_le_pow_left₀ hh.le hh1 2
  have hbase : 1≤64/h^2 := (le_div_iff₀ (sq_pos_of_pos hh)).mpr (by linarith only [hh2])
  have hpow : (64/h^2)^u≤64/h^2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase hu1
  calc
    _ ≤ (2*(1/t)/t)*(64/h^2) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

end OriginalNativeProfilePowerAlgebra
