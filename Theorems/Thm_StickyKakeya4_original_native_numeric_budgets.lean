import Theorems.Thm_StickyKakeya4_original_native_projection_power_cutoff
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048
noncomputable section

namespace OriginalNativeNumericBudgets
open OriginalNativePowerAlgebra OriginalNativeProfilePowerAlgebra
open OriginalNativeProjectionPowerCutoff OriginalNativeComparisonPowerAlgebra
open OriginalNativeProjectionBSGCore OriginalNativeProjectionFailureComparison
open OriginalTwoProjectionCartesian

theorem native_small_query_budgets {t h u : ℝ} (ht : 0<t) (htsmall : t≤1/64)
    (_hh : 0<h) (hp : h^u=t^8) :
    0<t^4/32 ∧ t^4/32<1 ∧ t^4/32≤t^3/16 ∧
      (((1/t)/t)/(1-t^4/32))*h^u≤t^3/16 ∧
      (1/t)*h^u≤t/4 := by
  have ht1 : t≤1 := by linarith only [htsmall]
  have hpow (n : ℕ) : t^n≤1 := by simpa using pow_le_pow_left₀ ht.le ht1 n
  have ht3 : t^3≤1/64 := (show t^3≤t from by simpa only [pow_one] using pow_le_pow_of_le_one ht.le ht1 (by omega : 1≤3)).trans htsmall
  have ht6 : t^6≤1/64 := (show t^6≤t from by simpa only [pow_one] using pow_le_pow_of_le_one ht.le ht1 (by omega : 1≤6)).trans htsmall
  have heps : t^4/32≤1/2 := by linarith only [hpow 4]
  have hden : 0<1-t^4/32 := by linarith only [heps]
  refine ⟨by positivity,by linarith only [heps],?_,?_,?_⟩
  · have hm := mul_le_mul_of_nonneg_right ht1 (show 0≤t^3 by positivity)
    nlinarith only [hm,pow_pos ht 3]
  · rw [hp]
    have hid : (((1/t)/t)/(1-t^4/32))*t^8=t^6/(1-t^4/32) := by field_simp
    rw [hid]
    calc
      _ ≤ t^6/(1/2) := div_le_div_of_nonneg_left (by positivity) (by norm_num)
        (by linarith only [heps])
      _ ≤ t^3/16 := by
        have hm := mul_le_mul_of_nonneg_left ht3 (show 0≤t^3 by positivity)
        nlinarith only [hm]
  · rw [hp]
    have hid : (1/t)*t^8=t*t^6 := by field_simp
    rw [hid]
    have hm := mul_le_mul_of_nonneg_left ht6 ht.le
    nlinarith only [hm,ht]

theorem native_secondary_profile_envelope {t h : ℝ}
    (ht : 0<t) (ht1 : t≤1) (hh : 0<h) (hh1 : h≤1) :
    128/(t^2*h^2)≤profileConstant/(t^44*h^11) ∧
      4/h^2≤profileConstant/(t^44*h^11) := by
  have ht2 : t^2≤1 := by simpa using pow_le_pow_left₀ ht.le ht1 2
  have hp : t^44*h^11≤t^2*h^2 := mul_le_mul
    (pow_le_pow_of_le_one ht.le ht1 (by omega : 2≤44))
    (pow_le_pow_of_le_one hh.le hh1 (by omega : 2≤11))
    (by positivity) (by positivity)
  have hc : (128:ℝ)≤profileConstant := by norm_num [profileConstant]
  have hlarge : 128/(t^2*h^2)≤profileConstant/(t^44*h^11) :=
    div_le_div₀ (by unfold profileConstant; positivity) hc (by positivity) hp
  refine ⟨hlarge,?_⟩
  have hsmall : 4/h^2≤128/(t^2*h^2) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hh) (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right ht2 (show 0≤h^2 by positivity)
    nlinarith only [hm,sq_nonneg h]
  exact hsmall.trans hlarge

/-- At the actual finer native mesh, the original scalar profile budgets and
the contradiction's reverse inequality follow from the constructed monomial
cutoffs. No graph-energy or projected-profile premise is supplied. -/
theorem native_profile_and_comparison_budgets (n : ℕ)
    {delta t h N M u eta epsilon : ℝ}
    (hd : 0<delta) (ht : 0<t) (ht1 : t≤1) (hh : 0<h) (hh1 : h≤1)
    (hN : 0<N) (hM : M^2=N/t^2) (hu1 : u≤1) (heta : 0<eta) (heps : 0<epsilon)
    (hlog : ((n:ℝ)+3)^2≤1/t)
    (hprofile : profileConstant/(t^44*h^11)≤delta^(-eta))
    (hcomparison : comparisonConstant≤t^386*h^206*delta^(-epsilon)) :
    originalAlphabetProfileCost n (1/t) (1/t) t (t^4/32) t N h M*(16/h)^u/
      originalRetention (t^3/16) N h M≤(h*delta/64)^(-eta) ∧
    (2*(1/t)/t)*(64/h^2)^u≤(h*delta/64)^(-eta) ∧
    4/h^2≤(h*delta/64)^(-eta) ∧
    (2:ℝ)^242*fiberBound h*(restrictedSumLoss h)^15*(12672/h^5)≤
      t*(originalDensity (t^3/16) N h M)^77*(h*delta/64)^(-epsilon) := by
  have hs : 0<h*delta/64 := by positivity
  have hsdelta : h*delta/64≤delta := by
    have hp := mul_le_mul_of_nonneg_right hh1 hd.le
    nlinarith only [hp,hd]
  have hbig := hprofile.trans (Real.rpow_le_rpow_of_nonpos hs hsdelta (by linarith only [heta]))
  have hsecondary := native_secondary_profile_envelope ht ht1 hh hh1
  refine ⟨(native_retained_profile_upper n ht ht1 hh hh1 hN hM hlog hu1).trans hbig,
    (native_coefficient_profile_upper ht hh hh1 hu1).trans (hsecondary.1.trans hbig),
    hsecondary.2.trans hbig,?_⟩
  apply le_of_not_gt
  intro hbad
  have hcontra := native_comparison_power ht hh hh1 hN hM
    (Real.rpow_nonneg hs.le (-epsilon)) hbad
  have hmono := Real.rpow_le_rpow_of_nonpos hs hsdelta (show -epsilon≤0 by linarith only [heps])
  have hright := mul_le_mul_of_nonneg_left hmono (show 0≤t^386*h^206 by positivity)
  exact (not_lt_of_ge (hcomparison.trans hright)) hcontra

end OriginalNativeNumericBudgets
