import Theorems.Thm_StickyKakeya4_original_native_power_algebra
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
noncomputable section

namespace OriginalNativeCoverScaleBudget
open OriginalNativePowerAlgebra OriginalNativeProjectionBSGCore

lemma native_inverse_power {delta e : ℝ} (hd : 0<delta) :
    delta^(-e)=1/delta^e := by rw [Real.rpow_neg hd.le,one_div]

lemma native_cover_scale_pos {delta e N : ℝ} (hd : 0<delta) (hN : 0<N) :
    0<delta^(-e)*Real.sqrt N := mul_pos (Real.rpow_pos_of_pos hd _) (Real.sqrt_pos.mpr hN)

/-- The native square-root cover scale is normalized against the actual
original population N, which cancels exactly in the BSG density. -/
theorem native_cover_scale_square {delta e N : ℝ} (hd : 0<delta) (hN : 0≤N) :
    (delta^(-e)*Real.sqrt N)^2=N/(delta^e)^2 := by
  rw [mul_pow,Real.sq_sqrt hN,native_inverse_power hd]
  ring

/-- The original planar cardinality gap supplies the scalar alphabet
cardinality gap at the smaller ACTUAL mesh sigma=h*delta/64. -/
theorem native_cover_scale_cardinality {delta e N gap h : ℝ}
    (hd : 0<delta) (hd1 : delta≤1) (hh : 0<h) (hh1 : h≤1)
    (hgap : 0<gap) (hgap1 : gap≤1/4) (he : e≤gap/2)
    (hcard : N≤delta^(-2+4*gap)) :
    delta^(-e)*Real.sqrt N≤(h*delta/64)^(-1+gap) := by
  have hs := Real.sqrt_le_sqrt hcard
  have hid : Real.sqrt (delta^(-2+4*gap))=delta^(-1+2*gap) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hd.le]
    congr 1
    ring
  rw [hid] at hs
  have hm := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hd.le (-e))
  have hexp : -1+gap≤-e+(-1+2*gap) := by linarith only [he,hgap]
  have hpow := Real.rpow_le_rpow_of_exponent_ge hd hd1 hexp
  have hsmall : h*delta/64≤delta := by
    have hp := mul_le_mul_of_nonneg_right hh1 hd.le
    nlinarith only [hp,hd]
  have hsigma : 0<h*delta/64 := by positivity
  have hmesh := Real.rpow_le_rpow_of_nonpos hsigma hsmall
    (show -1+gap≤0 by linarith only [hgap1])
  rw [← Real.rpow_add hd] at hm
  exact hm.trans (hpow.trans hmesh)

lemma native_source_mass_identity {delta e u : ℝ} (hd : 0<delta) :
    delta^((20+64/u)*e)=(delta^e)^20*(delta^(8*e/u))^8 := by
  rw [← Real.rpow_mul_natCast hd.le e 20,← Real.rpow_mul_natCast hd.le (8*e/u) 8,
    ← Real.rpow_add hd]
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

/-- The actual retained BSG source meets the original admissibility
threshold once the explicit t^2 budget is paid. -/
theorem native_source_mass_admissible {t h N M : ℝ}
    (ht : 0<t) (hh : 0<h) (hh1 : h≤1) (hN : 0<N) (hM : M^2=N/t^2)
    (hsmall : t^2≤1/(2:ℝ)^52) :
    (t^20*h^8)*N≤originalRetention (t^3/16) N h M*M^2 := by
  have hret := (native_density_retention_lower ht hh hh1 hN hM).2
  have hden : 0<(2:ℝ)^52*t^2 := by positivity
  have hden1 : (2:ℝ)^52*t^2≤1 := by
    have hp := (le_div_iff₀ (by positivity : (0:ℝ)<2^52)).mp hsmall
    nlinarith only [hp]
  have hfirst : (t^20*h^8)*N≤((t^20*h^8)*N)/((2:ℝ)^52*t^2) := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_left hden1 (show 0≤(t^20*h^8)*N by positivity)
    simpa only [mul_one] using hm
  calc
    _ ≤ ((t^20*h^8)*N)/((2:ℝ)^52*t^2) := hfirst
    _ = (t^20*h^8/(2:ℝ)^52)*M^2 := by rw [hM]; ring
    _ ≤ originalRetention (t^3/16) N h M*M^2 :=
      mul_le_mul_of_nonneg_right hret (sq_nonneg M)

end OriginalNativeCoverScaleBudget
