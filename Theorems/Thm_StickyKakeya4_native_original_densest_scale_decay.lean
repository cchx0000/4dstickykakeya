import Theorems.Thm_StickyKakeya4_native_original_tube_family_caller
import Theorems.Thm_StickyKakeya4_native_quarter_scale_parameters

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

noncomputable section
namespace NativeOriginalDensestScaleDecay
open NativeQuarterScaleParameters

/-- The original densest-scale inequality forces a small physical width.
This also handles sigma=0, when the fine-scale inequality is impossible. -/
theorem original_densest_scale_decay (delta rho sigma a : ℝ)
    (hd : 0<delta) (hr : 0<rho) (hr1 : rho≤1) (hs1 : sigma≤1)
    (hscale : delta^(-a)*rho^sigma≤(2:ℝ)^sigma) :
    rho≤2*delta^a := by
  have hrpow : rho≤rho^sigma := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hr hr1 hs1
  have htwo : (2:ℝ)^sigma≤2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hs1
  have hprod : delta^a*delta^(-a)=1 := by
    rw [← Real.rpow_add hd,add_neg_cancel,Real.rpow_zero]
  have hh := mul_le_mul_of_nonneg_left hscale (Real.rpow_pos_of_pos hd a).le
  have he : delta^a*(delta^(-a)*rho^sigma)=rho^sigma := by rw [← mul_assoc,hprod,one_mul]
  rw [he] at hh
  have hu := mul_le_mul_of_nonneg_left htwo (Real.rpow_pos_of_pos hd a).le
  calc
    rho ≤ rho^sigma := hrpow
    _ ≤ delta^a*(2:ℝ)^sigma := hh
    _ ≤ delta^a*2 := hu
    _ = _ := by ring

/-- A source-independent positive cutoff makes the actual native scale
power-small and supplies a nonempty admissible interval for clipped widths. -/
theorem exists_original_densest_scale_cutoff (a : ℝ) (ha : 0<a) :
    ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧
      ∀ delta rho sigma : ℝ, 0<delta → delta≤delta0 →
        0<rho → rho≤1 → sigma≤1 → delta^(-a)*rho^sigma≤(2:ℝ)^sigma →
        rho≤delta^(a/2) ∧ 3*rho≤1/448 := by
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_small_power_cutoff
    (show 0<a/2 by positivity) (by norm_num : (0:ℝ)<1/1344)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta rho sigma hd hsmall hr hr1 hs1 hscale
  have hb := hcut delta hd hsmall
  have hp : 0<delta^(a/2) := Real.rpow_pos_of_pos hd _
  have he : delta^a=delta^(a/2)*delta^(a/2) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hfirst := original_densest_scale_decay delta rho sigma a hd hr hr1 hs1 hscale
  rw [he] at hfirst
  have hdecay : rho≤delta^(a/2) := by
    have hh := mul_le_mul_of_nonneg_right hb hp.le
    nlinarith only [hfirst,hh,hp]
  exact ⟨hdecay,by linarith only [hdecay,hb]⟩

end NativeOriginalDensestScaleDecay
