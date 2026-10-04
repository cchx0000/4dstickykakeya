import Theorems.Thm_StickyKakeya4_native_quarter_scale_parameters

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace NativeOriginalShadingWidthCutoff
open NativeQuarterScaleParameters

/-- A genuine positive cutoff supplies the original wide-tube width
needed by every actual shading-center partner witness. -/
theorem exists_native_shading_width_cutoff (t eta : ℝ) (ht : 0<t) (heta : 0<eta) :
    ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧
      ∀ delta : ℝ, 0<delta → delta≤delta0 →
        24≤(delta^(2*eta/t))^(-3:ℝ) := by
  have ha : 0<6*eta/t := div_pos (by positivity) ht
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_small_power_cutoff ha
    (by norm_num : (0:ℝ)<1/24)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall
  have hh := hcut delta hd hsmall
  have hpow : (delta^(2*eta/t))^(-3:ℝ)=(delta^(6*eta/t))⁻¹ := by
    rw [← Real.rpow_mul hd.le,show (2*eta/t)*(-3)= -(6*eta/t) by ring,Real.rpow_neg hd.le]
  rw [hpow]
  have hp : 0<delta^(6*eta/t) := Real.rpow_pos_of_pos hd _
  rw [← one_div]
  apply (le_div_iff₀ hp).mpr
  nlinarith only [hh]

end NativeOriginalShadingWidthCutoff
