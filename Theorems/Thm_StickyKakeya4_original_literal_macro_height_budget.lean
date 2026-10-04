import Theorems.Thm_StickyKakeya4_original_literal_dense_macro_height
import Theorems.Thm_StickyKakeya4_original_literal_angular_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace OriginalLiteralMacroHeightBudget
/-- Every explicit coefficient in the actual macro-cell population theorem
fits a fixed power of the ORIGINAL source budget. No dimension or exponent
is used to select this numerical threshold. -/
theorem original_macro_cost_absorption {K L : ℝ}
    (hK : 79626240000 ≤ K) (hL : 0 ≤ L) (hLK : L ≤ K) :
    79626240000*K^4 ≤ K^5 ∧
      155520*K ≤ K^2 ∧
      124416000*K^5*(2*L+4)^2 ≤ K^8 := by
  have hK0 : 0 ≤ K := by linarith
  have hK1 : 1 ≤ K := by linarith
  refine ⟨?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hK (show 0 ≤ K^4 by positivity)
    nlinarith only [hh]
  · have hc : (155520:ℝ) ≤ K := by linarith
    have hh := mul_le_mul_of_nonneg_right hc hK0
    nlinarith only [hh]
  · have hs : (2*L+4)^2 ≤ (6*K)^2 := by
      apply pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hc : (4478976000:ℝ) ≤ K := by linarith
    have hb := mul_le_mul_of_nonneg_right hc (show 0 ≤ K^7 by positivity)
    calc
      _ ≤ 124416000*K^5*(6*K)^2 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 4478976000*K^7 := by ring
      _ ≤ K^8 := by nlinarith only [hb]
/-- The original eta and fixed slope oscillation constant select the cutoff
before the original sets, the grain exponent, or the actual macro-cell. -/
theorem exists_original_macro_power_cutoff {eta L : ℝ} (heta : 0 < eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ ∀ delta : ℝ,
      0 < delta → delta ≤ delta0 → 79626240000 ≤ delta^(-eta) ∧ L ≤ delta^(-eta) := by
  let M : ℝ := max 79626240000 L
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨d0,hd0,hd01,hcut⟩ := NativeQuarterScaleParameters.exists_small_power_cutoff heta (one_div_pos.mpr hM)
  refine ⟨d0,hd0,hd01,?_⟩
  intro delta hd hdd
  have hsmall := hcut delta hd hdd
  have hp : 0 < delta^eta := Real.rpow_pos_of_pos hd _
  have hlarge : M ≤ delta^(-eta) := by
    rw [Real.rpow_neg hd.le,inv_eq_one_div]
    apply (le_div_iff₀ hp).mpr
    have hh := (le_div_iff₀ hM).mp hsmall
    nlinarith only [hh]
  exact ⟨(le_max_left _ _).trans hlarge,(le_max_right _ _).trans hlarge⟩
end OriginalLiteralMacroHeightBudget
