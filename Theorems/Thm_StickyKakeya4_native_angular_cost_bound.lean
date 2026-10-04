import Theorems.Thm_StickyKakeya4_native_selected_parent_preparation
import Theorems.Thm_StickyKakeya4_working_scale_profile_budget

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

namespace NativeAngularCostBound

open NativeSelectedParentPreparation NativeAngularChartSelection DyadicAlignmentParameters WorkingScaleProfileBudget

noncomputable section

lemma gap_le_floor_add_one (M : ℕ) {m : ℕ} (hm : 0 < m) : gap M m ≤ M / m + 1 := by
  unfold gap
  apply Nat.ceil_le.mpr
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply (div_le_iff₀ hmR).mpr
  have hh := (Nat.lt_mul_div_succ M hm).le
  push_cast
  exact_mod_cast (by simpa only [Nat.mul_comm] using hh)

/-- The literal angular menu is smaller than the raw output grid extent
for EVERY adjacent working pair, before the winning pair is known. -/
lemma actual_angular_menu_le_extent (M k : ℕ) {m : ℕ} (hm : 0 < m) :
    2 * angularResolution M m + 1 ≤ 2 ^ (level M m (k + 1) - level M m k + 6) := by
  have hg : gap M m ≤ level M m (k + 1) - level M m k + 1 :=
    (gap_le_floor_add_one M hm).trans (Nat.add_le_add_right (adjacent_gap_lower M m k) 1)
  have hp : angularResolution M m ≤ 2 ^ (level M m (k + 1) - level M m k + 1) :=
    Nat.pow_le_pow_right (by omega) hg
  have hone : 1 ≤ 2 ^ (level M m (k + 1) - level M m k) := Nat.one_le_pow _ _ (by omega)
  rw [pow_add] at hp ⊢
  norm_num at hp ⊢
  omega

lemma angularBudget_le_root {n N m : ℕ} (hmenu : 2 * n + 1 ≤ N) :
    (angularBudget n m : ℝ) ≤ 2 * (N : ℝ) ^ (m : ℝ)⁻¹ := by
  have hnonneg : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hroot : (((2 * n + 1 : ℕ) : ℝ) ^ (m : ℝ)⁻¹) ≤ (N : ℝ) ^ (m : ℝ)⁻¹ :=
    Real.rpow_le_rpow hnonneg (by exact_mod_cast hmenu) (by positivity)
  have hone : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) ^ (m : ℝ)⁻¹ := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      (show (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) by exact_mod_cast (by omega : 1 ≤ 2 * n + 1))
      (by positivity : 0 ≤ (m : ℝ)⁻¹)
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hnonneg (m : ℝ)⁻¹)
  change (angularBudget n m : ℝ) < (((2 * n + 1 : ℕ) : ℝ) ^ (m : ℝ)⁻¹) + 1 at hceil
  linarith only [hroot, hone, hceil]

/-- The actual angular loss is at most twice N^(1/m), with N=64b/a.
No menu bound is supplied by the final caller. -/
lemma angularCost_le_extent_root (lo hi k : ℕ) {m : ℕ} (hm : 0 < m) :
    (angularCost lo hi m : ℝ) ≤
      2 * ((2 ^ (workingLevel lo (hi - lo) m (k + 1) - workingLevel lo (hi - lo) m k + 6) : ℕ) : ℝ) ^
        (m : ℝ)⁻¹ := by
  apply angularBudget_le_root
  simpa only [workingLevel, Nat.add_sub_add_left] using actual_angular_menu_le_extent (hi - lo) k hm

end
end NativeAngularCostBound
