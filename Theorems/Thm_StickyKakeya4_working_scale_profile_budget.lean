import Theorems.Thm_StickyKakeya4_native_angular_chart_selection

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace WorkingScaleProfileBudget

open NativeDyadicTubeStopping NativeAngularChartSelection DyadicAlignmentParameters

lemma adjacent_gap_lower (M m k : ℕ) :
    M / m ≤ level M m (k + 1) - level M m k := by
  have h : (k * M) / m + M / m ≤ (k * M + M) / m := Nat.div_add_div_le_add_div
  have he : (k + 1) * M = k * M + M := by ring
  rw [← he] at h
  unfold level
  omega

lemma old_length_le_adjacent (M k : ℕ) {m : ℕ} (hm : 0 < m) :
    M ≤ m * (level M m (k + 1) - level M m k + 1) := by
  have hround := Nat.lt_mul_div_succ M hm
  have hgap := adjacent_gap_lower M m k
  have hmul := Nat.mul_le_mul_left m (Nat.add_le_add_right hgap 1)
  exact hround.le.trans hmul

lemma working_ratio {δ : ℝ} (hδ : 0 < δ) (lo M m k : ℕ) :
    scale δ (workingLevel lo M m (k + 1)) / scale δ (workingLevel lo M m k) =
      (2 : ℝ) ^ (level M m (k + 1) - level M m k) := by
  rw [scale_ratio hδ (workingLevel_mono lo M m (Nat.le_succ k))]
  simp only [workingLevel, Nat.add_sub_add_left]

lemma working_ratio_lower {δ : ℝ} (hδ : 0 < δ) (lo M m k : ℕ) :
    (2 : ℝ) ^ (M / m) ≤
      scale δ (workingLevel lo M m (k + 1)) / scale δ (workingLevel lo M m k) := by
  rw [working_ratio hδ]
  exact pow_le_pow_right₀ (by norm_num) (adjacent_gap_lower M m k)

/-- Every actual adjacent floor interval controls the OLD aspect ratio.
This is uniform in the angular selector's winning index. -/
theorem old_ratio_le_working_ratio {δ : ℝ} (hδ : 0 < δ) (lo M k : ℕ)
    {m : ℕ} (hm : 0 < m) :
    scale δ (lo + M) / scale δ lo ≤
      (2 : ℝ) ^ m *
        (scale δ (workingLevel lo M m (k + 1)) / scale δ (workingLevel lo M m k)) ^ m := by
  rw [scale_ratio hδ (show lo ≤ lo + M by omega), Nat.add_sub_cancel_left, working_ratio hδ]
  have hh := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (old_length_le_adjacent M k hm)
  have he : m * (level M m (k + 1) - level M m k + 1) =
      m + (level M m (k + 1) - level M m k) * m := by ring
  rw [he, pow_add, pow_mul] at hh
  exact hh

/-- The profile epsilon loss becomes m*epsilon in the selected adjacent
ratio. No detour through delta^(-epsilon) and no division by chi is made. -/
theorem old_profile_power_le {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (lo M k : ℕ) {m : ℕ} (hm : 0 < m) :
    (scale δ (lo + M) / scale δ lo) ^ ε ≤
      (2 : ℝ) ^ ((m : ℝ) * ε) *
        (scale δ (workingLevel lo M m (k + 1)) / scale δ (workingLevel lo M m k)) ^ ((m : ℝ) * ε) := by
  have hratio : 0 ≤ scale δ (workingLevel lo M m (k + 1)) / scale δ (workingLevel lo M m k) :=
    div_nonneg (scale_pos hδ _).le (scale_pos hδ _).le
  have hh := Real.rpow_le_rpow (div_nonneg (scale_pos hδ _).le (scale_pos hδ _).le)
    (old_ratio_le_working_ratio hδ lo M k hm) hε
  rw [Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ) ^ m) (pow_nonneg hratio m)] at hh
  have htwo : ((2 : ℝ) ^ m) ^ ε = (2 : ℝ) ^ ((m : ℝ) * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hnew : ((scale δ (workingLevel lo M m (k + 1)) / scale δ (workingLevel lo M m k)) ^ m) ^ ε =
      (scale δ (workingLevel lo M m (k + 1)) / scale δ (workingLevel lo M m k)) ^ ((m : ℝ) * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hratio]
  rwa [htwo, hnew] at hh

theorem stopped_loss_le_adjacent {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Plane) {δ ε K t : ℝ} {N : ℕ} {E : Finset α}
    (D : StoppedProfile p δ ε K t N E) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (k : ℕ) {m : ℕ} (hm : 0 < m) :
    D.loss ≤ 72 * adProfileConstant K t * (2 : ℝ) ^ ((m : ℝ) * ε) *
      (scale δ (workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (k + 1)) /
        scale δ (workingLevel D.pair.1 (D.pair.2 - D.pair.1) m k)) ^ ((m : ℝ) * ε) := by
  have hh := old_profile_power_le hδ hε D.pair.1 (D.pair.2 - D.pair.1) k hm
  rw [Nat.add_sub_of_le D.valid.1] at hh
  have hc : 0 ≤ 72 * adProfileConstant K t := by unfold adProfileConstant; positivity
  have h := mul_le_mul_of_nonneg_left hh hc
  simpa only [StoppedProfile.loss, mul_assoc] using h

end WorkingScaleProfileBudget
