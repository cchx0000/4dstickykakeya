import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
set_option warningAsError true

namespace CumulativeMassRounding
open scoped BigOperators
noncomputable section

def massPrefix (w : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, w i
def level (w : ℕ → ℝ) (M : ℝ) (n : ℕ) : ℤ := ⌊massPrefix w n / M⌋
def selected (w : ℕ → ℝ) (M : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun i => level w M i < level w M (i + 1))

lemma massPrefix_succ (w : ℕ → ℝ) (n : ℕ) :
    massPrefix w (n+1) = massPrefix w n + w n := by
  exact Finset.sum_range_succ w n

lemma level_step (w : ℕ → ℝ) {M : ℝ} (hM : 0 < M) (n : ℕ)
    (hw : 0 ≤ w n ∧ w n ≤ M) :
    level w M n ≤ level w M (n+1) ∧ level w M (n+1) ≤ level w M n + 1 := by
  have hid : massPrefix w (n+1) / M = massPrefix w n / M + w n / M := by
    rw [massPrefix_succ, add_div]
  have hfrac : 0 ≤ w n / M ∧ w n / M ≤ 1 :=
    ⟨div_nonneg hw.1 hM.le, (div_le_one hM).mpr hw.2⟩
  constructor
  · apply Int.floor_mono
    rw [hid]
    linarith
  · have h := Int.floor_mono (show massPrefix w (n+1) / M ≤ massPrefix w n / M + 1 by
      rw [hid]; linarith)
    simpa only [level, Int.floor_add_one] using h

lemma selected_subset (w : ℕ → ℝ) (M : ℝ) {a b : ℕ} (hab : a ≤ b) :
    selected w M a ⊆ selected w M b := by
  exact Finset.filter_subset_filter _ (Finset.range_mono hab)

lemma selected_positive_weight (w : ℕ → ℝ) {M : ℝ} (n i : ℕ)
    (hw : ∀ j < n, 0 ≤ w j) (hi : i ∈ selected w M n) : 0 < w i := by
  obtain ⟨hir, hinc⟩ := Finset.mem_filter.mp hi
  have hin : i < n := Finset.mem_range.mp hir
  by_contra hn
  have hz : w i = 0 := le_antisymm (le_of_not_gt hn) (hw i hin)
  have heq : level w M (i+1) = level w M i := by simp [level, massPrefix_succ, hz]
  omega

/-- The actual selected bins telescope, rather than being sampled independently. -/
theorem selected_card_eq_level (w : ℕ → ℝ) {M : ℝ} (hM : 0 < M) (n : ℕ)
    (hw : ∀ i < n, 0 ≤ w i ∧ w i ≤ M) :
    ((selected w M n).card : ℤ) = level w M n := by
  induction n with
  | zero =>
    have hz : selected w M 0 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact Nat.not_lt_zero i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
    rw [hz]
    simp [level, massPrefix]
  | succ n ih =>
    have ih' := ih (fun i hi => hw i (by omega))
    have hs := level_step w hM n (hw n (by omega))
    have hn : n ∉ selected w M n := by simp [selected]
    have hid : selected w M (n+1) =
        if level w M n < level w M (n+1) then insert n (selected w M n) else selected w M n := by
      simp only [selected, Finset.range_add_one, Finset.filter_insert]
    rw [hid]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem hn]
      push_cast
      omega
    · omega

/-- At most one unit of the reference capacity is lost in the global rounding. -/
theorem selected_mass_bounds (w : ℕ → ℝ) {M : ℝ} (hM : 0 < M) (n : ℕ)
    (hw : ∀ i < n, 0 ≤ w i ∧ w i ≤ M) :
    M * ((selected w M n).card : ℝ) ≤ massPrefix w n ∧
      massPrefix w n < M * ((selected w M n).card + 1) := by
  have heq : ((selected w M n).card : ℝ) = (level w M n : ℝ) := by
    exact_mod_cast selected_card_eq_level w hM n hw
  have hlo := Int.floor_le (massPrefix w n / M)
  have hup := Int.lt_floor_add_one (massPrefix w n / M)
  change (level w M n : ℝ) ≤ massPrefix w n / M at hlo
  change massPrefix w n / M < (level w M n : ℝ) + 1 at hup
  rw [← heq] at hlo hup
  constructor
  · have := (le_div_iff₀ hM).mp hlo
    nlinarith
  · have := (div_lt_iff₀ hM).mp hup
    nlinarith

def window (w : ℕ → ℝ) (M : ℝ) (a b : ℕ) : Finset ℕ :=
  selected w M b \ selected w M a

lemma mem_window (w : ℕ → ℝ) (M : ℝ) (a b i : ℕ) :
    i ∈ window w M a b ↔ a ≤ i ∧ i < b ∧ level w M i < level w M (i+1) := by
  simp only [window, selected, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
  omega

lemma massPrefix_sub (w : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    massPrefix w b - massPrefix w a = ∑ i ∈ Finset.Ico a b, w i := by
  have h := Finset.sum_range_add_sum_Ico w hab
  change massPrefix w a + _ = massPrefix w b at h
  linarith

lemma window_card (w : ℕ → ℝ) (M : ℝ) {a b : ℕ} (hab : a ≤ b) :
    (selected w M b).card = (selected w M a).card + (window w M a b).card := by
  have hs := selected_subset w M hab
  have hc := Finset.card_sdiff_of_subset hs
  change (selected w M b \ selected w M a).card = _ at hc
  have hl := Finset.card_le_card hs
  unfold window
  omega

/-- Every actual interval of bins keeps the original mass distribution up to
one reference-capacity unit. No normalization of individual bins occurs. -/
theorem window_mass_bounds (w : ℕ → ℝ) {M : ℝ} (hM : 0 < M) {a b : ℕ}
    (hab : a ≤ b) (hw : ∀ i < b, 0 ≤ w i ∧ w i ≤ M) :
    massPrefix w b - massPrefix w a - M ≤ M * ((window w M a b).card : ℝ) ∧
      M * ((window w M a b).card : ℝ) ≤ massPrefix w b - massPrefix w a + M := by
  have ha := selected_mass_bounds w hM a (fun i hi => hw i (lt_of_lt_of_le hi hab))
  have hb := selected_mass_bounds w hM b hw
  have hc : ((selected w M b).card : ℝ) =
      ((selected w M a).card : ℝ) + ((window w M a b).card : ℝ) := by
    exact_mod_cast window_card w M hab
  constructor <;> nlinarith

/-- A rich total population yields an actual nonempty selected set and a
factor-two global lower count, with no stochastic selection premise. -/
theorem rich_selected_count (w : ℕ → ℝ) {M : ℝ} (hM : 0 < M) (n : ℕ)
    (hw : ∀ i < n, 0 ≤ w i ∧ w i ≤ M) (hrich : 2 * M ≤ massPrefix w n) :
    (selected w M n).Nonempty ∧ massPrefix w n ≤ 2 * M * ((selected w M n).card : ℝ) := by
  have h := selected_mass_bounds w hM n hw
  have hpos : 0 < (selected w M n).card := by
    by_contra hn
    have hz : (selected w M n).card = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_add, mul_one] at h
    linarith
  refine ⟨Finset.card_pos.mp hpos, ?_⟩
  have hc : (1 : ℝ) ≤ (selected w M n).card := by exact_mod_cast hpos
  nlinarith
end
end CumulativeMassRounding
