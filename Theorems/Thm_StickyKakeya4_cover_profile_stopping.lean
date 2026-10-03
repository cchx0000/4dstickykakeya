import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace CoverProfileStopping

abbrev ScalePair := ℕ × ℕ

def Valid (N : ℕ) (p : ScalePair) : Prop := p.1 ≤ p.2 ∧ p.2 ≤ N

def Nested (q p : ScalePair) : Prop := p.1 ≤ q.1 ∧ q.2 ≤ p.2 ∧ q.1 ≤ q.2

def length (p : ScalePair) : ℝ := (p.2 - p.1 : ℕ)

lemma length_nonneg (p : ScalePair) : 0 ≤ length p := Nat.cast_nonneg _

lemma nested_valid {N : ℕ} {p q : ScalePair} (hp : Valid N p) (hq : Nested q p) :
    Valid N q := ⟨hq.2.2, hq.2.1.trans hp.2⟩

lemma nested_length_le {p q : ScalePair} (hq : Nested q p) : length q ≤ length p := by
  unfold length
  have hn : q.2 - q.1 ≤ p.2 - p.1 := by
    rcases hq with ⟨h₁, h₂, h₃⟩
    omega
  exact_mod_cast hn

lemma power_length_lower {ε c L : ℝ} {B k : ℕ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hc : 0 ≤ c) (hL : 0 < L)
    (hlarge : 4 * c < ε ^ B * L) (hk : k ≤ B) :
    0 < ε ^ k * L - 2 * c ∧
      ε ^ B * L / 2 ≤ ε ^ k * L - 2 * c ∧
      c < ε ^ k * L - 2 * c := by
  have hp : ε ^ B ≤ ε ^ k := pow_le_pow_of_le_one hε.le hεone hk
  have hpL := mul_le_mul_of_nonneg_right hp hL.le
  constructor
  · linarith
  constructor <;> linarith

lemma length_recurrence {ε c L ell ell' : ℝ} {k : ℕ}
    (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) (hc : 0 ≤ c)
    (hbound : ε ^ k * L - 2 * c ≤ ell)
    (hnext : ε * ell - c ≤ ell') :
    ε ^ (k + 1) * L - 2 * c ≤ ell' := by
  have hmul := mul_le_mul_of_nonneg_left hbound hε
  have hec : 2 * ε * c ≤ c := by nlinarith
  rw [pow_succ]
  nlinarith

/-- A positive improving child raises the score by at least ε. -/
lemma improving_score {ε ell ell' mass mass' : ℝ}
    (hε : 0 ≤ ε) (hell' : 0 < ell') (hle : ell' ≤ ell)
    (hbad : ε * ell + (mass / ell) * ell' ≤ mass') :
    mass / ell + ε ≤ mass' / ell' := by
  apply (le_div_iff₀ hell').mpr
  have := mul_le_mul_of_nonneg_left hle hε
  nlinarith

/-- Concrete nested intervals: repeatedly choose a violating subinterval.
A finite slope budget forces stopping; the length recurrence preserves an
explicit positive fraction ε^B/2 of the initial logarithmic scale range. -/
theorem exists_log_profile_stopping
    (N B : ℕ) (ε c : ℝ) (H : ScalePair → ℝ)
    (hN : 0 < N) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hc : 0 ≤ c)
    (hB : 2 ≤ (B : ℝ) * ε)
    (hlarge : 4 * c < ε ^ B * (N : ℝ))
    (hH : ∀ p, Valid N p → 0 ≤ H p ∧ H p ≤ c + length p) :
    ∃ p : ScalePair, Valid N p ∧ 0 < length p ∧
      ε ^ B * (N : ℝ) / 2 ≤ length p ∧
      0 ≤ H p / length p ∧ H p / length p < 2 ∧
      ∀ q, Nested q p → H q < ε * length p + (H p / length p) * length q := by
  classical
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hεone : ε ≤ 1 := by linarith
  have walk : ∀ fuel k : ℕ, k + fuel = B → ∀ p : ScalePair,
      Valid N p → ε ^ k * (N : ℝ) - 2 * c ≤ length p →
      (k : ℝ) * ε ≤ H p / length p →
      ∃ q : ScalePair, Valid N q ∧ 0 < length q ∧
        ε ^ B * (N : ℝ) / 2 ≤ length q ∧
        0 ≤ H q / length q ∧ H q / length q < 2 ∧
        ∀ r, Nested r q → H r < ε * length q + (H q / length q) * length r := by
    intro fuel
    induction fuel with
    | zero =>
      intro k hsum p hp hlen hscore
      have hk : k = B := by omega
      have hlower := power_length_lower hε hεone hc hNreal hlarge (show k ≤ B by omega)
      have hell : 0 < length p := lt_of_lt_of_le hlower.1 hlen
      have hcL : c < length p := lt_of_lt_of_le hlower.2.2 hlen
      have hupper : H p / length p < 2 := by
        apply (div_lt_iff₀ hell).mpr
        have := (hH p hp).2
        linarith
      rw [hk] at hscore
      linarith
    | succ fuel ih =>
      intro k hsum p hp hlen hscore
      have hk : k ≤ B := by omega
      have hlower := power_length_lower hε hεone hc hNreal hlarge hk
      have hell : 0 < length p := lt_of_lt_of_le hlower.1 hlen
      have hcL : c < length p := lt_of_lt_of_le hlower.2.2 hlen
      have hnonneg : 0 ≤ H p / length p := div_nonneg (hH p hp).1 hell.le
      have hupper : H p / length p < 2 := by
        apply (div_lt_iff₀ hell).mpr
        have := (hH p hp).2
        linarith
      by_cases hstop : ∀ q, Nested q p → H q < ε * length p + (H p / length p) * length q
      · exact ⟨p, hp, hell, hlower.2.1.trans hlen, hnonneg, hupper, hstop⟩
      · have hbad : ∃ q, Nested q p ∧ ε * length p + (H p / length p) * length q ≤ H q := by
          by_contra hnone
          apply hstop
          intro q hq
          by_contra hn
          exact hnone ⟨q, hq, le_of_not_gt hn⟩
        obtain ⟨q, hq, hbadq⟩ := hbad
        have hqvalid := nested_valid hp hq
        have hterm : 0 ≤ (H p / length p) * length q := mul_nonneg hnonneg (length_nonneg q)
        have hnext : ε * length p - c ≤ length q := by
          have := (hH q hqvalid).2
          linarith
        have hlenq := length_recurrence hε.le hεhalf hc hlen hnext
        have hk' : k + 1 ≤ B := by omega
        have hlowerq := power_length_lower hε hεone hc hNreal hlarge hk'
        have hqpos : 0 < length q := lt_of_lt_of_le hlowerq.1 hlenq
        have hscoreq : ((k + 1 : ℕ) : ℝ) * ε ≤ H q / length q := by
          have himprove := improving_score hε.le hqpos (nested_length_le hq) hbadq
          push_cast
          nlinarith
        exact ih (k + 1) (by omega) q hqvalid hlenq hscoreq
  apply walk B 0 (by omega) (0, N)
  · exact ⟨Nat.zero_le N, le_rfl⟩
  · simp only [pow_zero, one_mul, length, Nat.sub_zero]
    linarith
  · simp only [Nat.cast_zero, zero_mul, length, Nat.sub_zero]
    exact div_nonneg (hH (0, N) ⟨Nat.zero_le N, le_rfl⟩).1 hNreal.le

def dyadicRatio (p : ScalePair) : ℝ := (2 : ℝ) ^ (p.2 - p.1)

noncomputable def logCount (M : ScalePair → ℕ) (p : ScalePair) : ℝ :=
  Real.log (M p : ℝ) / Real.log 2

noncomputable def slope (M : ScalePair → ℕ) (p : ScalePair) : ℝ :=
  logCount M p / length p

lemma log_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)

lemma logCount_bounds (M : ScalePair → ℕ) (C : ℝ) (p : ScalePair)
    (hC : 1 ≤ C) (hpositive : 0 < M p)
    (hupper : (M p : ℝ) ≤ C * dyadicRatio p) :
    0 ≤ logCount M p ∧ logCount M p ≤ Real.log C / Real.log 2 + length p := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hMpos : 0 < (M p : ℝ) := by exact_mod_cast hpositive
  have hMone : (1 : ℝ) ≤ (M p : ℝ) := by exact_mod_cast hpositive
  have hRpos : 0 < dyadicRatio p := pow_pos (by norm_num) _
  constructor
  · exact div_nonneg (Real.log_nonneg hMone) log_two_pos.le
  · have hlog := Real.log_le_log hMpos hupper
    rw [Real.log_mul hCpos.ne' hRpos.ne', dyadicRatio, Real.log_pow] at hlog
    apply (div_le_iff₀ log_two_pos).mpr
    have hcancel : (Real.log C / Real.log 2) * Real.log 2 = Real.log C :=
      div_mul_cancel₀ _ log_two_pos.ne'
    dsimp [length]
    nlinarith

lemma slope_eq_log_ratio (M : ScalePair → ℕ) (p : ScalePair) :
    slope M p = Real.log (M p : ℝ) / Real.log (dyadicRatio p) := by
  unfold slope logCount length dyadicRatio
  rw [Real.log_pow, div_div, mul_comm (Real.log 2)]

lemma dyadicRatio_rpow (p : ScalePair) (a : ℝ) :
    (dyadicRatio p) ^ a = (2 : ℝ) ^ (a * length p) := by
  unfold dyadicRatio length
  rw [← Real.rpow_natCast (2 : ℝ) (p.2 - p.1), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [mul_comm]

lemma dyadicRatio_rpow_product (p q : ScalePair) (a b : ℝ) :
    (dyadicRatio p) ^ a * (dyadicRatio q) ^ b =
      (2 : ℝ) ^ (a * length p + b * length q) := by
  rw [dyadicRatio_rpow, dyadicRatio_rpow, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

/-- Constructive stopping for actual positive integer cover counts on all finite
dyadic scale pairs. The selected upper profile and power separation are outputs.
Only the elementary tube-cover bound C·2^(hi-lo) is assumed. -/
theorem exists_dyadic_cover_profile
    (N B : ℕ) (ε C : ℝ) (M : ScalePair → ℕ)
    (hN : 0 < N) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hC : 1 ≤ C)
    (hB : 2 ≤ (B : ℝ) * ε)
    (hlarge : 4 * (Real.log C / Real.log 2) < ε ^ B * (N : ℝ))
    (hM : ∀ p, Valid N p → 0 < M p ∧ (M p : ℝ) ≤ C * dyadicRatio p) :
    ∃ p : ScalePair, Valid N p ∧ 0 < length p ∧
      ε ^ B * (N : ℝ) / 2 ≤ length p ∧
      ((2 : ℝ) ^ N) ^ (ε ^ B / 2) ≤ dyadicRatio p ∧
      0 ≤ slope M p ∧ slope M p < 2 ∧
      ∀ q, Nested q p →
        (M q : ℝ) < (dyadicRatio p) ^ ε * (dyadicRatio q) ^ (slope M p) := by
  have hc : 0 ≤ Real.log C / Real.log 2 := div_nonneg (Real.log_nonneg hC) log_two_pos.le
  obtain ⟨p, hp, hlenpos, hlen, hspos, hsbound, hstop⟩ :=
    exists_log_profile_stopping N B ε (Real.log C / Real.log 2) (logCount M)
      hN hε hεhalf hc hB hlarge (fun p hp =>
        logCount_bounds M C p hC (hM p hp).1 (hM p hp).2)
  refine ⟨p, hp, hlenpos, hlen, ?_, hspos, hsbound, ?_⟩
  · calc
      ((2 : ℝ) ^ N) ^ (ε ^ B / 2) = (2 : ℝ) ^ (ε ^ B * (N : ℝ) / 2) := by
        rw [← Real.rpow_natCast (2 : ℝ) N, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      _ ≤ (2 : ℝ) ^ length p := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlen
      _ = dyadicRatio p := by simp [dyadicRatio, length]
  · intro q hq
    rw [dyadicRatio_rpow_product]
    apply Real.lt_rpow_of_log_lt (by norm_num : (0 : ℝ) < 2)
    exact (div_lt_iff₀ log_two_pos).mp (hstop q hq)

/-- The number of ε-improvements needed to force score at least two. -/
noncomputable def stepBudget (ε : ℝ) : ℕ := ⌈2 / ε⌉₊

/-- Explicit positive separation exponent in the dyadic stopping theorem. -/
noncomputable def separationExponent (ε : ℝ) : ℝ := ε ^ stepBudget ε / 2

lemma stepBudget_mul (ε : ℝ) (hε : 0 < ε) : 2 ≤ (stepBudget ε : ℝ) * ε := by
  exact (div_le_iff₀ hε).mp (Nat.le_ceil (2 / ε))

lemma separationExponent_pos (ε : ℝ) (hε : 0 < ε) : 0 < separationExponent ε := by
  unfold separationExponent
  positivity

/-- The canonical choice B=ceil(2/ε), with no chosen-profile certificate among
the assumptions. For sufficiently large initial dyadic range N, this returns
both the common nested upper profile and positive power separation. -/
theorem exists_dyadic_cover_profile_canonical
    (N : ℕ) (ε C : ℝ) (M : ScalePair → ℕ)
    (hN : 0 < N) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hC : 1 ≤ C)
    (hlarge : 4 * (Real.log C / Real.log 2) < ε ^ stepBudget ε * (N : ℝ))
    (hM : ∀ p, Valid N p → 0 < M p ∧ (M p : ℝ) ≤ C * dyadicRatio p) :
    ∃ p : ScalePair, Valid N p ∧ 0 < length p ∧
      separationExponent ε * (N : ℝ) ≤ length p ∧
      ((2 : ℝ) ^ N) ^ separationExponent ε ≤ dyadicRatio p ∧
      0 ≤ slope M p ∧ slope M p < 2 ∧
      ∀ q, Nested q p →
        (M q : ℝ) < (dyadicRatio p) ^ ε * (dyadicRatio q) ^ (slope M p) := by
  obtain ⟨p, hp, hpos, hlen, hratio, hspos, hsbound, hstop⟩ :=
    exists_dyadic_cover_profile N (stepBudget ε) ε C M hN hε hεhalf hC
      (stepBudget_mul ε hε) hlarge hM
  refine ⟨p, hp, hpos, ?_, hratio, hspos, hsbound, hstop⟩
  dsimp [separationExponent]
  nlinarith

end CoverProfileStopping
