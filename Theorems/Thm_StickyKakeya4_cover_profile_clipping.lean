import Theorems.Thm_StickyKakeya4_cover_profile_stopping

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace CoverProfileClipping

open CoverProfileStopping

def clippedSlope (s t : ℝ) : ℝ := min s (min t 1)

lemma clippedSlope_bounds {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ clippedSlope s t ∧ clippedSlope s t ≤ min t 1 ∧ clippedSlope s t ≤ s := by
  exact ⟨le_min hs (le_min ht zero_le_one), min_le_right _ _, min_le_left _ _⟩

/-- The exponent is clipped with the AD and tube-cover slack retained explicitly. -/
lemma clipped_power_bounds {R s t C D : ℝ}
    (hR : 1 ≤ R) (hC : 1 ≤ C) (hD : 1 ≤ D)
    (ht : R ^ s ≤ D * R ^ t) (hline : R ^ s ≤ C * R) :
    R ^ clippedSlope s t ≤ R ^ s ∧ R ^ s ≤ (C * D) * R ^ clippedSlope s t := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hCnonneg : 0 ≤ C := zero_le_one.trans hC
  have hDnonneg : 0 ≤ D := zero_le_one.trans hD
  have hCD : 1 ≤ C * D := by nlinarith
  refine ⟨Real.rpow_le_rpow_of_exponent_le hR (min_le_left _ _), ?_⟩
  rcases min_choice s (min t 1) with hs | hinner
  · have hclip : clippedSlope s t = s := hs
    rw [hclip]
    have := mul_le_mul_of_nonneg_right hCD (Real.rpow_pos_of_pos hRpos s).le
    simpa using this
  · rcases min_choice t 1 with htmin | h1min
    · have hclip : clippedSlope s t = t := hinner.trans htmin
      rw [hclip]
      have hp : 0 ≤ D * R ^ t := mul_nonneg hDnonneg (Real.rpow_pos_of_pos hRpos t).le
      have hmul := mul_le_mul_of_nonneg_right hC hp
      nlinarith
    · have hclip : clippedSlope s t = 1 := hinner.trans h1min
      rw [hclip, Real.rpow_one]
      have hp : 0 ≤ C * R := mul_nonneg hCnonneg hRpos.le
      have hmul := mul_le_mul_of_nonneg_right hD hp
      nlinarith

/-- A multiplicative exponent loss controlled at the largest ratio controls
the same loss at every smaller admissible ratio. -/
lemma transport_nested_exponent {R r s u L : ℝ}
    (hR : 1 ≤ R) (hr : 1 ≤ r) (hrR : r ≤ R) (hu : u ≤ s)
    (hlarge : R ^ s ≤ L * R ^ u) : r ^ s ≤ L * r ^ u := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hpowpos := Real.rpow_pos_of_pos hRpos u
  have hdiff : R ^ (s - u) ≤ L := by
    rw [Real.rpow_sub hRpos]
    exact (div_le_iff₀ hpowpos).mpr hlarge
  have hsmall : r ^ (s - u) ≤ L :=
    (Real.rpow_le_rpow hrpos.le hrR (sub_nonneg.mpr hu)).trans hdiff
  calc
    r ^ s = r ^ u * r ^ (s - u) := by
      rw [← Real.rpow_add hrpos]
      congr 1
      ring
    _ ≤ r ^ u * L := mul_le_mul_of_nonneg_left hsmall (Real.rpow_pos_of_pos hrpos u).le
    _ = L * r ^ u := mul_comm _ _

lemma clipped_nested_profile {R r s t C D ε m : ℝ}
    (hR : 1 ≤ R) (hr : 1 ≤ r) (hrR : r ≤ R)
    (hC : 1 ≤ C) (hD : 1 ≤ D)
    (ht : R ^ s ≤ D * R ^ t) (hline : R ^ s ≤ C * R)
    (hprofile : m < R ^ ε * r ^ s) :
    m < (C * D) * R ^ ε * r ^ clippedSlope s t := by
  have hclip := (clipped_power_bounds hR hC hD ht hline).2
  have hsmall := transport_nested_exponent hR hr hrR (min_le_left s (min t 1)) hclip
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  change r ^ s ≤ (C * D) * r ^ clippedSlope s t at hsmall
  have hmul := mul_le_mul_of_nonneg_left hsmall (Real.rpow_pos_of_pos hRpos ε).le
  calc
    m < R ^ ε * r ^ s := hprofile
    _ ≤ R ^ ε * ((C * D) * r ^ clippedSlope s t) := hmul
    _ = (C * D) * R ^ ε * r ^ clippedSlope s t := by ring

lemma dyadicRatio_ge_one (p : ScalePair) : 1 ≤ dyadicRatio p := by
  unfold dyadicRatio
  exact one_le_pow₀ (by norm_num)

lemma nested_ratio_le {p q : ScalePair} (hq : Nested q p) : dyadicRatio q ≤ dyadicRatio p := by
  change (2 : ℝ) ^ (q.2 - q.1) ≤ (2 : ℝ) ^ (p.2 - p.1)
  have hn : q.2 - q.1 ≤ p.2 - p.1 := by
    rcases hq with ⟨h₁, h₂, h₃⟩
    omega
  exact pow_le_pow_right₀ (by norm_num) hn

lemma profile_power_eq (M : ScalePair → ℕ) (p : ScalePair)
    (hM : 0 < M p) (hlen : 0 < length p) :
    (dyadicRatio p) ^ slope M p = (M p : ℝ) := by
  have hRpos : 0 < dyadicRatio p := lt_of_lt_of_le zero_lt_one (dyadicRatio_ge_one p)
  have hMpos : 0 < (M p : ℝ) := by exact_mod_cast hM
  have hlog : 0 < Real.log (dyadicRatio p) := by
    rw [dyadicRatio, Real.log_pow]
    exact mul_pos hlen log_two_pos
  apply (Real.mul_log_eq_log_iff hRpos hMpos).mp
  rw [slope_eq_log_ratio, div_mul_cancel₀ _ hlog.ne']

/-- Applying the actual stopping construction and then clipping its slope.
The only extra hypothesis is the genuine AD upper count with constant D. -/
theorem exists_clipped_dyadic_cover_profile
    (N : ℕ) (ε C D t : ℝ) (M : ScalePair → ℕ)
    (hN : 0 < N) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hC : 1 ≤ C) (hD : 1 ≤ D) (htnonneg : 0 ≤ t)
    (hlarge : 4 * (Real.log C / Real.log 2) < ε ^ stepBudget ε * (N : ℝ))
    (hM : ∀ p, Valid N p → 0 < M p ∧ (M p : ℝ) ≤ C * dyadicRatio p)
    (hAD : ∀ p, Valid N p → (M p : ℝ) ≤ D * (dyadicRatio p) ^ t) :
    ∃ p : ScalePair, Valid N p ∧ 0 < length p ∧
      ((2 : ℝ) ^ N) ^ separationExponent ε ≤ dyadicRatio p ∧
      0 ≤ clippedSlope (slope M p) t ∧ clippedSlope (slope M p) t ≤ min t 1 ∧
      (dyadicRatio p) ^ clippedSlope (slope M p) t ≤ (M p : ℝ) ∧
      (M p : ℝ) ≤ (C * D) * (dyadicRatio p) ^ clippedSlope (slope M p) t ∧
      ∀ q, Nested q p → (M q : ℝ) <
        (C * D) * (dyadicRatio p) ^ ε * (dyadicRatio q) ^ clippedSlope (slope M p) t := by
  obtain ⟨p, hp, hlen, _, hsep, hs, _, hprofile⟩ :=
    exists_dyadic_cover_profile_canonical N ε C M hN hε hεhalf hC hlarge hM
  have hpower := profile_power_eq M p (hM p hp).1 hlen
  have hADp : (dyadicRatio p) ^ slope M p ≤ D * (dyadicRatio p) ^ t := by
    rw [hpower]
    exact hAD p hp
  have hline : (dyadicRatio p) ^ slope M p ≤ C * dyadicRatio p := by
    rw [hpower]
    exact (hM p hp).2
  have hclipped := clipped_power_bounds (dyadicRatio_ge_one p) hC hD hADp hline
  have hinterval := clippedSlope_bounds hs htnonneg
  refine ⟨p, hp, hlen, hsep, hinterval.1, hinterval.2.1, ?_, ?_, ?_⟩
  · simpa only [hpower] using hclipped.1
  · simpa only [hpower] using hclipped.2
  · intro q hq
    exact clipped_nested_profile (dyadicRatio_ge_one p) (dyadicRatio_ge_one q)
      (nested_ratio_le hq) hC hD hADp hline (hprofile q hq)

end CoverProfileClipping
