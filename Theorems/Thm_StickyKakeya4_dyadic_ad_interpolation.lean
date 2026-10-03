import Theorems.Thm_StickyKakeya4_dyadic_alignment_parameters

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace DyadicADInterpolation
open DyadicAlignmentParameters

noncomputable def scalePower (s : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ (s * (n : ℝ))

lemma scalePower_nonneg (s : ℝ) (n : ℕ) : 0 ≤ scalePower s n :=
  Real.rpow_nonneg (by norm_num) _

lemma scalePower_mono (s : ℝ) (hs : 0 ≤ s) : Monotone (scalePower s) := by
  intro j k hjk
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hjk) hs)

lemma scalePower_add (s : ℝ) (j k : ℕ) :
    scalePower s (j + k) = scalePower s j * scalePower s k := by
  simp only [scalePower, Nat.cast_add, mul_add, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

/-- A simultaneous power profile on the finite working grid yields its literal
all-integer-scale extension. The losses are derived from the constructed
brackets, not supplied as an interpolation certificate. -/
theorem interpolate_working_profile (M H : ℕ) (hH : 0 < H)
    (f : ℕ → ℝ) (hf : Monotone f) (A B s : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hworking : ∀ j ≤ H,
      A * scalePower s (level M H j) ≤ f (level M H j) ∧
        f (level M H j) ≤ B * scalePower s (level M H j))
    (n : ℕ) (hn : n ≤ M) :
    A * scalePower s n ≤ scalePower s (gap M H) * f n ∧
      f n ≤ scalePower s (gap M H) * B * scalePower s n := by
  obtain ⟨j, hj, hlo, hhi, _hgap⟩ := exists_bracketing_levels M H n hH hn
  have hjle : j ≤ H := Nat.le_of_lt hj
  have hjnext : j + 1 ≤ H := by omega
  have hlow : A * scalePower s (level M H j) ≤ f n :=
    (hworking j hjle).1.trans (hf hlo)
  have hupp : f n ≤ B * scalePower s (level M H (j + 1)) :=
    (hf hhi).trans (hworking (j + 1) hjnext).2
  have hadj := adjacent_level_le M H j hH
  have hnlow : n ≤ level M H j + gap M H := hhi.trans hadj
  have huppn : level M H (j + 1) ≤ n + gap M H :=
    hadj.trans (Nat.add_le_add_right hlo _)
  constructor
  · calc
      A * scalePower s n ≤ A * scalePower s (level M H j + gap M H) :=
        mul_le_mul_of_nonneg_left (scalePower_mono s hs hnlow) hA
      _ = scalePower s (gap M H) * (A * scalePower s (level M H j)) := by
        rw [scalePower_add]
        ring
      _ ≤ scalePower s (gap M H) * f n :=
        mul_le_mul_of_nonneg_left hlow (scalePower_nonneg _ _)
  · calc
      f n ≤ B * scalePower s (level M H (j + 1)) := hupp
      _ ≤ B * scalePower s (n + gap M H) :=
        mul_le_mul_of_nonneg_left (scalePower_mono s hs huppn) hB
      _ = scalePower s (gap M H) * B * scalePower s n := by
        rw [scalePower_add]
        ring

/-- The all-scale loss is at most 2^s R^(s/H), with R=2^M. -/
theorem interpolation_factor_le (M H : ℕ) (hH : 0 < H) (s : ℝ) (hs : 0 ≤ s) :
    scalePower s (gap M H) ≤ (2 : ℝ) ^ s * ((2 : ℝ) ^ M) ^ (s / (H : ℝ)) := by
  have hid : scalePower s (gap M H) = ((2 : ℝ) ^ gap M H) ^ s := by
    rw [scalePower, ← Real.rpow_natCast 2 (gap M H),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hid]
  calc
    ((2 : ℝ) ^ gap M H) ^ s ≤ (2 * ((2 : ℝ) ^ M) ^ ((H : ℝ)⁻¹)) ^ s :=
      Real.rpow_le_rpow (by positivity) (dyadic_gap_factor_le M H hH) hs
    _ = (2 : ℝ) ^ s * ((2 : ℝ) ^ M) ^ (s / (H : ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ M)]
      congr 2
      ring

end DyadicADInterpolation
