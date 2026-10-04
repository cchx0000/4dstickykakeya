import LeanFormalizations.Combinatorics.Additive.BalogSzemerediGowers
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped Pointwise

noncomputable section

namespace BalancedBSGIterationCore

def differenceConstant (eta : ℝ) : ℝ :=
  (((2 ^ 13 * (4 / eta) ^ 3 / (eta / 2) ^ 5 + 2 ^ 12 / (eta / 2) ^ 5) /
      (eta / 16)) ^ 3 / (eta / 16) + 1)

def growthConstant (eta : ℝ) : ℝ := (differenceConstant eta / (eta / 16)) ^ 2

theorem iterated_differences_of_small_difference
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (C : Finset G) (hC : C.Nonempty) (K : ℝ)
    (hsmall : ((C - C).card : ℝ) ≤ K * C.card) (m n : ℕ) :
    (((m • C) - (n • C)).card : ℝ) ≤ K ^ (m + n) * C.card := by
  have hpos : 0 < (C.card : ℝ) := by exact_mod_cast hC.card_pos
  have hPR : (((m • C) - (n • C)).card : ℚ≥0) ≤
      (((C - C).card : ℚ≥0) / (C.card : ℚ≥0)) ^ (m + n) * C.card :=
    Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub hC C m n
  have hReal : (((m • C) - (n • C)).card : ℝ) ≤
      (((C - C).card : ℝ) / (C.card : ℝ)) ^ (m + n) * C.card := by
    have hcast : (((m • C) - (n • C)).card : ℝ) ≤
        ((((C - C).card : ℚ≥0) / (C.card : ℚ≥0)) ^ (m + n) * C.card : ℚ≥0) := by
      exact_mod_cast hPR
    simpa using hcast
  have hratio : ((C - C).card : ℝ) / (C.card : ℝ) ≤ K :=
    (div_le_iff₀ hpos).2 hsmall
  have hratio0 : 0 ≤ ((C - C).card : ℝ) / (C.card : ℝ) := by positivity
  exact hReal.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hratio0 hratio (m + n)) (Nat.cast_nonneg _))

/-- A balanced BSG stage produces one actual small-difference core, with a
fully explicit polynomial loss, together with all iterated difference bounds.
It is suitable for the slow-growth stage of an asymmetric symmetry-set chain. -/
theorem balanced_energy_core
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (B : Finset G) (hB : B.Nonempty) (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (henergy : eta * (B.card : ℝ) ^ 3 ≤ (Finset.addEnergy B B : ℝ)) :
    ∃ C : Finset G, C ⊆ B ∧ C.Nonempty ∧
      (eta / 16) * (B.card : ℝ) ≤ C.card ∧
      ((C - C).card : ℝ) ≤ growthConstant eta * C.card ∧
      ∀ m n : ℕ, (((m • C) - (n • C)).card : ℝ) ≤
        (growthConstant eta) ^ (m + n) * C.card := by
  classical
  obtain ⟨C, D, hCB, _hDB, hCsize, hDsize, hdiff⟩ :=
    Finset.balog_szemeredi_gowers_asymmetric_explicit eta heta heta1 B B hB hB rfl henergy
  have hn : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hu : 0 < eta / 16 := by positivity
  have hCpos : 0 < (C.card : ℝ) := lt_of_lt_of_le (mul_pos hu hn) hCsize
  have hC : C.Nonempty := Finset.card_pos.mp (by exact_mod_cast hCpos)
  have hself0 : 0 ≤ ((C - C).card : ℝ) := Nat.cast_nonneg _
  have hdiff0 : 0 ≤ ((C - D).card : ℝ) := Nat.cast_nonneg _
  have hdiff' : ((C - D).card : ℝ) ≤ differenceConstant eta * B.card := hdiff
  have hRT : ((C - C).card : ℝ) * D.card ≤ ((C - D).card : ℝ) ^ 2 := by
    have hh := Finset.ruzsa_triangle_inequality_sub_sub_sub C D C
    have hh' : (C - C).card * D.card ≤ (C - D).card ^ 2 := by
      simpa only [pow_two] using hh
    exact_mod_cast hh' 
  have hfirst : ((C - C).card : ℝ) * (eta / 16) * B.card ≤
      (differenceConstant eta) ^ 2 * (B.card : ℝ) ^ 2 := by
    calc
      _ = ((C - C).card : ℝ) * ((eta / 16) * B.card) := by ring
      _ ≤ ((C - C).card : ℝ) * D.card := mul_le_mul_of_nonneg_left hDsize hself0
      _ ≤ ((C - D).card : ℝ) ^ 2 := hRT
      _ ≤ (differenceConstant eta * B.card) ^ 2 := pow_le_pow_left₀ hdiff0 hdiff' 2
      _ = _ := by ring
  have hnorm : ((C - C).card : ℝ) * (eta / 16) ≤
      (differenceConstant eta) ^ 2 * B.card := by
    apply (mul_le_mul_iff_left₀ hn).mp
    simpa only [pow_two, mul_assoc] using hfirst
  have hscaled : ((C - C).card : ℝ) * (eta / 16) ^ 2 ≤
      (differenceConstant eta) ^ 2 * C.card := by
    calc
      _ = (((C - C).card : ℝ) * (eta / 16)) * (eta / 16) := by ring
      _ ≤ ((differenceConstant eta) ^ 2 * B.card) * (eta / 16) :=
        mul_le_mul_of_nonneg_right hnorm hu.le
      _ = (differenceConstant eta) ^ 2 * ((eta / 16) * B.card) := by ring
      _ ≤ (differenceConstant eta) ^ 2 * C.card :=
        mul_le_mul_of_nonneg_left hCsize (sq_nonneg _)
  have hsmall : ((C - C).card : ℝ) ≤ growthConstant eta * C.card := by
    calc
      _ ≤ ((differenceConstant eta) ^ 2 * C.card) / (eta / 16) ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos hu)).2 hscaled
      _ = growthConstant eta * C.card := by
        unfold growthConstant
        field_simp
  exact ⟨C, hCB, hC, hCsize, hsmall,
    fun m n => iterated_differences_of_small_difference C hC _ hsmall m n⟩

end BalancedBSGIterationCore
