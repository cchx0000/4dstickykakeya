import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

noncomputable section

namespace NativeHaloCountTransfer

/-- Finite double counting with real row and column bounds.  No geometric
assumptions enter this lemma; applications supply the actual relation. -/
theorem relation_card_mul_le {α β : Type*}
    (A : Finset α) (B : Finset β) (R : α → β → Prop) [DecidableRel R]
    {K C : ℝ}
    (hrow : ∀ a ∈ A, K ≤ ((B.filter (R a)).card : ℝ))
    (hcolumn : ∀ b ∈ B, ((A.filter (fun a => R a b)).card : ℝ) ≤ C) :
    K * (A.card : ℝ) ≤ C * (B.card : ℝ) := by
  simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow,
    nsmul_eq_mul, mul_comm] using
    (Finset.card_nsmul_le_card_nsmul (r := R) (s := A) (t := B) hrow hcolumn)

/-- Actual finite rows and menus imply the cardinality comparison when each
incidence places its row label in the corresponding menu. -/
theorem rows_card_mul_le_of_menu {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (row : α → Finset β) (menu : β → Finset α)
    {K C : ℝ}
    (hrow_subset : ∀ a ∈ A, row a ⊆ B)
    (hrow_lower : ∀ a ∈ A, K ≤ ((row a).card : ℝ))
    (hmenu_contains : ∀ a ∈ A, ∀ b ∈ row a, a ∈ menu b)
    (hmenu_upper : ∀ b ∈ B, ((menu b).card : ℝ) ≤ C) :
    K * (A.card : ℝ) ≤ C * (B.card : ℝ) := by
  apply relation_card_mul_le A B (fun a b => b ∈ row a)
  · intro a ha
    have heq : B.filter (fun b => b ∈ row a) = row a := by
      ext b
      simp only [Finset.mem_filter]
      exact ⟨fun hb => hb.2, fun hb => ⟨hrow_subset a ha hb, hb⟩⟩
    simpa only [heq] using hrow_lower a ha
  · intro b hb
    have hsubset : A.filter (fun a => b ∈ row a) ⊆ menu b := by
      intro a ha
      exact hmenu_contains a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp ha).2
    exact (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans (hmenu_upper b hb)

/-- Comparing both incidence and point counts at the same positive scale
transfers their ratios.  The scale is explicitly cancelled, and positivity
of the overlap constant follows from the incidence upper bound. -/
theorem multiplicity_transfer {IA PA IB PB T eps C : ℝ}
    (hIA : 0 < IA) (hPA : 0 < PA) (hIB : 0 < IB) (hPB : 0 < PB)
    (hT : 0 < T) (heps : 0 < eps)
    (hinc_lower : eps * T * IA ≤ C * IB)
    (hinc_upper : IB ≤ C * T * IA)
    (hpoint_lower : eps * T * PA ≤ C * PB)
    (hpoint_upper : PB ≤ C * T * PA) :
    (eps / C ^ 2) * (IB / PB) ≤ IA / PA ∧
      IA / PA ≤ (C ^ 2 / eps) * (IB / PB) := by
  have hC : 0 < C := by
    apply (mul_pos_iff_of_pos_right (mul_pos hT hIA)).mp
    simpa only [mul_assoc] using lt_of_lt_of_le hIB hinc_upper
  have hlower_scaled : (eps * T * PA) * IB ≤ (C * PB) * (C * T * IA) := by
    calc
      _ ≤ (C * PB) * IB := mul_le_mul_of_nonneg_right hpoint_lower (le_of_lt hIB)
      _ ≤ _ := mul_le_mul_of_nonneg_left hinc_upper (by positivity)
  have hupper_scaled : (eps * T * IA) * PB ≤ (C * IB) * (C * T * PA) := by
    calc
      _ ≤ (C * IB) * PB := mul_le_mul_of_nonneg_right hinc_lower (le_of_lt hPB)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpoint_upper (by positivity)
  have hlower : eps * IB * PA ≤ C ^ 2 * IA * PB := by
    apply (mul_le_mul_iff_left₀ hT).mp
    nlinarith only [hlower_scaled]
  have hupper : eps * IA * PB ≤ C ^ 2 * IB * PA := by
    apply (mul_le_mul_iff_left₀ hT).mp
    nlinarith only [hupper_scaled]
  constructor
  · rw [div_mul_div_comm, div_le_div_iff₀ (by positivity : 0 < C ^ 2 * PB) hPA]
    nlinarith only [hlower]
  · rw [div_mul_div_comm, div_le_div_iff₀ hPA (mul_pos heps hPB)]
    nlinarith only [hupper]

end NativeHaloCountTransfer
