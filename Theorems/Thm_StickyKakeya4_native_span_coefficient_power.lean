import Theorems.Thm_StickyKakeya4_native_separated_span_control

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace NativeSpanCoefficientPower
open NativeSeparatedSpanControl

/-- The inverse-frame cost derived from actual successive separation is
polynomial, with the dimension in the exponent. -/
theorem coefficientCost_le_power {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (n : ℕ) :
    coefficientCost 2 q n ≤ (4/q)^n := by
  have hR : (1:ℝ) ≤ 4/q := (le_div_iff₀ hq).mpr (by linarith)
  have hp : 0 ≤ 1+2/q := by positivity
  have hs : 1/q+(1+2/q) ≤ 4/q := by
    apply (le_div_iff₀ hq).mpr
    have h1 := div_mul_cancel₀ (1:ℝ) hq.ne'
    have h2 := div_mul_cancel₀ (2:ℝ) hq.ne'
    nlinarith
  induction n with
  | zero => simp [coefficientCost]
  | succ n ih =>
    have hn : (1:ℝ) ≤ (4/q)^n := one_le_pow₀ hR
    calc
      coefficientCost 2 q (n+1) = 1/q+(1+2/q)*coefficientCost 2 q n := rfl
      _ ≤ 1/q+(1+2/q)*(4/q)^n := add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hp)
      _ ≤ (1/q)*(4/q)^n+(1+2/q)*(4/q)^n :=
        add_le_add (le_mul_of_one_le_right (by positivity) hn) le_rfl
      _ = (1/q+(1+2/q))*(4/q)^n := by ring
      _ ≤ (4/q)*(4/q)^n := mul_le_mul_of_nonneg_right hs (by positivity)
      _ = (4/q)^(n+1) := by rw [pow_succ]; ring

end NativeSpanCoefficientPower
