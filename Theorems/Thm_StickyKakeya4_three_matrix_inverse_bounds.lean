import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Explicit three-dimensional inverse bounds

The constants here come directly from the concrete adjugate formula and the
actual nonsingular matrix inverse. No inverse-norm certificate is assumed.
-/

namespace StickyKakeya4

/-- Each entry of a three-by-three adjugate is a difference of two products. -/
theorem threeMatrix_adjugate_entry_abs_le
    {A : Matrix (Fin 3) (Fin 3) ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hA : ∀ i j, |A i j| ≤ M) (i j : Fin 3) :
    |A.adjugate i j| ≤ 2 * M ^ 2 := by
  have hp (i j k l : Fin 3) : |A i j * A k l| ≤ M ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hA i j) (hA k l) (abs_nonneg _) hM
  have hd (i j k l p q s t : Fin 3) :
      |A i j * A k l - A p q * A s t| ≤ 2 * M ^ 2 := by
    calc
      _ ≤ |A i j * A k l| + |A p q * A s t| := abs_sub _ _
      _ ≤ M ^ 2 + M ^ 2 := add_le_add (hp i j k l) (hp p q s t)
      _ = 2 * M ^ 2 := by ring
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;>
    norm_num only [Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_succ] <;>
    simp only [neg_add_eq_sub] <;> apply hd

/-- A positive determinant lower bound makes the actual matrix nonsingular. -/
theorem threeMatrix_det_ne_zero
    {A : Matrix (Fin 3) (Fin 3) ℝ} {Δ : ℝ}
    (hΔ : 0 < Δ) (hdet : Δ ≤ |A.det|) : A.det ≠ 0 := by
  exact abs_pos.mp (lt_of_lt_of_le hΔ hdet)

/-- Explicit entrywise bound for the actual inverse of a three-by-three matrix. -/
theorem threeMatrix_inv_entry_abs_le
    {A : Matrix (Fin 3) (Fin 3) ℝ} {M Δ : ℝ}
    (hM : 0 ≤ M) (hΔ : 0 < Δ)
    (hA : ∀ i j, |A i j| ≤ M) (hdet : Δ ≤ |A.det|) (i j : Fin 3) :
    |A⁻¹ i j| ≤ 2 * M ^ 2 / Δ := by
  rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul,
    abs_mul, abs_inv]
  have hD : 0 < |A.det| := lt_of_lt_of_le hΔ hdet
  calc
    _ ≤ |A.det|⁻¹ * (2 * M ^ 2) :=
      mul_le_mul_of_nonneg_left (threeMatrix_adjugate_entry_abs_le hM hA i j)
        (inv_nonneg.mpr hD.le)
    _ = (2 * M ^ 2) / |A.det| := by ring
    _ ≤ (2 * M ^ 2) / Δ :=
      div_le_div_of_nonneg_left (by positivity) hΔ hdet

/-- Solving the actual matrix equation costs three inverse-entry bounds. -/
theorem threeMatrix_solution_entry_abs_le
    {A : Matrix (Fin 3) (Fin 3) ℝ} {u v : Fin 3 → ℝ} {M Δ ε : ℝ}
    (hM : 0 ≤ M) (hΔ : 0 < Δ) (hε : 0 ≤ ε)
    (hA : ∀ i j, |A i j| ≤ M) (hdet : Δ ≤ |A.det|)
    (huv : A.mulVec u = v) (hv : ∀ i, |v i| ≤ ε) (j : Fin 3) :
    |u j| ≤ 6 * M ^ 2 * ε / Δ := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (threeMatrix_det_ne_zero hΔ hdet)
  have hsolve : (A⁻¹).mulVec v = u := by
    rw [← huv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hunit, Matrix.one_mulVec]
  rw [← hsolve, Matrix.mulVec_apply_eq_sum]
  calc
    _ ≤ ∑ k : Fin 3, |A⁻¹ j k * v k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 3, (2 * M ^ 2 / Δ) * ε := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hv k) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right
          (threeMatrix_inv_entry_abs_le hM hΔ hA hdet j k) hε)
    _ = 6 * M ^ 2 * ε / Δ := by simp; ring

/-- Multiplication by the actual inverse costs three bounded products per entry. -/
theorem threeMatrix_mul_inv_entry_abs_le
    {A B : Matrix (Fin 3) (Fin 3) ℝ} {M Δ E : ℝ}
    (hM : 0 ≤ M) (hΔ : 0 < Δ) (hE : 0 ≤ E)
    (hA : ∀ i j, |A i j| ≤ M) (hdet : Δ ≤ |A.det|)
    (hB : ∀ i j, |B i j| ≤ E) (i j : Fin 3) :
    |(B * A⁻¹) i j| ≤ 6 * M ^ 2 * E / Δ := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k : Fin 3, |B i k * A⁻¹ k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 3, E * (2 * M ^ 2 / Δ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hB i k)
        (threeMatrix_inv_entry_abs_le hM hΔ hA hdet k j) (abs_nonneg _) hE
    _ = 6 * M ^ 2 * E / Δ := by simp; ring

end StickyKakeya4
