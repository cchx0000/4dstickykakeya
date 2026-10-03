import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 3000000

noncomputable section

namespace TwoDimensionalTransverseEscape

/-- The determinant of two real column vectors, expressed in scalar coordinates. -/
def det2 (x₁ y₁ x₂ y₂ : ℝ) : ℝ := x₁ * y₂ - y₁ * x₂

/-- A vector of max norm at least `h`, and another vector at max-norm distance
at least `h` from every scalar multiple of the first, have determinant at least
`h²` in absolute value. No determinant lower bound is assumed. -/
theorem det_abs_lower_of_max_transverse
    (h x₁ y₁ x₂ y₂ : ℝ) (hh : 0 < h)
    (hfirst : h ≤ max |x₁| |y₁|)
    (htrans : ∀ t : ℝ, h ≤ max |x₂ - t * x₁| |y₂ - t * y₁|) :
    h ^ 2 ≤ |det2 x₁ y₁ x₂ y₂| := by
  rcases le_total |y₁| |x₁| with hmax | hmax
  · have hx : h ≤ |x₁| := by simpa only [max_eq_left hmax] using hfirst
    have hx0 : x₁ ≠ 0 := by
      intro heq
      simp only [heq, abs_zero] at hx
      linarith
    have hcancel : x₂ - x₂ / x₁ * x₁ = 0 := by field_simp; ring
    have hdist : h ≤ |y₂ - x₂ / x₁ * y₁| := by
      simpa only [hcancel, abs_zero, max_eq_right (abs_nonneg (y₂ - x₂ / x₁ * y₁))] using htrans (x₂ / x₁)
    have hid : det2 x₁ y₁ x₂ y₂ = x₁ * (y₂ - x₂ / x₁ * y₁) := by
      dsimp [det2]
      field_simp
    rw [hid, abs_mul]
    nlinarith [mul_le_mul hx hdist hh.le (abs_nonneg x₁)]
  · have hy : h ≤ |y₁| := by simpa only [max_eq_right hmax] using hfirst
    have hy0 : y₁ ≠ 0 := by
      intro heq
      simp only [heq, abs_zero] at hy
      linarith
    have hcancel : y₂ - y₂ / y₁ * y₁ = 0 := by field_simp; ring
    have hdist : h ≤ |x₂ - y₂ / y₁ * x₁| := by
      simpa only [hcancel, abs_zero, max_eq_left (abs_nonneg (x₂ - y₂ / y₁ * x₁))] using htrans (y₂ / y₁)
    have hid : det2 x₁ y₁ x₂ y₂ = -(y₁ * (x₂ - y₂ / y₁ * x₁)) := by
      dsimp [det2]
      field_simp
      ring
    rw [hid, abs_neg, abs_mul]
    nlinarith [mul_le_mul hy hdist hh.le (abs_nonneg y₁)]

/-- Scalar Cramer's-rule bound. Each coordinate of both columns is bounded by
`V`, and each coordinate of their linear combination is bounded by `R`. -/
theorem coefficients_mul_bound_of_det_bound
    (h V R x₁ y₁ x₂ y₂ a b : ℝ)
    (hdet : h ^ 2 ≤ |det2 x₁ y₁ x₂ y₂|)
    (hx₁ : |x₁| ≤ V) (hy₁ : |y₁| ≤ V)
    (hx₂ : |x₂| ≤ V) (hy₂ : |y₂| ≤ V)
    (hX : |x₁ * a + x₂ * b| ≤ R)
    (hY : |y₁ * a + y₂ * b| ≤ R) :
    h ^ 2 * |a| ≤ 2 * V * R ∧ h ^ 2 * |b| ≤ 2 * V * R := by
  have hV : 0 ≤ V := (abs_nonneg x₁).trans hx₁
  have hR : 0 ≤ R := (abs_nonneg (x₁ * a + x₂ * b)).trans hX
  constructor
  · calc
      h ^ 2 * |a| ≤ |det2 x₁ y₁ x₂ y₂| * |a| :=
        mul_le_mul_of_nonneg_right hdet (abs_nonneg a)
      _ = |det2 x₁ y₁ x₂ y₂ * a| := (abs_mul _ _).symm
      _ = |(x₁ * a + x₂ * b) * y₂ - (y₁ * a + y₂ * b) * x₂| := by
        congr 1
        dsimp [det2]
        ring
      _ ≤ |(x₁ * a + x₂ * b) * y₂| + |(y₁ * a + y₂ * b) * x₂| := abs_sub _ _
      _ = |x₁ * a + x₂ * b| * |y₂| + |y₁ * a + y₂ * b| * |x₂| := by
        rw [abs_mul, abs_mul]
      _ ≤ R * V + R * V := by gcongr
      _ = 2 * V * R := by ring
  · calc
      h ^ 2 * |b| ≤ |det2 x₁ y₁ x₂ y₂| * |b| :=
        mul_le_mul_of_nonneg_right hdet (abs_nonneg b)
      _ = |det2 x₁ y₁ x₂ y₂ * b| := (abs_mul _ _).symm
      _ = |x₁ * (y₁ * a + y₂ * b) - y₁ * (x₁ * a + x₂ * b)| := by
        congr 1
        dsimp [det2]
        ring
      _ ≤ |x₁ * (y₁ * a + y₂ * b)| + |y₁ * (x₁ * a + x₂ * b)| := abs_sub _ _
      _ = |x₁| * |y₁ * a + y₂ * b| + |y₁| * |x₁ * a + x₂ * b| := by
        rw [abs_mul, abs_mul]
      _ ≤ V * R + V * R := by gcongr
      _ = 2 * V * R := by ring

/-- Division form of the scalar coefficient estimate. -/
theorem coefficients_bound_of_det_bound
    (h V R x₁ y₁ x₂ y₂ a b : ℝ) (hh : 0 < h)
    (hdet : h ^ 2 ≤ |det2 x₁ y₁ x₂ y₂|)
    (hx₁ : |x₁| ≤ V) (hy₁ : |y₁| ≤ V)
    (hx₂ : |x₂| ≤ V) (hy₂ : |y₂| ≤ V)
    (hX : |x₁ * a + x₂ * b| ≤ R)
    (hY : |y₁ * a + y₂ * b| ≤ R) :
    |a| ≤ 2 * V * R / h ^ 2 ∧ |b| ≤ 2 * V * R / h ^ 2 := by
  obtain ⟨ha, hb⟩ := coefficients_mul_bound_of_det_bound h V R x₁ y₁ x₂ y₂ a b
    hdet hx₁ hy₁ hx₂ hy₂ hX hY
  constructor
  · exact (le_div_iff₀ (sq_pos_of_pos hh)).2 (by simpa [mul_comm] using ha)
  · exact (le_div_iff₀ (sq_pos_of_pos hh)).2 (by simpa [mul_comm] using hb)

/-- Applied to coefficient differences, the transverse hypotheses alone yield
both scalar coefficient bounds. -/
theorem coefficient_differences_bound_of_max_transverse
    (h V R x₁ y₁ x₂ y₂ c₁ c₂ d₁ d₂ : ℝ) (hh : 0 < h)
    (hfirst : h ≤ max |x₁| |y₁|)
    (htrans : ∀ t : ℝ, h ≤ max |x₂ - t * x₁| |y₂ - t * y₁|)
    (hx₁ : |x₁| ≤ V) (hy₁ : |y₁| ≤ V)
    (hx₂ : |x₂| ≤ V) (hy₂ : |y₂| ≤ V)
    (hX : |x₁ * (c₁ - d₁) + x₂ * (c₂ - d₂)| ≤ R)
    (hY : |y₁ * (c₁ - d₁) + y₂ * (c₂ - d₂)| ≤ R) :
    |c₁ - d₁| ≤ 2 * V * R / h ^ 2 ∧ |c₂ - d₂| ≤ 2 * V * R / h ^ 2 := by
  exact coefficients_bound_of_det_bound h V R x₁ y₁ x₂ y₂ (c₁ - d₁) (c₂ - d₂) hh
    (det_abs_lower_of_max_transverse h x₁ y₁ x₂ y₂ hh hfirst htrans)
    hx₁ hy₁ hx₂ hy₂ hX hY

end TwoDimensionalTransverseEscape
