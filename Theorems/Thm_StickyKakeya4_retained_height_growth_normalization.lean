import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true

namespace RetainedHeightGrowthNormalization

/-- Cancel the original-height density scale against the actual scalar interval-cap
factor. Neither the height count nor the output count is renormalized. -/
theorem scalar_normalized_growth {delta rho beta h lambda N G Q : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (hdensity : lambda * rho ≤ N * delta)
    (hgrowth : beta * h * N ≤ G * (3 * rho ^ 2 / delta) * Q) :
    beta * h * lambda ≤ 3 * G * rho * Q := by
  have hd := mul_le_mul_of_nonneg_left hdensity (mul_nonneg hbeta hh)
  have hg := mul_le_mul_of_nonneg_right hgrowth hdelta.le
  apply (mul_le_mul_iff_left₀ hrho).mp
  calc
    beta * h * lambda * rho = beta * h * (lambda * rho) := by ring
    _ ≤ beta * h * (N * delta) := hd
    _ = (beta * h * N) * delta := by ring
    _ ≤ (G * (3 * rho ^ 2 / delta) * Q) * delta := hg
    _ = (3 * G * rho * Q) * rho := by field_simp [ne_of_gt hdelta]

/-- The scalar output-count lower bound, retaining the original density parameter. -/
theorem scalar_output_lower_bound {delta rho beta h lambda N G Q : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (hG : 0 < G) (hdensity : lambda * rho ≤ N * delta)
    (hgrowth : beta * h * N ≤ G * (3 * rho ^ 2 / delta) * Q) :
    beta * h * lambda / (3 * G * rho) ≤ Q := by
  apply (div_le_iff₀ (show 0 < 3 * G * rho by positivity)).mpr
  simpa only [mul_comm Q] using
    scalar_normalized_growth hdelta hrho hbeta hh hdensity hgrowth

/-- Squaring density is justified by nonnegative lambda. The even powers of beta
and h need no sign assumptions; no separate sign or lower bound on N is needed. -/
theorem planar_normalized_growth {delta rho beta h lambda N G Q : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (hlambda : 0 ≤ lambda)
    (hdensity : lambda * rho ≤ N * delta)
    (hgrowth : beta ^ 2 * h ^ 4 * N ^ 2 ≤ G ^ 2 * (3 * rho ^ 2 / delta) ^ 2 * Q) :
    beta ^ 2 * h ^ 4 * lambda ^ 2 ≤ 9 * G ^ 2 * rho ^ 2 * Q := by
  have hdensity_sq : (lambda * rho) ^ 2 ≤ (N * delta) ^ 2 := by
    simpa only [pow_two] using
      mul_self_le_mul_self (mul_nonneg hlambda hrho.le) hdensity
  have hd := mul_le_mul_of_nonneg_left hdensity_sq
    (show 0 ≤ beta ^ 2 * h ^ 4 by positivity)
  have hg := mul_le_mul_of_nonneg_right hgrowth (sq_nonneg delta)
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hrho)).mp
  calc
    beta ^ 2 * h ^ 4 * lambda ^ 2 * rho ^ 2 =
        beta ^ 2 * h ^ 4 * (lambda * rho) ^ 2 := by ring
    _ ≤ beta ^ 2 * h ^ 4 * (N * delta) ^ 2 := hd
    _ = (beta ^ 2 * h ^ 4 * N ^ 2) * delta ^ 2 := by ring
    _ ≤ (G ^ 2 * (3 * rho ^ 2 / delta) ^ 2 * Q) * delta ^ 2 := hg
    _ = (9 * G ^ 2 * rho ^ 2 * Q) * rho ^ 2 := by field_simp [ne_of_gt hdelta]; ring

/-- The planar output-count lower bound with its rho-to-the-minus-two scale. -/
theorem planar_output_lower_bound {delta rho beta h lambda N G Q : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (hlambda : 0 ≤ lambda)
    (hG : 0 < G) (hdensity : lambda * rho ≤ N * delta)
    (hgrowth : beta ^ 2 * h ^ 4 * N ^ 2 ≤ G ^ 2 * (3 * rho ^ 2 / delta) ^ 2 * Q) :
    beta ^ 2 * h ^ 4 * lambda ^ 2 / (9 * G ^ 2 * rho ^ 2) ≤ Q := by
  apply (div_le_iff₀ (show 0 < 9 * G ^ 2 * rho ^ 2 by positivity)).mpr
  simpa only [mul_comm Q] using
    planar_normalized_growth hdelta hrho hlambda hdensity hgrowth

end RetainedHeightGrowthNormalization
