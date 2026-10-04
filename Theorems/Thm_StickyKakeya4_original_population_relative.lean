import Mathlib.Tactic
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace OriginalPopulationRelative
/-- Convert an absolute local count using a proved original population and
 proved graph retention, with both losses visible. -/
theorem ball_from_original_mass {N M count rho R K loss eta : ℝ}
    (hrho : 0 < rho) (heta : 0 < eta) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hdensity : eta ≤ rho*N) (hret : N ≤ loss*M) (hball : count ≤ K*R/rho) :
    count ≤ (K*loss/eta)*R*M := by
  have hmass : eta ≤ rho*(loss*M) := hdensity.trans (mul_le_mul_of_nonneg_left hret hrho.le)
  apply hball.trans
  apply (div_le_iff₀ hrho).mpr
  have hh := mul_le_mul_of_nonneg_left hmass (show 0 ≤ K*R by positivity)
  have hdiv := div_le_div_of_nonneg_right hh heta.le
  have hcancel : K*R*eta/eta=K*R := by field_simp
  rw [hcancel] at hdiv
  convert hdiv using 1
  ring
end OriginalPopulationRelative
