import Definitions.Def_sticky_kakeya4_core

open scoped RealInnerProductSpace

namespace StickyKakeya4

theorem exact_collision_identity (α β : E3) (hα : α ≠ 0) (s : ℝ) :
    ‖β + s • α‖ ^ 2 =
      ‖collisionResidual α β‖ ^ 2 + ‖α‖ ^ 2 * |s - collisionTime α β| ^ 2 := by
  have hnorm : ‖α‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hα)
  have horth : inner ℝ (collisionResidual α β) α = 0 := by
    simp only [collisionResidual, collisionTime, inner_add_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [real_inner_comm β α]
    field_simp
    ring
  have horth' :
      inner ℝ (collisionResidual α β) ((s - collisionTime α β) • α) = 0 := by
    rw [real_inner_smul_right, horth, mul_zero]
  have hdecomp :
      β + s • α = collisionResidual α β + (s - collisionTime α β) • α := by
    simp only [collisionResidual]
    module
  rw [hdecomp]
  calc
    ‖collisionResidual α β + (s - collisionTime α β) • α‖ ^ 2 =
        ‖collisionResidual α β‖ ^ 2 +
          ‖(s - collisionTime α β) • α‖ ^ 2 := by
      simpa only [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_real horth')
    _ = ‖collisionResidual α β‖ ^ 2 +
          ‖α‖ ^ 2 * |s - collisionTime α β| ^ 2 := by
      simp only [norm_smul, Real.norm_eq_abs, mul_pow]
      ring

/-- Two separated Reeb probes control the angular displacement.  This is the
exact linear estimate used when an old collision time is separated from the
current bush time. -/
theorem separated_reeb_two_probe_direction_bound
    (α β : E3) (s t Rs Rt g : ℝ)
    (hRs : ‖β + s • α‖ ≤ Rs)
    (hRt : ‖β + t • α‖ ≤ Rt)
    (hg : 0 < g) (hsep : g ≤ |t - s|) :
    ‖α‖ ≤ (Rs + Rt) / g := by
  have hvector : (t - s) • α = (β + t • α) - (β + s • α) := by
    module
  have hnorm : ‖(t - s) • α‖ ≤ Rt + Rs := by
    rw [hvector]
    exact (norm_sub_le _ _).trans (add_le_add hRt hRs)
  have hproduct : |t - s| * ‖α‖ ≤ Rt + Rs := by
    simpa [norm_smul, Real.norm_eq_abs] using hnorm
  have hgproduct : g * ‖α‖ ≤ Rt + Rs :=
    (mul_le_mul_of_nonneg_right hsep (norm_nonneg α)).trans hproduct
  rw [add_comm]
  exact (le_div_iff₀ hg).2 (by simpa [mul_comm] using hgproduct)

/-- A fixed-angle self-collision of one bush is localized at the bush's Reeb
time, and its transverse Maslov residual is no larger than the bush error. -/
theorem collision_time_local_and_residual_bound
    (α β : E3) (hα : α ≠ 0) (s R τ : ℝ)
    (hR : ‖β + s • α‖ ≤ R) (hRnonneg : 0 ≤ R)
    (hτ : 0 < τ) (hangle : τ ≤ ‖α‖) :
    |collisionTime α β - s| ≤ R / τ ∧
      ‖collisionResidual α β‖ ≤ R := by
  have hid := exact_collision_identity α β hα s
  have hsq : ‖β + s • α‖ ^ 2 ≤ R ^ 2 := by
    nlinarith [norm_nonneg (β + s • α)]
  have hresSq : ‖collisionResidual α β‖ ^ 2 ≤ R ^ 2 := by
    have hterm : 0 ≤ ‖α‖ ^ 2 * |s - collisionTime α β| ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith
  have hres : ‖collisionResidual α β‖ ≤ R := by
    nlinarith [norm_nonneg (collisionResidual α β)]
  have htimeSq :
      ‖α‖ ^ 2 * |s - collisionTime α β| ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_nonneg ‖collisionResidual α β‖]
  have habsnonneg : 0 ≤ |s - collisionTime α β| := abs_nonneg _
  have hτprod : τ * |s - collisionTime α β| ≤ R := by
    have hnormprod :
        ‖α‖ * |s - collisionTime α β| ≤ R := by
      nlinarith [norm_nonneg α]
    exact (mul_le_mul_of_nonneg_right hangle habsnonneg).trans hnormprod
  constructor
  · rw [abs_sub_comm]
    exact (le_div_iff₀ hτ).2 (by simpa [mul_comm] using hτprod)
  · exact hres

end StickyKakeya4
