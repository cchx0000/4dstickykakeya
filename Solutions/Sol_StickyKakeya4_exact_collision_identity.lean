import Definitions.Def_sticky_kakeya4_core

open scoped RealInnerProductSpace

open StickyKakeya4

theorem solution (α β : E3) (hα : α ≠ 0) (s : ℝ) :
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
