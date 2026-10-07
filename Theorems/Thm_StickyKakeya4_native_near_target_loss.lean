import Theorems.Thm_StickyKakeya4_native_near_power_cleanup

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

noncomputable section
namespace NativeNearTargetLoss

/-- A larger allowed original-delta loss weakens an established near lower. -/
lemma lower_with_target_loss {delta rho exponent target kappa M : ℝ}
    (hd : 0<delta) (hd1 : delta≤1) (hr : 0<rho) (hexp : exponent≤target)
    (hbound : delta^exponent*rho^(-kappa)≤M) :
    delta^target*rho^(-kappa)≤M := by
  exact (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 hexp) (Real.rpow_pos_of_pos hr _).le).trans hbound

/-- A scale error is paid at original delta whenever that scale is at least
delta. The upper loss then combines additively with the original-delta loss. -/
lemma upper_with_target_loss {delta rho gamma loss target kappa M : ℝ}
    (hd : 0<delta) (hd1 : delta≤1) (hr : 0<rho) (hscale : delta≤rho)
    (hloss : 0≤loss) (hexp : gamma+loss≤target)
    (hbound : M≤delta^(-gamma)*rho^(-kappa-loss)) :
    M≤delta^(-target)*rho^(-kappa) := by
  have herror := Real.rpow_le_rpow_of_nonpos hd hscale (neg_nonpos.mpr hloss)
  calc
    M ≤ delta^(-gamma)*rho^(-kappa-loss) := hbound
    _ = (delta^(-gamma)*rho^(-loss))*rho^(-kappa) := by
      rw [mul_assoc,←Real.rpow_add hr]
      congr 2
      ring
    _ ≤ (delta^(-gamma)*delta^(-loss))*rho^(-kappa) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left herror (Real.rpow_pos_of_pos hd _).le)
        (Real.rpow_pos_of_pos hr _).le
    _ = delta^(-(gamma+loss))*rho^(-kappa) := by
      rw [←Real.rpow_add hd]
      congr 2
      ring
    _ ≤ delta^(-target)*rho^(-kappa) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)) (Real.rpow_pos_of_pos hr _).le

end NativeNearTargetLoss
