import Theorems.Thm_StickyKakeya4_native_same_source_balance_absorption

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

noncomputable section
namespace NativeNearPowerCleanup
open NativeSameSourceBalanceAbsorption

/-- Replace the complementary-scale error by its original-delta lower bound.
The exact product, rather than a scale-comparison convention, supplies it. -/
lemma remove_complementary_error {delta rho eps power loss kappa M : ℝ}
    (hd : 0<delta) (hr : 0<rho) (he : 0<eps) (hscale : rho*eps=delta)
    (hr1 : rho≤1) (hloss : 0≤loss)
    (hbound : delta^power*eps^loss*rho^(-kappa) ≤ M) :
    delta^(power+loss)*rho^(-kappa) ≤ M := by
  have hde : delta≤eps := by
    calc
      delta = rho*eps := hscale.symm
      _ ≤ 1*eps := mul_le_mul_of_nonneg_right hr1 he.le
      _ = eps := one_mul _
  have hp := Real.rpow_le_rpow hd.le hde hloss
  calc
    _ = delta^power*delta^loss*rho^(-kappa) := by rw [Real.rpow_add hd]
    _ ≤ delta^power*eps^loss*rho^(-kappa) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (Real.rpow_pos_of_pos hd _).le)
        (Real.rpow_pos_of_pos hr _).le
    _ ≤ M := hbound

/-- Combine a source-derived cost absorption with the exact complementary
scale identity to leave a pure original-delta near-extremal loss. -/
lemma absorb_and_remove_error {delta rho eps power costLoss loss kappa C M : ℝ}
    (hd : 0<delta) (hr : 0<rho) (he : 0<eps) (hscale : rho*eps=delta)
    (hr1 : rho≤1) (hloss : 0≤loss) (hM : 0≤M)
    (hbound : delta^power*eps^loss*rho^(-kappa) ≤ C*M)
    (hcost : C ≤ delta^(-costLoss)) :
    delta^(power+costLoss+loss)*rho^(-kappa) ≤ M := by
  have hh := absorb_balance_cost (power:=power) (loss:=costLoss)
    (X:=eps^loss*rho^(-kappa)) hd hM (by simpa only [mul_assoc] using hbound) hcost
  exact remove_complementary_error hd hr he hscale hr1 hloss
    (by simpa only [mul_assoc] using hh)

end NativeNearPowerCleanup
