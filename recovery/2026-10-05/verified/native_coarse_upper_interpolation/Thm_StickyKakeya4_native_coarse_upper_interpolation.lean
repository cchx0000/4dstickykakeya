import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

noncomputable section
namespace NativeCoarseUpperInterpolation

/-- Forward physical coarse interpolation. The fixed geometric constant C
is absorbed once and the scale ratio costs s*(4+kappa). The hypotheses on
the actual multiplicities are only the given geometric and menu bounds. -/
theorem forward_upper {delta rhoC rhoD r C t s kappa Mc Md : ℝ}
    (hd : 0 < delta) (hD : 0 < rhoD) (hr : 1 ≤ r)
    (hscale : rhoC=r*rhoD) (hratio : r ≤ delta^(-s))
    (hC : 0 ≤ C) (hCcost : C ≤ delta^(-t)) (hk : 0 ≤ kappa)
    (htransfer : Mc ≤ C*r^(4:ℕ)*Md) (hupper : Md ≤ delta^(-t)*rhoD^(-kappa)) :
    Mc ≤ delta^(-(2*t+s*(4+kappa)))*rhoC^(-kappa) := by
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hCp : 0 < rhoC := by rw [hscale]; positivity
  have hscalePow : rhoD^(-kappa)=r^kappa*rhoC^(-kappa) := by
    rw [hscale,Real.mul_rpow hrp.le hD.le,←mul_assoc,←Real.rpow_add hrp]
    simp
  have hcombine : r^(4:ℕ)*r^kappa=r^(4+kappa) := by
    calc
      _ = r^(4:ℝ)*r^kappa := by norm_num
      _ = _ := (Real.rpow_add hrp 4 kappa).symm
  have hratioPow : r^(4+kappa) ≤ delta^(-s*(4+kappa)) := by
    have hB : 0 ≤ (4:ℝ)+kappa := add_nonneg (by norm_num) hk
    have hh := Real.rpow_le_rpow hrp.le hratio hB
    rwa [←Real.rpow_mul hd.le] at hh
  have hcost : C*delta^(-t) ≤ delta^(-t)*delta^(-t) :=
    mul_le_mul_of_nonneg_right hCcost (Real.rpow_nonneg hd.le _)
  calc
    Mc ≤ C*r^(4:ℕ)*Md := htransfer
    _ ≤ C*r^(4:ℕ)*(delta^(-t)*rhoD^(-kappa)) :=
      mul_le_mul_of_nonneg_left hupper (mul_nonneg hC (pow_nonneg hrp.le 4))
    _ = (C*delta^(-t))*(r^(4:ℕ)*r^kappa)*rhoC^(-kappa) := by rw [hscalePow]; ring
    _ = (C*delta^(-t))*r^(4+kappa)*rhoC^(-kappa) := by rw [hcombine]
    _ ≤ (delta^(-t)*delta^(-t))*delta^(-s*(4+kappa))*rhoC^(-kappa) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hcost hratioPow (Real.rpow_nonneg hrp.le _) (by positivity))
        (Real.rpow_nonneg hCp.le _)
    _ = delta^(-(2*t+s*(4+kappa)))*rhoC^(-kappa) := by
      rw [←Real.rpow_add hd,←Real.rpow_add hd]
      congr 2
      ring

/-- Reverse interpolation costs s*10. Since rhoC≥rhoD and kappa≥0, its
negative scale power only improves when transferred to the fine endpoint. -/
theorem reverse_upper {delta rhoC rhoD r C t s kappa Mc Md : ℝ}
    (hd : 0 < delta) (hD : 0 < rhoD) (hr : 1 ≤ r)
    (hscale : rhoC=r*rhoD) (hratio : r ≤ delta^(-s))
    (hC : 0 ≤ C) (hCcost : C ≤ delta^(-t)) (hk : 0 ≤ kappa)
    (htransfer : Md ≤ C*r^(10:ℕ)*Mc) (hupper : Mc ≤ delta^(-t)*rhoC^(-kappa)) :
    Md ≤ delta^(-(2*t+10*s))*rhoD^(-kappa) := by
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hscaleLe : rhoD ≤ rhoC := by
    rw [hscale]
    calc
      rhoD = 1*rhoD := (one_mul _).symm
      _ ≤ r*rhoD := mul_le_mul_of_nonneg_right hr hD.le
  have hscalePow : rhoC^(-kappa) ≤ rhoD^(-kappa) :=
    Real.rpow_le_rpow_of_nonpos hD hscaleLe (neg_nonpos.mpr hk)
  have hratioPow : r^(10:ℕ) ≤ delta^(-10*s) := by
    calc
      _ = r^(10:ℝ) := by norm_num
      _ ≤ (delta^(-s))^(10:ℝ) := Real.rpow_le_rpow hrp.le hratio (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hd.le]; congr 1; ring
  have hcost : C*delta^(-t) ≤ delta^(-t)*delta^(-t) :=
    mul_le_mul_of_nonneg_right hCcost (Real.rpow_nonneg hd.le _)
  calc
    Md ≤ C*r^(10:ℕ)*Mc := htransfer
    _ ≤ C*r^(10:ℕ)*(delta^(-t)*rhoC^(-kappa)) :=
      mul_le_mul_of_nonneg_left hupper (mul_nonneg hC (pow_nonneg hrp.le 10))
    _ ≤ C*r^(10:ℕ)*(delta^(-t)*rhoD^(-kappa)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hscalePow (Real.rpow_nonneg hd.le _))
        (mul_nonneg hC (pow_nonneg hrp.le 10))
    _ = (C*delta^(-t))*r^(10:ℕ)*rhoD^(-kappa) := by ring
    _ ≤ (delta^(-t)*delta^(-t))*delta^(-10*s)*rhoD^(-kappa) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hcost hratioPow (pow_nonneg hrp.le 10) (by positivity))
        (Real.rpow_nonneg hD.le _)
    _ = delta^(-(2*t+10*s))*rhoD^(-kappa) := by
      rw [←Real.rpow_add hd,←Real.rpow_add hd]
      congr 2
      ring

end NativeCoarseUpperInterpolation
