import Theorems.Thm_StickyKakeya4_native_matrix_height_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeSingleHeightBudget

/-- The actual number8R of fine-height bins is paid by the physical error
scale. There is no independent subpower-height-menu assumption. -/
theorem height_cost_from_error_envelope {mu epsilon C : ℝ} (R : ℕ)
    (hmu : 0<mu) (hmu1 : mu≤1) (he : 0≤epsilon) (hC : 0≤C)
    (hbase : mu*(R:ℝ)≤2*max (C*(64*mu)^(1-2*epsilon)) mu) :
    (8*R:ℕ)≤16*max (64*C) 1*mu^(-2*epsilon) := by
  have hpow : 0<mu^(-2*epsilon) := Real.rpow_pos_of_pos hmu _
  have hp1 : 1≤mu^(-2*epsilon) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hmu hmu1
      (show -2*epsilon≤0 by linarith)
  have h64 : (64:ℝ)^(1-2*epsilon)≤64 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤64)
      (show 1-2*epsilon≤1 by linarith)
  have hmul : mu^(1-2*epsilon)=mu*mu^(-2*epsilon) := by
    rw [show 1-2*epsilon=1+(-2*epsilon) by ring,Real.rpow_add hmu,Real.rpow_one]
  have hE : C*(64*mu)^(1-2*epsilon)≤mu*(max (64*C) 1*mu^(-2*epsilon)) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤64) hmu.le,hmul]
    calc
      _ ≤ C*(64*(mu*mu^(-2*epsilon))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h64 (by positivity)) hC
      _ = mu*((64*C)*mu^(-2*epsilon)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (le_max_left (64*C) 1) hpow.le) hmu.le
  have hOne : 1≤max (64*C) 1*mu^(-2*epsilon) :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _) hp1
  have hmuB : mu≤mu*(max (64*C) 1*mu^(-2*epsilon)) := by nlinarith
  have hmax := max_le hE hmuB
  have hR : (R:ℝ)≤2*max (64*C) 1*mu^(-2*epsilon) := by
    have hh := hbase.trans (mul_le_mul_of_nonneg_left hmax (by norm_num : (0:ℝ)≤2))
    have hh' : mu*(R:ℝ)≤mu*(2*max (64*C) 1*mu^(-2*epsilon)) := by nlinarith only [hh]
    exact (mul_le_mul_iff_right₀ hmu).mp hh'
  push_cast
  nlinarith only [hR]

end NativeSingleHeightBudget
