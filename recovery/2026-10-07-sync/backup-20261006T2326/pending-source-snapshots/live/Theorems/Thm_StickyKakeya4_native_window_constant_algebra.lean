import Theorems.Thm_StickyKakeya4_native_third_XY_constant_comparison
import Theorems.Thm_StickyKakeya4_native_window_XY_metric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeWindowConstantAlgebra
open NativeSliceADConstant NativeThirdXYConstantComparison NativeWindowXYMetric

lemma constant_mono {l l' u u' B s : ℝ} (hl : 0 < l) (hll : l ≤ l')
    (huu : u' ≤ u) (hB : 0 ≤ B) :
    constant l' u' B s ≤ constant l u B s := by
  apply max_le_max le_rfl
  apply max_le_max
  · exact div_le_div_of_nonneg_left (Real.rpow_nonneg hB _) hl hll
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huu (by norm_num))
      (Real.rpow_nonneg hB _)

/-- The reference ratio and the actual map capacity are paid separately.
The reference ratio loss A occurs once, while the map capacity has degree three. -/
theorem ratio_window_le {lbase ubase p p0 A C x s : ℝ}
    (hl : 0 < lbase) (hu : 0 ≤ ubase) (hp : 0 < p) (hp0 : 0 < p0)
    (hA : 1 ≤ A) (hC : 1 ≤ C) (hRatio : p ≤ A*p0)
    (hx : 0 ≤ x) (hs : 0 ≤ s) (hs3 : s ≤ 3) :
    constant (lbase/(C^2*p)) (27*C^3*ubase*p) (max 64 x) s ≤
      (512*27*A*C^3)*constant (lbase/p0) (ubase*p0) (max 8 x) s := by
  have hAp : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hlow : (lbase/p0)/(A*C^2) ≤ lbase/(C^2*p) := by
    calc
      _ = lbase/(C^2*(A*p0)) := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_left hl.le (by positivity)
        (mul_le_mul_of_nonneg_left hRatio (sq_nonneg C))
  have hupp : 27*C^3*ubase*p ≤ (27*A*C^3)*(ubase*p0) := by
    calc
      _ ≤ 27*C^3*ubase*(A*p0) := mul_le_mul_of_nonneg_left hRatio (by positivity)
      _ = _ := by ring
  have hmono := constant_mono (by positivity : 0 < (lbase/p0)/(A*C^2)) hlow hupp
    (by positivity : 0 ≤ max 64 x)
  have hCA : 1 ≤ A*C^2 := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hC)
  have hCC : A*C^2 ≤ 27*A*C^3 := by
    have hpow : C^2 ≤ C^3 := pow_le_pow_right₀ hC (by omega : 2 ≤ 3)
    have hh := mul_le_mul_of_nonneg_left hpow hAp.le
    nlinarith [mul_nonneg hAp.le (pow_nonneg hCp.le 3)]
  have hgrid := constant_grid_comparison (by positivity : 0 < lbase/p0)
    (by positivity : 0 ≤ ubase*p0) hCA hCC
    (by positivity : 0 < max 8 x) (gap_power_comparison hx hs hs3)
  exact hmono.trans (by simpa only [mul_assoc] using hgrid)

lemma menu_cube_cost_le {Lip : ℝ} (hLip : 0 ≤ Lip) :
    (((2*menuRadius Lip+1)^3:ℕ):ℝ)^3 ≤ (1209:ℝ)^9*(1+Lip)^9 := by
  have hc := (Nat.ceil_lt_add_one hLip).le
  have hb : (((2*menuRadius Lip+1):ℕ):ℝ) ≤ 1209*(1+Lip) := by
    unfold menuRadius
    push_cast
    nlinarith only [hc,hLip]
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (2*menuRadius Lip+1)) hb 9
  simpa only [Nat.cast_pow,←pow_mul,mul_pow] using hp

/-- A source small-power Lipschitz bound costs exactly nine times its
exponent. No quotient constant has been included in this estimate. -/
theorem menu_cube_cost_of_lip_bound {Lip A r e : ℝ}
    (hLip : 0 ≤ Lip) (hA : 1 ≤ A) (hr : 0 < r) (hr1 : r ≤ 1)
    (he : 0 ≤ e) (hbound : Lip ≤ A*r^(-e)) :
    (((2*menuRadius Lip+1)^3:ℕ):ℝ)^3 ≤ (2418*A)^9*r^(-(9*e)) := by
  have hAp : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hp : 1 ≤ r^(-e) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (neg_nonpos.mpr he)
  have hprod : 1 ≤ A*r^(-e) := one_le_mul_of_one_le_of_one_le hA hp
  have hb : 1+Lip ≤ 2*A*r^(-e) := by nlinarith only [hbound,hprod]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+Lip) hb 9
  have hexp : (r^(-e))^9 = r^(-(9*e)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr.le]
    congr 1
    ring
  calc
    _ ≤ (1209:ℝ)^9*(1+Lip)^9 := menu_cube_cost_le hLip
    _ ≤ (1209:ℝ)^9*(2*A*r^(-e))^9 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by rw [mul_pow,mul_pow,hexp]; ring

end NativeWindowConstantAlgebra
