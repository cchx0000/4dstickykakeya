import Theorems.Thm_StickyKakeya4_native_middle_grain_parent_budget
import Theorems.Thm_StickyKakeya4_native_quarter_scale_parameters

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeAngularTestScale

/-- Ordinary dyadic rounding at the actual angular mesh. The chosen scale
is at least the target and less than twice it. -/
theorem exists_dyadic_angular_scale {target : ℝ} (ht : 0< target) (ht1 : target≤ 1) :
    ∃s : ℕ,6≤ s ∧ target≤ 64/((2^s:ℕ):ℝ) ∧ 64/((2^s:ℕ):ℝ)≤ 2*target := by
  have hx : (1:ℝ)≤ 1/target := (le_div_iff₀ ht).mpr (by simpa only [one_mul] using ht1)
  obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)< 2)
  have hjpos : (0:ℝ)< 2^j := by positivity
  have hlow : target≤ 1/(2:ℝ)^j := (le_div_iff₀ hjpos).mpr
    (by have hh := (le_div_iff₀ ht).mp hlo; nlinarith only [hh])
  have hhigh : 1/(2:ℝ)^j≤ 2*target := by
    have hh := (div_lt_iff₀ ht).mp hhi
    rw [pow_succ] at hh
    apply (div_le_iff₀ hjpos).mpr
    nlinarith only [hh]
  have hid : (64:ℝ)/((2^(j+6):ℕ):ℝ)=1/(2:ℝ)^j := by
    rw [Nat.cast_pow,Nat.cast_ofNat,pow_add]
    norm_num
    field_simp
  exact ⟨j+6,by omega,by simpa only [hid] using hlow,by simpa only [hid] using hhigh⟩

/-- A dyadic rho near Delta^(1-3epsilon) absorbs the actual affine error
and obeys the loose r^(1/3) upper required by the kappa≤ 1 contradiction.
It lies between depths6 andm, so the global angular depth is between
m+3 and2m-3. -/
theorem exists_actual_test_scale {r epsilon : ℝ} (m : ℕ) (hm : 6≤ m)
    (hr : 0< r) (hr1 : r≤ 1) (he : 0< epsilon) (he9 : epsilon≤ 1/9)
    (hsmall : ((64:ℝ)/((2^m:ℕ):ℝ))^epsilon≤ 1/10)
    (hroot : (64:ℝ)/((2^m:ℕ):ℝ)≤ 80*r^(1/2:ℝ)) :
    ∃s : ℕ,6≤ s ∧ s≤ m ∧
      (((64:ℝ)/((2^m:ℕ):ℝ))^(1-3*epsilon)≤ 64/((2^s:ℕ):ℝ)) ∧
      ((64:ℝ)/((2^s:ℕ):ℝ)≤ 2*((64:ℝ)/((2^m:ℕ):ℝ))^(1-3*epsilon)) ∧
      (5/4:ℝ)*((64:ℝ)/((2^m:ℕ):ℝ))^(1-2*epsilon)≤ (64/((2^s:ℕ):ℝ))/8 ∧
      (64:ℝ)/((2^s:ℕ):ℝ)≤ 160*r^(1/3:ℝ) := by
  let Delta : ℝ := 64/((2^m:ℕ):ℝ)
  have hD : 0< Delta := by dsimp [Delta]; positivity
  have hN : (64:ℝ)≤ ((2^m:ℕ):ℝ) := by
    exact_mod_cast (show (64:ℕ)≤ 2^m by
      simpa only [show (2:ℕ)^6=64 by norm_num] using Nat.pow_le_pow_right (by norm_num : 0< (2:ℕ)) hm)
  have hD1 : Delta≤ 1 := (div_le_one (by positivity)).mpr hN
  have hexp : 0≤ 1-3*epsilon := by linarith only [he9]
  have htarget := Real.rpow_pos_of_pos hD (1-3*epsilon)
  have htarget1 := Real.rpow_le_one hD.le hD1 hexp
  obtain ⟨s,hs,hlow,hhigh⟩ := exists_dyadic_angular_scale htarget htarget1
  have hDtarget : Delta≤ Delta^(1-3*epsilon) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hD hD1 (by linarith only [he] : 1-3*epsilon≤ 1))
  have hsm : s≤ m := by
    have hh := hDtarget.trans hlow
    have hp : ((2^s:ℕ):ℝ)≤ ((2^m:ℕ):ℝ) := by
      have hh' := (div_le_div_iff₀ (by positivity : (0:ℝ)< ((2^m:ℕ):ℝ))
        (by positivity : (0:ℝ)< ((2^s:ℕ):ℝ))).mp hh
      linarith only [hh']
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1< (2:ℕ))).mp (by exact_mod_cast hp)
  have hsplit : Delta^(1-2*epsilon)=Delta^epsilon*Delta^(1-3*epsilon) := by
    rw [←Real.rpow_add hD]
    congr 1
    ring
  have herror : (5/4:ℝ)*Delta^(1-2*epsilon)≤ (64/((2^s:ℕ):ℝ))/8 := by
    have hh := mul_le_mul_of_nonneg_right hsmall htarget.le
    rw [←hsplit] at hh
    nlinarith only [hh,hlow]
  have hrootPower : Delta^(1-3*epsilon)≤ 80*r^(1/3:ℝ) := by
    have hh := Real.rpow_le_rpow hD.le hroot hexp
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤ 80) (Real.rpow_nonneg hr.le _),←Real.rpow_mul hr.le] at hh
    have h80 : (80:ℝ)^(1-3*epsilon)≤ 80 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1:ℝ)≤ 80) (by linarith only [he] : 1-3*epsilon≤ 1)
    have hR : r^((1/2:ℝ)*(1-3*epsilon))≤ r^(1/3:ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith only [he9])
    exact hh.trans (mul_le_mul h80 hR (Real.rpow_nonneg hr.le _) (by norm_num))
  exact ⟨s,hs,hsm,hlow,hhigh,herror,hhigh.trans (by nlinarith only [hrootPower])⟩

end NativeAngularTestScale
