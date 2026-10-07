import Theorems.Thm_StickyKakeya4_native_recoded_grid_ad

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeRecodedGridCost

/-- The grid-recoding loss is polynomial in its displacement constant.
There is no ambient-dimensional power of the fine/coarse mesh ratio. -/
theorem coefficient_le_power (l : ℕ) {alpha K s : ℝ}
    (halpha : 1 ≤ alpha) (hs : 0 ≤ s) :
    ((((4*⌈alpha⌉₊+5)^l:ℕ):ℝ)*K^2*(4*((⌈alpha⌉₊:ℝ)+2))^s) ≤
      (13:ℝ)^l*(16:ℝ)^s*K^2*alpha^((l:ℝ)+s) := by
  have ha : 0 < alpha := lt_of_lt_of_le zero_lt_one halpha
  have hceil := (Nat.ceil_lt_add_one ha.le).le
  have hbase : ((4*⌈alpha⌉₊+5:ℕ):ℝ) ≤ 13*alpha := by
    push_cast
    linarith only [hceil,halpha]
  have hgrid := pow_le_pow_left₀ (Nat.cast_nonneg (4*⌈alpha⌉₊+5)) hbase l
  have hrad : 4*((⌈alpha⌉₊:ℝ)+2) ≤ 16*alpha := by linarith only [hceil,halpha]
  have hradpow := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 4*((⌈alpha⌉₊:ℝ)+2)) hrad hs
  have hpower : alpha^l*alpha^s = alpha^((l:ℝ)+s) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ha]
  calc
    _ = (((4*⌈alpha⌉₊+5:ℕ):ℝ)^l)*K^2*(4*((⌈alpha⌉₊:ℝ)+2))^s := by rw [Nat.cast_pow]
    _ ≤ (13*alpha)^l*K^2*(16*alpha)^s :=
      mul_le_mul (mul_le_mul_of_nonneg_right hgrid (sq_nonneg K)) hradpow
        (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = (13:ℝ)^l*(16:ℝ)^s*K^2*(alpha^l*alpha^s) := by
      rw [mul_pow,Real.mul_rpow (by norm_num) ha.le]
      ring
    _ = _ := by rw [hpower]

/-- The actual one- and two-dimensional quotient cases have a fixed
fourth-degree geometry cost, useful for the pre-source power budget. -/
theorem low_dim_coefficient_le (l : ℕ) {alpha K s : ℝ}
    (hl : l ≤ 2) (halpha : 1 ≤ alpha) (hs : 0 ≤ s) (hs2 : s ≤ 2) :
    ((((4*⌈alpha⌉₊+5)^l:ℕ):ℝ)*K^2*(4*((⌈alpha⌉₊:ℝ)+2))^s) ≤
      43264*K^2*alpha^4 := by
  have ha : 0 < alpha := lt_of_lt_of_le zero_lt_one halpha
  have h13 : (13:ℝ)^l ≤ 169 := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 13) hl
    norm_num at hh
    exact hh
  have h16 : (16:ℝ)^s ≤ 256 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 16) hs2
    norm_num at hh
    exact hh
  have hlr : (l:ℝ) ≤ 2 := by exact_mod_cast hl
  have ha4 : alpha^((l:ℝ)+s) ≤ alpha^4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le halpha (show (l:ℝ)+s ≤ 4 by linarith only [hlr,hs2])
    simpa only [Real.rpow_ofNat] using hh
  have hprod : (13:ℝ)^l*(16:ℝ)^s ≤ 169*256 :=
    mul_le_mul h13 h16 (Real.rpow_nonneg (by norm_num) _) (by norm_num)
  calc
    _ ≤ (13:ℝ)^l*(16:ℝ)^s*K^2*alpha^((l:ℝ)+s) := coefficient_le_power l halpha hs
    _ ≤ (169*256)*K^2*alpha^4 := mul_le_mul
      (mul_le_mul_of_nonneg_right hprod (sq_nonneg K)) ha4
      (Real.rpow_nonneg ha.le _) (by positivity)
    _ = _ := by norm_num

end NativeRecodedGridCost
