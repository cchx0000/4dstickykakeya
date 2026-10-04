import Theorems.Thm_StickyKakeya4_symmetry_chain_uniform_density
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace NativeAsymmetricScaleBudget
open SymmetryDifferenceGrowthChain
noncomputable section

def budget (n J : ℕ) (ν : ℝ) : ℕ := n+4+2^J*⌈20/ν⌉₊

lemma ceil_inverse_bound {ν : ℝ} (hν : 0<ν) (hν1 : ν≤1) :
    (⌈20/ν⌉₊ : ℝ) ≤ 21/ν := by
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 20/ν by positivity)
  have hh : 20/ν+1 ≤ 21/ν := by
    apply (le_div_iff₀ hν).mpr
    field_simp
    nlinarith
  exact hc.le.trans hh

lemma budget_linear_bound (n J : ℕ) {ν : ℝ} (hν : 0<ν) (hν1 : ν≤1) :
    2*(budget n J ν : ℝ)+1 ≤ 100*((2:ℝ)^J+1)*((n:ℝ)+5)/ν := by
  have hc := ceil_inverse_bound hν hν1
  have hp : 0 ≤ (2:ℝ)^J := by positivity
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  unfold budget
  push_cast
  apply (le_div_iff₀ hν).mpr
  have hc' : (⌈20/ν⌉₊ : ℝ)*ν ≤ 21 := (le_div_iff₀ hν).mp hc
  have hprod := mul_le_mul_of_nonneg_left hc' hp
  have hbase : (2*(n:ℝ)+9)*ν ≤ 2*(n:ℝ)+9 := by nlinarith
  nlinarith

lemma threshold_native (J : ℕ) (ν : ℝ) :
    threshold (ν/10) J = 2*ν^(2^J)/(20:ℝ)^(2^J) := by
  rw [threshold_formula]
  have h : ν/10/2 = ν/20 := by ring
  rw [h,div_pow]
  ring

/-- The chain density has an explicit fixed-depth polynomial loss in the
original energy parameter and one logarithmic mesh factor. -/
theorem density_native_lower (n J : ℕ) {ν : ℝ} (hν : 0<ν) (hν1 : ν≤1) :
    2*ν^(2^J+1)/((20:ℝ)^(2^J)*(100*((2:ℝ)^J+1))*((n:ℝ)+5)) ≤
      threshold (ν/10) J/(2*(budget n J ν : ℝ)+1) := by
  have hb := budget_linear_bound n J hν hν1
  have hd : 0 < 2*(budget n J ν : ℝ)+1 := by positivity
  have hn : 0 < (n:ℝ)+5 := by positivity
  have he : 0 < (20:ℝ)^(2^J) := by positivity
  have hc : 0 < 100*((2:ℝ)^J+1) := by positivity
  rw [threshold_native]
  calc
    _ = (2*ν^(2^J)/(20:ℝ)^(2^J)) /
        (100*((2:ℝ)^J+1)*((n:ℝ)+5)/ν) := by
      rw [pow_succ]
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hd hb

lemma inverse_le_binary_ceil (ν : ℝ) :
    20/ν ≤ (2:ℝ)^⌈20/ν⌉₊ := by
  have h := (show ⌈20/ν⌉₊ < 2^⌈20/ν⌉₊ from Nat.lt_two_pow_self).le
  exact (Nat.le_ceil _).trans (by exact_mod_cast h)

/-- A literal bounded separated-source cardinality budget, uniform in the
energy parameter. The mesh level is n and the fixed chain depth is J. -/
theorem native_card_budget (n J : ℕ) {ν x y : ℝ} (hν : 0<ν)
    (hx : x ≤ 9*(2:ℝ)^n) (hy : y ≤ 3*(2:ℝ)^n) :
    x ≤ (2:ℝ)^(budget n J ν) ∧
    y/threshold (ν/10) J ≤ (2:ℝ)^(budget n J ν) := by
  let k := ⌈20/ν⌉₊
  let e := 2^J
  have hbin := inverse_le_binary_ceil ν
  have hp : (20/ν)^e ≤ ((2:ℝ)^k)^e :=
    pow_le_pow_left₀ (by positivity) hbin e
  have hpow : ((2:ℝ)^k)^e = (2:ℝ)^(e*k) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hpow] at hp
  have hE : 1 ≤ (2:ℝ)^(e*k) := one_le_pow₀ (by norm_num)
  have hformula : (2:ℝ)^(budget n J ν) = (2:ℝ)^n*16*(2:ℝ)^(e*k) := by
    dsimp [budget,e,k]
    rw [pow_add,pow_add]
    norm_num
  rw [hformula]
  constructor
  · have hn : 0 ≤ (2:ℝ)^n := by positivity
    nlinarith
  · have ht := threshold_pos (div_pos hν (by norm_num : (0:ℝ)<10)) J
    have hrecip : (threshold (ν/10) J)⁻¹ = (20/ν)^e/2 := by
      rw [threshold_native]
      dsimp [e]
      rw [div_pow]
      field_simp
    rw [div_eq_mul_inv,hrecip]
    calc
      _ ≤ (3*(2:ℝ)^n)*((20/ν)^e/2) :=
        mul_le_mul_of_nonneg_right hy (by positivity)
      _ ≤ (3*(2:ℝ)^n)*((2:ℝ)^(e*k)/2) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp (by norm_num)) (by positivity)
      _ ≤ _ := by
        have hpos : 0 ≤ (2:ℝ)^n*(2:ℝ)^(e*k) := by positivity
        nlinarith
end
end NativeAsymmetricScaleBudget
