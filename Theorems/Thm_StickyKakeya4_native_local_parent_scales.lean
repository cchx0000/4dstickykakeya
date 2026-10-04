import Theorems.Thm_StickyKakeya4_native_local_parent_cells
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeLocalParentScales
open StickyKakeya4

lemma relative_scale {delta : ℝ} {level m : ℕ} (hdy : delta=(2:ℝ)⁻¹^level) (hm : m ≤ level) :
    ((2^m:ℕ):ℝ)*delta=(2:ℝ)⁻¹^(level-m) := by
  rw [hdy,show level=m+(level-m) by omega,pow_add]
  simp only [Nat.cast_pow,Nat.cast_ofNat,inv_pow]
  rw [←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℝ)≠0)),one_mul]
  simp

/-- The actual local tube and cube scales stay dyadic, with relative fine
scale2^m*delta and the fixed64/128 normalization factors displayed. -/
theorem local_scales_dyadic {delta : ℝ} {level m : ℕ}
    (hdy : delta=(2:ℝ)⁻¹^level) (hm : m ≤ level) :
    IsWZDyadicScale (((2^m:ℕ):ℝ)*delta/64) ∧
      IsWZDyadicScale (((2^m:ℕ):ℝ)*delta/128) := by
  have hr : IsWZDyadicScale (((2^m:ℕ):ℝ)*delta) := ⟨level-m,relative_scale hdy hm⟩
  constructor
  · simpa only [show (2:ℝ)^6=64 by norm_num] using NativePaddedCellSource.dyadic_div_power hr 6
  · simpa only [show (2:ℝ)^7=128 by norm_num] using NativePaddedCellSource.dyadic_div_power hr 7
end NativeLocalParentScales
