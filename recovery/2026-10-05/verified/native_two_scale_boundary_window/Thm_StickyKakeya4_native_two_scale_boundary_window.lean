import Theorems.Thm_StickyKakeya4_native_fixed_size_scale_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

noncomputable section
namespace NativeTwoScaleBoundaryWindow

/-- A sufficiently separated arbitrary depth pair can be clamped into the
middle window. Each discarded boundary gap is at most twice the window
fraction of the original level. The clamping does not change any source. -/
theorem exists_clamped_depths (w : ℝ) (hw : 0 < w) (hwsmall : w ≤ 1/8)
    (level m f : ℕ) (hlarge : 4 ≤ w*(level:ℝ)) (hmf : m ≤ f) (hfl : f ≤ level)
    (hfar : 8*w*(level:ℝ) < ((f-m:ℕ):ℝ)) :
    ∃d b : ℕ,m ≤ d ∧ d ≤ b ∧ b ≤ f ∧
      w*(level:ℝ) ≤ d ∧ (b:ℝ) ≤ (1-w)*(level:ℝ) ∧
      ((d-m:ℕ):ℝ) ≤ (2*w)*(level:ℝ) ∧ ((f-b:ℕ):ℝ) ≤ (2*w)*(level:ℝ) := by
  let lo := ⌈w*(level:ℝ)⌉₊
  let hi := ⌊(1-w)*(level:ℝ)⌋₊
  have hln : (0:ℝ) ≤ level := Nat.cast_nonneg _
  have hmn : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hflR : (f:ℝ) ≤ level := by exact_mod_cast hfl
  have hwL : w*(level:ℝ) ≤ (1/8:ℝ)*(level:ℝ) := mul_le_mul_of_nonneg_right hwsmall hln
  have hloLower : w*(level:ℝ) ≤ lo := Nat.le_ceil _
  have hloUpper : (lo:ℝ) < w*(level:ℝ)+1 := Nat.ceil_lt_add_one (mul_nonneg hw.le hln)
  have hhiLower : (1-w)*(level:ℝ)-1 < hi := Nat.sub_one_lt_floor _
  have hhiUpper : (hi:ℝ) ≤ (1-w)*(level:ℝ) := Nat.floor_le (by nlinarith)
  rw [Nat.cast_sub hmf] at hfar
  have hmhi : m ≤ hi := by
    have hh : (m:ℝ) ≤ hi := by nlinarith
    exact_mod_cast hh
  have hlof : lo ≤ f := by
    have hh : (lo:ℝ) ≤ f := by nlinarith
    exact_mod_cast hh
  have hlohi : lo ≤ hi := by
    have hh : (lo:ℝ) ≤ hi := by nlinarith
    exact_mod_cast hh
  let d := max m lo
  let b := min f hi
  have hmd : m ≤ d := le_max_left _ _
  have hbf : b ≤ f := min_le_left _ _
  have hdb : d ≤ b := max_le (le_min hmf hmhi) (le_min hlof hlohi)
  refine ⟨d,b,hmd,hdb,hbf,?_,?_,?_,?_⟩
  · exact hloLower.trans (by exact_mod_cast (le_max_right m lo))
  · exact (show (b:ℝ) ≤ hi by exact_mod_cast min_le_right f hi).trans hhiUpper
  · rw [Nat.cast_sub hmd]
    by_cases hh : m ≤ lo
    · have he : d=lo := max_eq_right hh
      rw [he]
      nlinarith
    · have he : d=m := max_eq_left (le_of_not_ge hh)
      rw [he]
      nlinarith
  · rw [Nat.cast_sub hbf]
    by_cases hh : f ≤ hi
    · have he : b=f := min_eq_left hh
      rw [he]
      nlinarith
    · have he : b=hi := min_eq_right (le_of_not_ge hh)
      rw [he]
      nlinarith

end NativeTwoScaleBoundaryWindow
