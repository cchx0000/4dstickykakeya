import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

noncomputable section
namespace RadialAnglePeriodicCover
open Classical

/-- Five literal pi-shifts cover every bounded angle difference with small
sine; this supplies an interval-counting proof, not an angular-cover axiom. -/
theorem small_sine_five_intervals {x e : ℝ} (hx : |x|≤2*Real.pi)
    (hs : |Real.sin x|≤e) :
    ∃ k∈Finset.Icc (-2:ℤ) 2, |x-(k:ℝ)*Real.pi|≤Real.pi/2*e := by
  let k : ℤ := ⌊x/Real.pi+1/2⌋
  have hlo : (k:ℝ)≤x/Real.pi+1/2 := Int.floor_le _
  have hhi : x/Real.pi+1/2<(k:ℝ)+1 := Int.lt_floor_add_one _
  have hp := Real.pi_pos
  have hpne : Real.pi≠0 := ne_of_gt hp
  have hlo' := mul_le_mul_of_nonneg_right hlo hp.le
  have hhi' := mul_lt_mul_of_pos_right hhi hp
  have hc : (x/Real.pi)*Real.pi=x := div_mul_cancel₀ x hpne
  have hsmall : |x-(k:ℝ)*Real.pi|≤Real.pi/2 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hlo',hhi',hc]
  have hx' := abs_le.mp hx
  have hkr : (-3:ℝ)<k ∧ (k:ℝ)<3 := by
    constructor <;> nlinarith only [hlo',hhi',hc,hx'.1,hx'.2,hp]
  have hkl : (-3:ℤ)<k := by exact_mod_cast hkr.1
  have hku : k<(3:ℤ) := by exact_mod_cast hkr.2
  have hk : k∈Finset.Icc (-2:ℤ) 2 := Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hsin : |Real.sin (x-(k:ℝ)*Real.pi)|=|Real.sin x| := by
    rw [Real.sin_sub_int_mul_pi]
    simp only [abs_mul,abs_zpow,abs_neg,abs_one,one_zpow,one_mul]
  have hb := Real.mul_abs_le_abs_sin hsmall
  rw [hsin] at hb
  have hm := mul_le_mul_of_nonneg_left (hb.trans hs) hp.le
  have hcancel : Real.pi*(2/Real.pi)=2 := by field_simp
  rw [← mul_assoc,hcancel] at hm
  exact ⟨k,hk,by nlinarith only [hm]⟩

end RadialAnglePeriodicCover
