import Theorems.Thm_StickyKakeya4_native_output_alignment_menu_budget
import Theorems.Thm_StickyKakeya4_native_quarter_scale_parameters

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
noncomputable section
namespace NativeAlignmentScaleMenuBudget
open NativeOutputAlignmentMenuBudget NativeQuarterScaleParameters

/-- Charge the actual common-scale menu at the LATER alignment output amplification*ratio.
The caller must identify ratio with its actual absolute or normalized scale.
The positive chi is fixed first, then the requested menu loss and cutoff.
Only the original hierarchy costs are allowed to shrink after chi is known;
this theorem does not replace the Y-retention exponent by zeta/chi. -/
theorem exists_refined_menu_cutoff (chi loss : ℝ) (hchi : 0 < chi)
    (hloss : 0 < loss) (Ns : ℕ) (amplification : ℝ) (hAmp : 0 < amplification) :
    ∃deltaY0 : ℝ,0 < deltaY0 ∧ deltaY0 ≤ 1 ∧ ∀u : ℕ,
      (2:ℝ)⁻¹^(u+9) ≤ deltaY0 → ∀ratio : ℝ,0 < ratio →
      ratio ≤ ((2:ℝ)⁻¹^(u+9))^chi →
      (2:ℝ)*((u:ℝ)+10)^2*((Ns:ℝ)+1) ≤ (amplification*ratio)^(-loss) := by
  have hp : 0 < chi*loss/2 := by positivity
  obtain ⟨dm,hdm,hdm1,HM⟩ := exists_menu_cutoff (chi*loss/2) hp Ns
  obtain ⟨dc,hdc,_hdc1,HC⟩ := exists_small_power_cutoff
    (show 0 < chi/2 by positivity) (show (0:ℝ) < 1/amplification by positivity)
  refine ⟨min (dm/8) dc,lt_min (by positivity) hdc,?_,?_⟩
  · have hh := min_le_left (dm/8) dc
    linarith only [hh,hdm1]
  intro u hsmall ratio hratio hr
  let d : ℝ := (2:ℝ)⁻¹^(u+9)
  have hd : 0 < d := by dsimp [d]; positivity
  have hid : (2:ℝ)⁻¹^(u+6)=8*d := by
    dsimp [d]
    rw [show u+9=(u+6)+3 by omega,pow_add]
    norm_num
    ring
  have hbase : (2:ℝ)⁻¹^(u+6) ≤ dm := by
    rw [hid]
    have hh := hsmall.trans (min_le_left _ _)
    linarith only [hh]
  have hm := HM u hbase
  rw [hid] at hm
  have hhalf := HC d hd (hsmall.trans (min_le_right _ _))
  have heq : d^(chi/2)*d^(chi/2)=d^chi := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  have hproduct : amplification*d^chi ≤ d^(chi/2) := by
    have hh : amplification*d^(chi/2) ≤ 1 := by
      have h := (le_div_iff₀ hAmp).mp hhalf
      simpa only [mul_comm] using h
    have hmul := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hd.le (chi/2))
    rw [←heq]
    nlinarith only [hmul]
  have hwindow : amplification*ratio ≤ d^(chi/2) :=
    (mul_le_mul_of_nonneg_left hr hAmp.le).trans hproduct
  have htransfer := Real.rpow_le_rpow_of_nonpos (show 0 < amplification*ratio by positivity)
    hwindow (neg_nonpos.mpr hloss.le)
  have hpower : (d^(chi/2))^(-loss)=d^(-(chi*loss/2)) := by
    rw [←Real.rpow_mul hd.le]
    congr 1
    ring
  rw [hpower] at htransfer
  exact hm.trans ((Real.rpow_le_rpow_of_nonpos hd
    (show d ≤ 8*d by linarith only [hd]) (neg_nonpos.mpr hp.le)).trans htransfer)

end NativeAlignmentScaleMenuBudget
