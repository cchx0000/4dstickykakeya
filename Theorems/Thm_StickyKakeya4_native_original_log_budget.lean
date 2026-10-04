import Theorems.Thm_StickyKakeya4_native_quarter_scale_parameters
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeOriginalLogBudget
open NativeQuarterScaleParameters
/-- An explicit positive original-delta cutoff absorbs fixed logarithmic
 losses into any positive power. No eventual-smallness premise is assumed. -/
theorem exists_logarithmic_budget_cutoff {a C0 C1 : ℝ}
    (ha : 0 < a) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ ∀ delta : ℝ,
      0 < delta → delta ≤ delta0 → C0+C1*(-Real.log delta) ≤ delta^(-a) := by
  let r := a/2
  let B := C1/r
  let Q := 1+C0+B
  have hr : 0 < r := by dsimp [r]; positivity
  have hB : 0 ≤ B := div_nonneg hC1 hr.le
  have hQ : 0 < Q := by dsimp [Q]; positivity
  obtain ⟨d0,hd0,hd01,hcut⟩ := exists_small_power_cutoff hr (div_pos (by norm_num : (0:ℝ)<1) hQ)
  refine ⟨d0,hd0,hd01,?_⟩
  intro delta hd hdelta
  let t := delta^(-r)
  have ht : 0 < t := Real.rpow_pos_of_pos hd _
  have hsmall := hcut delta hd hdelta
  have hQt : Q ≤ t := by
    have hh := (le_div_iff₀ hQ).mp hsmall
    have hqinv : Q ≤ 1/delta^r := (le_div_iff₀ (Real.rpow_pos_of_pos hd r)).mpr (by nlinarith only [hh])
    simpa only [t,Real.rpow_neg hd.le,one_div] using hqinv
  have hlog := Real.log_le_sub_one_of_pos ht
  rw [Real.log_rpow hd] at hlog
  have hneglog : -Real.log delta ≤ t/r := (le_div_iff₀ hr).mpr (by nlinarith only [hlog])
  have hlinear : C0+C1*(-Real.log delta) ≤ C0+B*t := by
    have hh := mul_le_mul_of_nonneg_left hneglog hC1
    calc
      _ ≤ C0+C1*(t/r) := by linarith only [hh]
      _ = _ := by dsimp [B]; ring
  have hquadratic : C0+B*t ≤ t^2 := by
    have ht1 : 1 ≤ t := by dsimp [Q] at hQt; linarith only [hQt,hC0,hB]
    have hh := mul_le_mul_of_nonneg_right hQt ht.le
    have hC := mul_nonneg hC0 (sub_nonneg.mpr ht1)
    dsimp [Q] at hh
    nlinarith only [hh,hC,ht]
  have hid : t^2=delta^(-a) := by
    dsimp [t,r]
    rw [← Real.rpow_natCast,← Real.rpow_mul hd.le]
    congr 1
    norm_num
  exact hlinear.trans (hquadratic.trans_eq hid)
/-- The actual projection scale menu has a fixed original-delta logarithmic
 envelope at the proved balanced quarter-scale radius. -/
theorem projection_menu_log_envelope {delta rho N : ℝ} (hd : 0 < delta)
    (hrho : delta^(1/2:ℝ) ≤ rho)
    (hN : N ≤ Real.log (2/rho)/Real.log 2+2) :
    N ≤ 3+(1/(2*Real.log 2))*(-Real.log delta) := by
  have hr : 0 < rho := (Real.rpow_pos_of_pos hd (1/2:ℝ)).trans_le hrho
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : 2/rho ≤ 2/delta^(1/2:ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hd _) hrho
  have hl := Real.log_le_log (div_pos (by norm_num : (0:ℝ)<2) hr) hdiv
  rw [Real.log_div (by norm_num : (2:ℝ)≠0) (Real.rpow_pos_of_pos hd _).ne',Real.log_rpow hd] at hl
  have hh := div_le_div_of_nonneg_right hl hlog2.le
  have hid : (Real.log 2-(1/2:ℝ)*Real.log delta)/Real.log 2+2=
      3+(1/(2*Real.log 2))*(-Real.log delta) := by field_simp; ring
  have hh2 : Real.log (2/rho)/Real.log 2+2 ≤ (Real.log 2-(1/2:ℝ)*Real.log delta)/Real.log 2+2 := by
    linarith only [hh]
  exact hN.trans (hh2.trans_eq hid)
/-- Hence the selected finite projection scale count fits the ORIGINAL
 power budget delta^-a after a constructed smallness cutoff. -/
theorem exists_projection_menu_budget_cutoff {a : ℝ} (ha : 0 < a) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ ∀ delta rho N : ℝ,
      0 < delta → delta ≤ delta0 → delta^(1/2:ℝ) ≤ rho →
      N ≤ Real.log (2/rho)/Real.log 2+2 → N ≤ delta^(-a) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨d0,hd0,hd01,hcut⟩ := exists_logarithmic_budget_cutoff ha
    (by norm_num : (0:ℝ)≤3) (by positivity : (0:ℝ)≤1/(2*Real.log 2))
  exact ⟨d0,hd0,hd01,fun delta rho N hd hsmall hr hN =>
    (projection_menu_log_envelope hd hr hN).trans (hcut delta hd hsmall)⟩
end NativeOriginalLogBudget
