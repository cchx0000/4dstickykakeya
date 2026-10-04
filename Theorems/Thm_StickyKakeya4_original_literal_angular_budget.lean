import Theorems.Thm_StickyKakeya4_original_literal_angular_readback
import Theorems.Thm_StickyKakeya4_native_scheduled_scale_selection
import Theorems.Thm_StickyKakeya4_native_quarter_scale_parameters
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalLiteralAngularBudget
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening NativeScheduledScaleSelection
/-- Increasing only the source regularity budget preserves the actual
 set, its mesh, exponent, and both bounds. -/
theorem point_AD_budget_mono {X : Type*} [PseudoMetricSpace X] (C : Finset X)
    {mesh K L kappa : ℝ} (hm : 0 < mesh) (hK : 0 < K) (hKL : K ≤ L)
    (H : ADBounds C mesh K kappa) : ADBounds C mesh L kappa := by
  intro c hc r hr hr1
  have hr0 : 0 < r := hm.trans_le hr
  have hp : 0 ≤ (r/mesh)^kappa := by positivity
  exact ⟨(div_le_div_of_nonneg_left hp hK hKL).trans (H c hc r hr hr1).1,
    (H c hc r hr hr1).2.trans (mul_le_mul_of_nonneg_right hKL hp)⟩
/-- The literal 192K² net loss fits the fourth power source budget after
 one fixed, exponent-independent numerical cutoff. -/
theorem literal_angular_cost_absorption {K : ℝ} (hK : 192 ≤ K) : 192*K^2 ≤ K^4 := by
  have hsq : (192:ℝ) ≤ K^2 := by nlinarith only [hK]
  have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg K)
  nlinarith only [hh]
/-- This cutoff is selected before the actual sets or their exponent.
 It turns the proved literal-cover net constant into the native power budget. -/
theorem exists_literal_angular_power_cutoff {eta : ℝ} (heta : 0 < eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ ∀ delta : ℝ,
      0 < delta → delta ≤ delta0 → 192*(delta^(-eta))^2 ≤ delta^(-(4*eta)) := by
  obtain ⟨d0,hd0,hd01,hcut⟩ := NativeQuarterScaleParameters.exists_small_power_cutoff heta
    (by norm_num : (0:ℝ)<1/192)
  refine ⟨d0,hd0,hd01,?_⟩
  intro delta hd hdd
  have hp : 0 < delta^eta := Real.rpow_pos_of_pos hd _
  have hsmall := hcut delta hd hdd
  have hK : 192 ≤ delta^(-eta) := by
    rw [Real.rpow_neg hd.le]
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hp).mpr
    nlinarith only [hsmall]
  have hh := literal_angular_cost_absorption hK
  have heq : (delta^(-eta))^4=delta^(-(4*eta)) := by
    rw [←Real.rpow_mul_natCast hd.le]
    congr 1
    ring
  exact hh.trans_eq heq
/-- The enlarged working eta uses an exact subsequence of the ORIGINAL
 scheduled scales, so no field law at an unscheduled scale is introduced. -/
theorem fourfold_schedule_readback (delta eta : ℝ) (n : ℕ) :
    scheduledScale delta (4*eta) n=scheduledScale delta eta (4*n) := by
  unfold scheduledScale
  congr 1
  push_cast
  ring
/-- Original scheduled field laws remain literal after the fourfold
 source-budget enlargement, including negative integer schedule indices. -/
theorem fourfold_scheduled_law {delta eta : ℝ} {law : ℝ → Prop}
    (H : ScheduledLaw delta eta law) : ScheduledLaw delta (4*eta) law := by
  intro k hlo hhi
  have heq : (4*eta)*(k:ℝ)=eta*((4*k:ℤ):ℝ) := by push_cast; ring
  rw [heq] at hlo hhi ⊢
  exact H (4*k) hlo hhi
end OriginalLiteralAngularBudget
