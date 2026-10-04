import Theorems.Thm_StickyKakeya4_native_original_pruned_mass
import Theorems.Thm_StickyKakeya4_native_original_log_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeDyadicPruningCutoff
open StickyKakeya4 NativeOriginalPrunedMass NativeOriginalLogBudget

lemma dyadic_depth_log {delta : ℝ} (level : ℕ) (hdelta : delta=(2:ℝ)⁻¹^level) :
    (level:ℝ)+1=1+(-Real.log delta)/Real.log 2 := by
  have hlog : Real.log delta= -(level:ℝ)*Real.log 2 := by
    rw [hdelta,Real.log_pow,Real.log_inv]
    ring
  rw [hlog]
  have hl : Real.log 2≠0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  field_simp
  ring

/-- Choose the original-delta cutoff before the finite source. It absorbs the
actual dyadic number of levels, chart reach, and the true tube-volume upper
constant. Source eta at most zeta/16 pays for both tube and shading retention. -/
theorem exists_dyadic_pruning_cutoff {C L zeta : ℝ}
    (hC : 0<C) (hL : 0<L) (hzeta : 0<zeta) :
    ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧ ∀ (delta eta : ℝ) (level : ℕ),
      0<delta → delta≤delta0 → delta=(2:ℝ)⁻¹^level → eta≤zeta/16 →
      delta^zeta*L^3≤1 ∧
      2*(2*C*(level+1)*delta^(zeta-2*eta-3))≤delta^(eta-3) ∧
      2*(2*C*(level+1)*delta^(zeta-2*eta-3))*volumeConstant*delta^3≤
        delta^(2*eta+zeta/16) := by
  let A := 4*C*max 1 volumeConstant
  have hA : 0≤A := by dsimp [A]; positivity
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨dlog,hdlog,hdlog1,hlog⟩ := exists_logarithmic_budget_cutoff
    (show 0<zeta/4 by positivity) hA (show 0≤A/Real.log 2 by positivity)
  obtain ⟨dchart,hdchart,_hdchart1,hchart⟩ := exists_positive_rpow_absorption_threshold
    hzeta (show 0≤L^3 by positivity) (show (0:ℝ)<1 by norm_num)
  refine ⟨min dlog dchart,lt_min hdlog hdchart,(min_le_left _ _).trans hdlog1,?_⟩
  intro delta eta level hd hsmall hdy heta
  have hdlog' := hsmall.trans (min_le_left dlog dchart)
  have hdchart' := hsmall.trans (min_le_right dlog dchart)
  have hd1 := hdlog'.trans hdlog1
  have hbudget : A*((level:ℝ)+1)≤delta^(-zeta/4) := by
    have hh := hlog delta hd hdlog'
    rw [dyadic_depth_log level hdy]
    convert hh using 1 <;> ring
  have hA1 : 4*C≤A := by
    dsimp [A]
    nlinarith [le_max_left (1:ℝ) volumeConstant]
  have hAV : 4*C*volumeConstant≤A := by
    exact mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) volumeConstant) (by positivity)
  have hc : 4*C*((level:ℝ)+1)≤delta^(-zeta/4) :=
    (mul_le_mul_of_nonneg_right hA1 (by positivity)).trans hbudget
  have hcv : 4*C*volumeConstant*((level:ℝ)+1)≤delta^(-zeta/4) :=
    (mul_le_mul_of_nonneg_right hAV (by positivity)).trans hbudget
  refine ⟨by simpa only [mul_comm] using hchart delta hd hdchart',?_,?_⟩
  · calc
      _ = (4*C*((level:ℝ)+1))*delta^(zeta-2*eta-3) := by ring
      _ ≤ delta^(-zeta/4)*delta^(zeta-2*eta-3) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_pos_of_pos hd _).le
      _ = delta^(3*zeta/4-2*eta-3) := by rw [←Real.rpow_add hd]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
  · calc
      _ = (4*C*volumeConstant*((level:ℝ)+1))*(delta^(zeta-2*eta-3)*delta^3) := by ring
      _ = (4*C*volumeConstant*((level:ℝ)+1))*delta^(zeta-2*eta) := by
        rw [←Real.rpow_natCast delta 3,←Real.rpow_add hd]
        congr 2
        ring
      _ ≤ delta^(-zeta/4)*delta^(zeta-2*eta) :=
        mul_le_mul_of_nonneg_right hcv (Real.rpow_pos_of_pos hd _).le
      _ = delta^(3*zeta/4-2*eta) := by rw [←Real.rpow_add hd]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)

end NativeDyadicPruningCutoff
