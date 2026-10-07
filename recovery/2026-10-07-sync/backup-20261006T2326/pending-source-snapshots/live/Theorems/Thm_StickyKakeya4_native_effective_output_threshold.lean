import Theorems.Thm_StickyKakeya4_native_coarse_native_admissibility
import Theorems.Thm_StickyKakeya4_native_quarter_scale_parameters

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeEffectiveOutputThreshold
open NativeCoarsePowerWindow NativeCoarseRelativeCW NativeCoarseMassBudget
open NativeQuarterScaleParameters

/-- Internal pruning threshold determined by the actual output scale.
The input source and all fixed accuracy parameters have already been chosen. -/
def exponent (epsilon Delta e : ℝ) : ℝ :=
  (e/16)*(Real.log Delta/Real.log epsilon)

/-- The same formula pays every threshold power exactly at the output
scale. It does not replace epsilon by Delta in a source predicate. -/
theorem power_readback {epsilon Delta : ℝ} (heps : 0 < epsilon)
    (heps1 : epsilon < 1) (hDelta : 0 < Delta) (e k : ℝ) :
    epsilon^(k*exponent epsilon Delta e) = Delta^(k*e/16) := by
  have hn : Real.log epsilon ≠ 0 := ne_of_lt (Real.log_neg heps heps1)
  rw [Real.rpow_def_of_pos heps, Real.rpow_def_of_pos hDelta]
  congr 1
  unfold exponent
  field_simp [hn]

/-- One fixed lower exponent works for every allowed output scale.
The proof uses the actual power-window inequality and its negative log. -/
theorem fixed_lower_bound {epsilon Delta window e : ℝ}
    (heps : 0 < epsilon) (heps1 : epsilon < 1) (hDelta : 0 < Delta)
    (he : 0 ≤ e) (hwindow : Delta ≤ epsilon^window) :
    window*e/16 ≤ exponent epsilon Delta e := by
  have hlogneg : Real.log epsilon < 0 := Real.log_neg heps heps1
  have hh := Real.log_le_log hDelta hwindow
  rw [Real.log_rpow heps] at hh
  have hratio : window ≤ Real.log Delta/Real.log epsilon :=
    (le_div_iff_of_neg hlogneg).mpr (by simpa only [mul_comm] using hh)
  unfold exponent
  have hp := mul_le_mul_of_nonneg_left hratio
    (show (0:ℝ) ≤ e/16 from div_nonneg he (by norm_num))
  calc
    window*e/16 = (e/16)*window := by ring
    _ ≤ _ := hp

/-- Choosing an output above the reference mesh bounds the effective
exponent above as well; no source-dependent constant is made uniform. -/
theorem fixed_upper_bound {epsilon Delta e : ℝ}
    (heps : 0 < epsilon) (heps1 : epsilon < 1) (he : 0 ≤ e)
    (hwindow : epsilon ≤ Delta) : exponent epsilon Delta e ≤ e/16 := by
  have hlogneg : Real.log epsilon < 0 := Real.log_neg heps heps1
  have hh := Real.log_le_log heps hwindow
  have hratio : Real.log Delta/Real.log epsilon ≤ 1 :=
    (div_le_iff_of_neg hlogneg).mpr (by simpa using hh)
  unfold exponent
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio (div_nonneg he (by norm_num))

/-- Fixed constants, including the real retention payment, are paid by one
output cutoff chosen before ANY source or output scale. -/
theorem exists_output_cutoff (e : ℝ) (he : 0 < e) :
    ∃Delta0 : ℝ,0 < Delta0 ∧ Delta0 ≤ 1/64 ∧
      ∀Delta F : ℝ,0 < Delta → Delta ≤ Delta0 → 0 ≤ F → F ≤ Delta^(-(e/32)) →
        (43*F*colorCost)*Delta^(e/16) ≤ 1 ∧
        10077696*Delta^(e/2) ≤ 1 ∧
        densityCost*Delta^(e/16) ≤ 1 ∧ cwCost*Delta^(e/16) ≤ 1 := by
  let C : ℝ := max (43*colorCost) (max 10077696 (max densityCost cwCost))
  have hC : 0 < C := lt_of_lt_of_le (mul_pos (by norm_num) colorCost_pos) (le_max_left _ _)
  obtain ⟨d0,hd0,_hd01,H⟩ := exists_small_power_cutoff
    (show 0 < e/32 by positivity) (show 0 < 1/C by positivity)
  refine ⟨min (1/64) d0,lt_min (by norm_num) hd0,min_le_left _ _,?_⟩
  intro Delta F hD hsmall hF hFupper
  have hD1 : Delta ≤ 1 := (hsmall.trans (min_le_left _ _)).trans (by norm_num)
  have hbase : C*Delta^(e/32) ≤ 1 := by
    have hh := (le_div_iff₀ hC).mp (H Delta hD (hsmall.trans (min_le_right _ _)))
    simpa only [mul_comm] using hh
  have hpay (c t : ℝ) (hc : 0 ≤ c) (hcC : c ≤ C) (ht : e/32 ≤ t) :
      c*Delta^t ≤ 1 :=
    (mul_le_mul hcC (Real.rpow_le_rpow_of_exponent_ge hD hD1 ht)
      (Real.rpow_nonneg hD.le t) hC.le).trans hbase
  refine ⟨?_,hpay _ _ (by norm_num)
    ((le_max_left 10077696 (max densityCost cwCost)).trans (le_max_right (43*colorCost) _))
    (by linarith only [he]),?_,?_⟩
  · calc
      (43*F*colorCost)*Delta^(e/16) ≤
          (43*Delta^(-(e/32))*colorCost)*Delta^(e/16) := by
            gcongr
            exact colorCost_pos.le
      _ = (43*colorCost)*Delta^(e/32) := by
        rw [mul_assoc (43:ℝ) _ colorCost, mul_comm (Delta^(-(e/32))) colorCost,
          ←mul_assoc, mul_assoc, ←Real.rpow_add hD]
        congr 2
        ring
      _ ≤ 1 := hpay _ _ (mul_pos (by norm_num) colorCost_pos).le (le_max_left _ _) le_rfl
  · apply hpay _ _ densityCost_pos.le
    · exact (le_max_left densityCost cwCost).trans ((le_max_right 10077696 _).trans (le_max_right _ _))
    · linarith only [he]
  · apply hpay _ _ cwCost_pos.le
    · exact (le_max_right densityCost cwCost).trans ((le_max_right 10077696 _).trans (le_max_right _ _))
    · linarith only [he]

end NativeEffectiveOutputThreshold
