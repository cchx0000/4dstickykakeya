import Theorems.Thm_StickyKakeya4_native_middle_window_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

noncomputable section
namespace NativeEarlyWindowSuccessor
open Classical Finset NativeFixedSizeScaleMenu NativeScaleMenuSuccessor NativeMiddleWindowBalance

/-- The same fixed clipped schedule covers every depth in the first half
of the original scale range. Below its first point, the clipping cost is w;
elsewhere the finer-menu gap is at most1/g, already smaller than w. -/
theorem exists_early_successor (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g level f : ℕ) (hg : 0 < g) (hgrid : 1/(g:ℝ) < w/4) (hgl : g ≤ level)
    (hhalf : (f:ℝ) ≤ (level:ℝ)/2) :
    ∃j : Fin (g+1), f ≤ (windowSchedule w hw.le g level j).val ∧
      (((windowSchedule w hw.le g level j).val-f:ℕ):ℝ) ≤ w*(level:ℝ) := by
  have hlarge := large_level_of_grid w hw g level hg hgrid hgl
  have hl : 0 < level := hg.trans_le hgl
  have hln : (0:ℝ) ≤ level := Nat.cast_nonneg _
  have hupper : f ≤ upperDepth w level := by
    apply Nat.le_floor
    have hh := mul_le_mul_of_nonneg_right hwsmall.le hln
    nlinarith only [hhalf,hh,hln]
  by_cases hlo : f ≤ lowerDepth w level
  · refine ⟨0,?_,?_⟩
    · rwa [windowSchedule_zero w hw hwsmall g level hlarge]
    · rw [windowSchedule_zero w hw hwsmall g level hlarge]
      have hceil := (Nat.ceil_lt_add_one (show 0 ≤ (w/2)*(level:ℝ) by positivity)).le
      calc
        _ ≤ (lowerDepth w level:ℝ) := by exact_mod_cast Nat.sub_le (lowerDepth w level) f
        _ ≤ _ := by
          change (⌈(w/2)*(level:ℝ)⌉₊:ℝ) ≤ _
          nlinarith only [hceil,hlarge]
  · obtain ⟨j,hfj,_hgap,hgapR⟩ := exists_clipped_successor g level (lowerDepth w level)
      (upperDepth w level) f hg hl (upperDepth_le w hw.le level) (by omega) hupper
    refine ⟨j,hfj,hgapR.trans ?_⟩
    calc
      _ = (1/(g:ℝ))*(level:ℝ) := by ring
      _ ≤ (w/4)*(level:ℝ) := mul_le_mul_of_nonneg_right hgrid.le hln
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hw]) hln

theorem exists_early_successor_power {delta : ℝ} (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g level f : ℕ) (hg : 0 < g) (hgrid : 1/(g:ℝ) < w/4) (hgl : g ≤ level)
    (hhalf : (f:ℝ) ≤ (level:ℝ)/2) (hdy : delta=(2:ℝ)⁻¹^level) :
    ∃j : Fin (g+1), f ≤ (windowSchedule w hw.le g level j).val ∧
      ((2^((windowSchedule w hw.le g level j).val-f):ℕ):ℝ) ≤ delta^(-w) := by
  obtain ⟨j,hfj,hgap⟩ := exists_early_successor w hw hwsmall g level f hg hgrid hgl hhalf
  exact ⟨j,hfj,NativeLocalMenuInterpolation.dyadic_gap_power hdy hgap⟩

end NativeEarlyWindowSuccessor
