import Theorems.Thm_StickyKakeya4_native_configured_dyadic_matching
import Theorems.Thm_StickyKakeya4_native_squared_grain_queries

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeConfiguredHistoryMatching
open StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeJointUniformCoarseRelations NativeAllTwoScaleConfiguration NativeMiddleWindowBalance
open NativeActualMesoscopicRankConfiguration
open NativeSquaredGrainQueries NativeConfiguredDyadicMatching

/-- The real mesoscopic menu and retained-history depth supply the strong
quarter-depth condition before the actual local-source thickness is read.
No replacement of the relative fine thickness by the XY mesh occurs. -/
theorem actual_history_matching {n : ℕ} {D : FiniteScaleSource n} {eta tau a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau)
    (g level J u : ℕ) (schedule : Fin (g + 1) → Fin (level + 1))
    (hschedule : schedule = fullSchedule tau htau g level) (j : Fin (g + 1))
    (hj : j ∈ NativeRankMesoscopicRadiusMenu.menu (rankWindow tau) (rankWindow_pos htau).le g level)
    (selected : Fin J) (R : Finset (Fin n)) (Eref : Finset (Fin n × Index)) (p : Parent)
    (hdy : D.thickness = (2 : ℝ)⁻¹ ^ level)
    (hcfg : 64 / ((2 ^ (grainDepth J (schedule j).val selected.succ) : ℕ) : ℝ) ≤ (2 : ℝ)⁻¹ ^ u) :
    let m := grainDepth J (schedule j).val selected.succ
    u + 12 ≤ m + 6 ∧ u + 12 ≤ level - m + 6 ∧
      ((2 ^ (u + 12) : ℕ) : ℝ) * (NativeLocalParentSource.source h R Eref a m p).thickness ≤ 1 ∧
      (2 : ℝ)⁻¹ ^ u / 512 = 8 / ((2 ^ (u + 12) : ℕ) : ℝ) ∧
      64 / ((2 ^ (u + 12) : ℕ) : ℝ) = (2 : ℝ)⁻¹ ^ u / 64 ∧
      3 * (64 / ((2 ^ m : ℕ) : ℝ)) ≤ 12288 / ((2 ^ (u + 12) : ℕ) : ℝ) := by
  let m := grainDepth J (schedule j).val selected.succ
  have hquarter : m ≤ level / 4 :=
    (grainDepth_bounds J (schedule j).val selected.succ).2.trans
      (stopping_depth_cap htau g level schedule hschedule j hj)
  simpa only [NativeLocalParentSource.source_thickness] using
    match_actual_scales level m u hdy hquarter hcfg

/-- The same actual quarter-depth history also reaches every original
population query needed by the second full-source AD/CW reader. This is
stronger than merely fitting inside the local shading depth. -/
theorem actual_history_population_depth {tau : ℝ} (htau : 0 < tau)
    (g level J u : ℕ) (schedule : Fin (g + 1) → Fin (level + 1))
    (hschedule : schedule = fullSchedule tau htau g level) (j : Fin (g + 1))
    (hj : j ∈ NativeRankMesoscopicRadiusMenu.menu (rankWindow tau) (rankWindow_pos htau).le g level)
    (selected : Fin J)
    (hcfg : 64 / ((2 ^ (grainDepth J (schedule j).val selected.succ) : ℕ) : ℝ) ≤ (2 : ℝ)⁻¹ ^ u) :
    grainDepth J (schedule j).val selected.succ + (u + 12) ≤ level := by
  let m := grainDepth J (schedule j).val selected.succ
  have hquarter : m ≤ level / 4 :=
    (grainDepth_bounds J (schedule j).val selected.succ).2.trans
      (stopping_depth_cap htau g level schedule hschedule j hj)
  have hu : u + 6 ≤ m := configured_depth_le m u hcfg
  change m + (u + 12) ≤ level
  omega

end NativeConfiguredHistoryMatching
