import Theorems.Thm_StickyKakeya4_native_third_XY_fixed_budget
import Theorems.Thm_StickyKakeya4_native_retained_slice_budget_native

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000
noncomputable section
namespace NativeActualXYBudgetComparison
open NativeThirdXYData NativeThirdXYConstantComparison NativeThirdXYFixedBudget
open NativeRetainedSliceBudgetSource NativeRetainedSliceBudgetAlgebra
open NativeReferenceSliceBudgetAlgebra NativeParentHeightGraphCore NativeActivePhasePopulation
open NativeFixedCompactKakeyaExponent

/-- The literal fixed-coordinate XY constant on the same third incidence
core. Cpre is explicit; its base value quotientCost(q) is paid by the source. -/
def actualXYConstant (delta eta zeta lambda b tau seed c2 w _q Cpre : ℝ)
    (F1 G Q2 F3 Q3 J m K : ℕ) : ℝ :=
  let mu := population delta eta lambda b F1 G
  let eps := columnEpsilon delta lambda (seed/8) c2
  xyConstant delta zeta mu
    (profileLower delta mu eps tau (seed/8) w) (profileUpper delta eps tau)
    (mu/rowConstant) ((selectionCost K:ℝ)*Cpre*F3) Q2 Q3 J m

lemma base_XY_le_retained {delta eta zeta lambda b tau seed c2 w q : ℝ}
    (F1 G Q2 F3 Q3 J m K : ℕ)
    (hd : 0 < delta) (hlambda : 0 < lambda) (hb : 0 < b)
    (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2) (hF3 : 0 < F3) (hQ3 : 0 < Q3)
    (hq : 0 < q) :
    actualXYConstant delta eta zeta lambda b tau seed c2 w q (quotientCost q) F1 G Q2 F3 Q3 J m K ≤
      geometryCost*actualRetainedConstant delta eta zeta lambda b F1 G Q2 tau seed c2 w F3 Q3 q J m K
        (3-extremalExponent) := by
  have hmu : 0 < population delta eta lambda b F1 G := by unfold population; positivity
  have heps : 0 < columnEpsilon delta lambda (seed/8) c2 := by unfold columnEpsilon; positivity
  have hCmp := NativeAnisotropicGlobalSourceBridge.comparisonCost_pos
  have hRow := rowConstant_pos
  have hGraph := NativeRetainedSliceBudgetExtra.graphCost_pos K
  have hQuot := quotientCost_pos hq
  have hPL : 0 < profileLower delta (population delta eta lambda b F1 G)
      (columnEpsilon delta lambda (seed/8) c2) tau (seed/8) w := by unfold profileLower; positivity
  have hPU : 0 < profileUpper delta (columnEpsilon delta lambda (seed/8) c2) tau := by
    unfold profileUpper
    positivity
  exact xyConstant_le_retained Q2 Q3 J m hd hmu hPL hPU (div_pos hmu hRow)
    (by positivity) hQ2 hQ3

end NativeActualXYBudgetComparison
