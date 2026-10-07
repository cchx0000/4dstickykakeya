import Theorems.Thm_StickyKakeya4_native_retained_slice_budget_extra
import Theorems.Thm_StickyKakeya4_native_small_loss_parent_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000

noncomputable section
namespace NativeRetainedSliceBudgetSource
open NativeReferenceSliceBudgetAlgebra NativeReferenceColumnExponents NativeReferenceSliceBudgetSource
open NativeRetainedSliceBudgetAlgebra NativeRetainedSliceBudgetExtra NativeParentHeightGraphCore
open NativeActivePhasePopulation NativeSquaredGrainQueries NativeRankExponentHierarchy

/-- Literal constant returned by the one retained grain/point/class core. -/
def actualRetainedConstant (delta eta zeta lambda b F G Q tau seed c2 w F3 Q3 q : ℝ)
    (J m K : ℕ) (s : ℝ) : ℝ :=
  let mu := population delta eta lambda b F G
  let eps := columnEpsilon delta lambda (seed/8) c2
  let L := lowerCountCoefficient delta zeta mu (profileUpper delta eps tau)
  let U := upperCountCoefficient delta zeta (profileLower delta mu eps tau (seed/8) w)
  let B : ℝ := max 8 (((2^((phaseDepth m-m)/J+1):ℕ):ℝ))
  NativeSliceADConstant.constant
    ((mu/rowConstant)*(L/U)/(((selectionCost K:ℝ)*quotientCost q*F3)*Q^2*Q3^4))
    (Q^4*U/L) B s

lemma actualRetainedConstant_le {delta eta zeta lambda b F G Q tau seed c2 w F3 Q3 q s : ℝ}
    (J m K : ℕ) (hd : 0 < delta) (hlambda : 0 < lambda) (hb : 0 < b)
    (hF : 0 < F) (hG : 0 < G) (hQ : 1 ≤ Q) (hF3 : 0 < F3) (hQ3 : 0 < Q3) (hq : 0 < q) :
    actualRetainedConstant delta eta zeta lambda b F G Q tau seed c2 w F3 Q3 q J m K s ≤
      actualConstant delta eta zeta lambda b F G Q tau seed c2 w J m s *
        max 1 (extraCoefficient delta eta lambda b F G F3 Q3 q K) := by
  have hmu : 0 < population delta eta lambda b F G := by unfold population; positivity
  have heps : 0 < columnEpsilon delta lambda (seed/8) c2 := by unfold columnEpsilon; positivity
  have hCmp := NativeAnisotropicGlobalSourceBridge.comparisonCost_pos
  have hRow := rowConstant_pos
  have hPL : 0 < profileLower delta (population delta eta lambda b F G)
      (columnEpsilon delta lambda (seed/8) c2) tau (seed/8) w := by unfold profileLower; positivity
  have hPU : 0 < profileUpper delta (columnEpsilon delta lambda (seed/8) c2) tau := by
    unfold profileUpper
    positivity
  obtain ⟨hL,hU⟩ := count_coefficients_pos (zeta:=zeta) hd hmu hPL hPU
  exact retained_constant_le_reference hL hU hQ
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<8) (le_max_left _ _))
    (by positivity) (graphCost_pos K) (quotientCost_pos hq) hF3 hQ3

def quotientTolerance (epsilon : ℝ) : ℝ := min 1 (epsilon/16)

lemma quotientTolerance_bounds {epsilon : ℝ} (he : 0 < epsilon) :
    0 < quotientTolerance epsilon ∧ quotientTolerance epsilon ≤ 1 ∧ quotientTolerance epsilon ≤ epsilon/16 := by
  exact ⟨lt_min (by norm_num) (by positivity),min_le_left _ _,min_le_right _ _⟩

/-- The actual radius-grid test pays the quotient cost. The auxiliary menu
parameter is zero, so the factory's tau≤t/1024 already suffices. -/
lemma actual_quotient_test {delta r q eta0 c tau epsilon : ℝ}
    (hd : 0 < delta) (hr : 0 < r) (hr1 : r ≤ 1) (he : 0 < epsilon)
    (he0 : 0 ≤ eta0) (he01 : eta0 ≤ 1) (heSmall : eta0 ≤ epsilon/336)
    (hc : 0 < c) (hc1 : c ≤ 1) (hcSmall : c ≤ quotientTolerance epsilon/24)
    (i : Fin 4) (hrdelta : r ≤ delta^(cutoff c i)) (htau : 0 ≤ tau) (g : ℕ)
    (hTau : tau ≤ commonBudget eta0 c/1024)
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hq : r^(2*c)/(2*delta^(-(1/(g:ℝ)))) ≤ q) :
    r^(quotientTolerance epsilon/6)/2 ≤ q := by
  have hsmall : eta0 ≤ quotientTolerance epsilon := le_min he01 (by linarith only [heSmall,he])
  have hTau' : tau ≤ commonBudget eta0 c/(1000*((0:ℝ)+1)) := by
    have ht : 0 ≤ commonBudget eta0 c := by unfold commonBudget; positivity
    norm_num
    linarith only [hTau,ht]
  exact NativeSmallLossParentBudget.actual_test_radius_small_loss hd hr hr1
    (quotientTolerance_bounds he).1 he0 hsmall hc hc1 hcSmall i hrdelta htau g 0
    (by simpa only [Nat.cast_zero] using hTau') hgrid hq

end NativeRetainedSliceBudgetSource
