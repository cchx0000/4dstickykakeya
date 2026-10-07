import Theorems.Thm_StickyKakeya4_native_actual_XY_budget_allowance
import Theorems.Thm_StickyKakeya4_native_sharp_X_budget_actual
import Theorems.Thm_StickyKakeya4_native_actual_XY_budget_comparison

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativePaidThirdBudget
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeRetainedSliceCore
open NativeRetainedSliceBudgetSource NativeRetainedSliceBudgetCutoff NativeRetainedSliceBudgetFinal
open NativeActualXYBudgetComparison NativeThirdXYConstantComparison
open NativeRankExponentHierarchy NativeFixedCompactKakeyaExponent NativeAllTwoScaleConfiguration

open NativeSharpXPowerAlgebra NativeSharpXBudgetActual NativeSharpXBudgetCutoff
/-- Uniform raw allowance and all base X/XY/Y scalar payments on one L3.
The original first-stage factor remains an arbitrary actual source parameter. -/
def HasBudget (epsilon eta0 c : ℝ) (g K d J L3 : ℕ) (delta0 : ℝ) : Prop :=
      (∀(n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
        IsWangZakharovNativeFiniteInput D eta → D.thickness ≤ delta0 →
        0 ≤ eta → eta ≤ commonBudget eta0 c/32 →
        ∀original : Fin n → Finset Index,
          (∀i,D.shading i=wzCellShading (mesh D) original i) →
          ∀S : Finset (Fin n × Index),S⊆incidences original → S.Nonempty →
            (refinementCost (d+2) (J+1) L3:ℝ)*(NativeSourceSizeBounds.radix S.card L3:ℝ)^4 ≤
              D.thickness^(-(commonBudget eta0 c/4))) ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
        IsWangZakharovNativeFiniteInput D eta → D.thickness ≤ delta0 → 0 ≤ eta →
        ∀original : Fin n → Finset Index,
          (∀i,D.shading i=wzCellShading (mesh D) original i) →
          ∀S : Finset (Fin n × Index),S⊆incidences original → S.Nonempty →
          ∀F1 F2 G Q1 Q2 m : ℕ,0 < F1 → 0 < G → 1 ≤ Q1 → 0 < Q2 → G ≤ F2 → 6 ≤ m →
          ∀i : Fin 4,i.val+1 ≤ 3 →
          ∀zeta lambda b tau seed c2 r q : ℝ,
            eta ≤ seed/8 → 0 ≤ tau → tau ≤ commonBudget eta0 c/1024 →
            seed ≤ tau/16384 → zeta ≤ seed/256 → c2=commonBudget eta0 c/4 →
            (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-(seed/8)) →
            (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2) →
            0 < r → r ≤ 1 → r ≤ D.thickness^(cutoff c i) →
            lambda=r^(rankLoss eta0 c i)/(4*((g:ℝ)+1)) →
            r^((2*((i.val+1:ℕ):ℝ)+1)*rankLoss eta0 c i) ≤ b →
            0 < q → q ≤ 1 →
            1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4 →
            r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q →
            ((64:ℝ)/((2^m:ℕ):ℝ))^2 ≤ 6144*r →
            let F3 := refinementCost (d+2) (J+1) L3
            let Q3 := NativeSourceSizeBounds.radix S.card L3
            let rho := (64:ℝ)/((2^m:ℕ):ℝ)
            let w := min (boundaryWindow tau) ((tau/16)/1000)
            (F3:ℝ)*(Q3:ℝ)^4 ≤ D.thickness^(-(commonBudget eta0 c/4)) ∧
            actualRetainedConstant D.thickness eta zeta lambda b F1 G Q2 tau seed c2 w F3 Q3 q J m K
              (3-extremalExponent) ≤ rho^(-(epsilon/4)) ∧
            actualXYConstant D.thickness eta zeta lambda b tau seed c2 w q
              (NativeRetainedSliceBudgetAlgebra.quotientCost q) F1 G Q2 F3 Q3 J m K ≤ rho^(-(epsilon/2)) ∧
            NativeThirdXYFixedBudget.fixedCost ≤ rho^(-(epsilon/4)) ∧
            fiberCoefficient D.thickness eta zeta tau (seed/8) c2 lambda b F1 G Q2 F3 Q3 q (i.val+1) ≤
              rho^(-(epsilon/4))

/-- All numerical choices precede the source and the eventual coherent
pre-third subset. No coefficient target is an assumed input. -/
theorem exists_paid_third_budget (epsilon eta0 c : ℝ) (g K d J : ℕ)
    (he : 0 < epsilon) (he0 : 0 < eta0) (he01 : eta0 ≤ 1) (heSmall : eta0 ≤ epsilon/8192)
    (hc : 0 < c) (hcsmall : c ≤ 1/2)
    (hcQXY : c ≤ quotientTolerance (epsilon/4)/24)
    (hcQX : c ≤ quotientTolerance (epsilon/16)/24)
    (hJ : 0 < J) (hJloss : 3/(J:ℝ) ≤ epsilon/32) :
    ∃L3 : ℕ,0 < L3 ∧ ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      HasBudget epsilon eta0 c g K d J L3 delta0 := by
  have heQuarter : 0 < epsilon/4 := by positivity
  obtain ⟨L3,hL3,deltaXY,hdXY,hdXY1,Hraw,Hactual⟩ :=
    NativeActualXYBudgetAllowance.exists_actual_native_XY_budget_with_raw epsilon eta0 c g K d J
      he he0 he01 (by linarith only [heSmall,he]) hc hcsmall hcQXY hJ hJloss
  let deltaX := sourceCutoff (epsilon/4) c g heQuarter hc
  have hdX : 0 < deltaX := sourceCutoff_pos _ _ _ _ _
  let delta0 := min deltaXY deltaX
  refine ⟨L3,hL3,delta0,lt_min hdXY hdX,(min_le_left _ _).trans hdXY1,?_,?_⟩
  · intro n D eta h hsmall heta hetaSmall original horiginal S hS hSn
    exact Hraw n D eta h (hsmall.trans (min_le_left _ _)) heta hetaSmall original horiginal S hS hSn
  intro n D eta h hsmall heta original horiginal S hS hSn F1 F2 G Q1 Q2 m
    hF1 hG hQ1 hQ2 hGF hm6 i hell zeta lambda b tau seed c2 r q
    hetaSeed htau0 htau hseed hzeta hc2 H1 H2 hr hr1 hrdelta hlambda hb hq hq1 hgrid hqraw hscale
  obtain ⟨hthird,hret,hxy,hfixed⟩ := Hactual n D eta h (hsmall.trans (min_le_left _ _)) heta
    original horiginal S hS hSn F1 F2 G Q1 Q2 m hF1 hG hQ1 hQ2 hGF hm6 i hell
    zeta lambda b tau seed c2 r q hetaSeed htau0 htau hseed hzeta hc2 H1 H2 hr hr1 hrdelta hlambda hb
    hq hq1 hgrid hqraw hscale
  refine ⟨hthird,hret,hxy,hfixed,?_⟩
  have hQ3 : 1 ≤ NativeSourceSizeBounds.radix S.card L3 :=
    (by norm_num : 1 ≤ (4:ℕ)).trans (NativeSourceSizeBounds.radix_four_le _ _)
  have hcX : c ≤ quotientTolerance ((epsilon/4)/4)/24 := by
    simpa only [div_div,show (4:ℝ)*4=16 by norm_num] using hcQX
  exact actual_fiber_coefficient_le_power heQuarter he0 he01 (by linarith only [heSmall]) hc
    (hcsmall.trans (by norm_num)) hcX F1 F2 G Q1 Q2 (refinementCost (d+2) (J+1) L3)
    (NativeSourceSizeBounds.radix S.card L3) g m i hm6 hell h.1.2.1 (hsmall.trans (min_le_right _ _))
    heta hetaSeed (by linarith only [heta,hetaSeed]) hQ1 hQ3 hGF H1 H2 hthird
    htau0 htau hseed hzeta hc2 hr hr1 hrdelta hlambda hb hq hq1 hgrid hqraw hscale

end NativePaidThirdBudget
