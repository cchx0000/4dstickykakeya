import Theorems.Thm_StickyKakeya4_native_paid_third_budget
import Theorems.Thm_StickyKakeya4_native_XY_pre_loss_budget
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data
import Theorems.Thm_StickyKakeya4_native_quotient_constant_bound

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
noncomputable section
namespace NativePaidThirdReadback
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeRetainedSliceCore
open NativePaidThirdBudget NativeActualXYBudgetComparison NativeXYPreLossBudget
open NativeThirdXYData NativeThirdXYSourceData NativeEncodedQuotientAD NativeQuotientConstantBound
open NativeSharpXPowerAlgebra NativeRetainedSliceBudgetAlgebra NativeReferenceSliceBudgetAlgebra
open NativeRankExponentHierarchy NativeFixedCompactKakeyaExponent NativeAllTwoScaleConfiguration
open NativeActivePhasePopulation NativeParentHeightGraphCore NativeRetainedSliceBudgetExtra
open NativeSourceParentGrainCleanup NativeActualProjectedGrainCount NativeActualRichPacketLayers
open NativeThirdXYFixedBudget

/-- Pay the literal XY and quotient constants from the uniform budget that
was chosen before D. Every extra pre-third coherence loss remains explicit. -/
theorem constants_from_budget {epsilon eta0 c delta0 : ℝ} {g K d J L3 n : ℕ}
    {D : FiniteScaleSource n} {eta : ℝ}
    (Hbudget : HasBudget epsilon eta0 c g K d J L3 delta0) (he : 0 < epsilon)
    (h : IsWangZakharovNativeFiniteInput D eta) (hsmall : D.thickness ≤ delta0) (heta : 0 ≤ eta)
    (original : Fin n → Finset Index) (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (S : Finset (Fin n × Index)) (hS : S⊆incidences original) (hSn : S.Nonempty)
    (F1 F2 G Q1 Q2 m : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ1 : 1 ≤ Q1) (hQ2 : 0 < Q2)
    (hGF : G ≤ F2) (hm6 : 6 ≤ m) (i : Fin 4) (hi : 1 ≤ i.val) (hell : i.val+1 ≤ 3)
    (zeta lambda b tau seed c2 r q : ℝ)
    (hetaSeed : eta ≤ seed/8) (htau0 : 0 ≤ tau) (htau : tau ≤ commonBudget eta0 c/1024)
    (hseed : seed ≤ tau/16384) (hzeta : zeta ≤ seed/256) (hc2 : c2=commonBudget eta0 c/4)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2))
    (hr : 0 < r) (hr1 : r ≤ 1) (hrdelta : r ≤ D.thickness^(cutoff c i))
    (hlambda : lambda=r^(rankLoss eta0 c i)/(4*((g:ℝ)+1)))
    (hb : r^((2*((i.val+1:ℕ):ℝ)+1)*rankLoss eta0 c i) ≤ b)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hqraw : r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q)
    (hscale : ((64:ℝ)/((2^m:ℕ):ℝ))^2 ≤ 6144*r)
    (Cpre : ℝ) (hCpre : 0 < Cpre) :
    let F3 := refinementCost (d+2) (J+1) L3
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let rho := (64:ℝ)/((2^m:ℕ):ℝ)
    let w := min (boundaryWindow tau) ((tau/16)/1000)
    let CXbase := fiberCoefficient D.thickness eta zeta tau (seed/8) c2 lambda b F1 G Q2 F3 Q3 q (i.val+1)
    let M := max 1 (Cpre/quotientCost q)
    let KXY := actualXYConstant D.thickness eta zeta lambda b tau seed c2 w q Cpre F1 G Q2 F3 Q3 J m K
    let CX := (Cpre/quotientCost q)*CXbase
    CXbase ≤ rho^(-(epsilon/4)) ∧
      KXY ≤ M*rho^(-(epsilon/2)) ∧
      quotientConstant (i.val+1-1) (4-(i.val+1)) (1/((32:ℝ)^(i.val+1-1)*CX)) KXY (3-extremalExponent) ≤
        M^2*rho^(-epsilon) := by
  intro F3 Q3 rho w CXbase M KXY CX
  obtain ⟨_H3,_Hret,HxyBase,Hfixed,HxBase⟩ := Hbudget.2 n D eta h hsmall heta original horiginal S hS hSn
    F1 F2 G Q1 Q2 m hF1 hG hQ1 hQ2 hGF hm6 i hell zeta lambda b tau seed c2 r q
    hetaSeed htau0 htau hseed hzeta hc2 H1 H2 hr hr1 hrdelta hlambda hb hq hq1 hgrid hqraw hscale
  have hd := h.1.2.1
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    have hp : (64:ℝ) ≤ ((2^m:ℕ):ℝ) := by
      exact_mod_cast (show (2^6:ℕ) ≤ 2^m from Nat.pow_le_pow_right (by norm_num) hm6)
    exact (div_le_one (by positivity : (0:ℝ)<((2^m:ℕ):ℝ))).mpr hp
  have hlp : 0 < lambda := by rw [hlambda]; positivity
  have hbp : 0 < b := (Real.rpow_pos_of_pos hr _).trans_le hb
  have hQ3 : 0 < Q3 := (by norm_num : 0 < (4:ℕ)).trans_le (NativeSourceSizeBounds.radix_four_le _ _)
  have hF3 : 0 < F3 := refinementCost_pos _ _ _
  have hquot := quotientCost_pos hq
  have hpop : 0 < population D.thickness eta lambda b F1 G := by unfold population; positivity
  have heps : 0 < columnEpsilon D.thickness lambda (seed/8) c2 := by unfold columnEpsilon; positivity
  have hcmp := NativeAnisotropicGlobalSourceBridge.comparisonCost_pos
  have hrow := rowConstant_pos
  have hgraph := graphCost_pos K
  have hPL : 0 < profileLower D.thickness (population D.thickness eta lambda b F1 G)
      (columnEpsilon D.thickness lambda (seed/8) c2) tau (seed/8) w := by unfold profileLower; positivity
  have hPU : 0 < profileUpper D.thickness (columnEpsilon D.thickness lambda (seed/8) c2) tau := by
    unfold profileUpper
    positivity
  have Hpre : KXY ≤ M*actualXYConstant D.thickness eta zeta lambda b tau seed c2 w q (quotientCost q)
      F1 G Q2 F3 Q3 J m K := by
    dsimp only [KXY,M,actualXYConstant]
    exact xyConstant_pre_loss Q2 Q3 J m F3 hd hpop hPL hPU (div_pos hpop hrow)
      hgraph hquot hCpre hF3 hQ2 hQ3
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have Hxy : KXY ≤ M*rho^(-(epsilon/2)) :=
    Hpre.trans (mul_le_mul_of_nonneg_left HxyBase hM0)
  have hu : 0 < Cpre/quotientCost q := div_pos hCpre hquot
  have hPG : 0 < parentGrainConstant := by
    have hh := NativeParentVertexMassCap.parentCapConstant_pos
    unfold parentGrainConstant
    positivity
  have hTrans := transverseCost_pos hq (i.val+1)
  have hRef := referenceConstant_pos
  have hBasePos : 0 < CXbase := by
    dsimp only [CXbase,fiberCoefficient]
    positivity
  have hCX : 0 < CX := mul_pos hu hBasePos
  have hKXY : 1 ≤ KXY := by
    dsimp only [KXY,actualXYConstant]
    exact xyConstant_one_le _ _ _ _ _ _ _ _ _ _ _
  have HY := quotientConstant_le (i.val+1) (by omega) hell extremalExponent KXY CX
    extremalExponent_nonneg hKXY hCX
  have hpow : 1 ≤ rho^(-(epsilon/4)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrho hrho1 (by linarith only [he])
  have hmax : max 1 CX ≤ M*rho^(-(epsilon/4)) := by
    apply max_le
    · nlinarith only [hM,hpow]
    · exact ((mul_le_mul_of_nonneg_left HxBase hu.le).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 (Cpre/quotientCost q)) (by positivity)))
  have hnum : (512000:ℝ) ≤ rho^(-(epsilon/4)) := by
    have hn : (512000:ℝ) ≤ fixedCost := by norm_num [fixedCost,NativeThirdXYConstantComparison.geometryCost]
    exact hn.trans Hfixed
  refine ⟨HxBase,Hxy,?_⟩
  calc
    _ ≤ 512000*KXY*max 1 CX := HY
    _ ≤ rho^(-(epsilon/4))*(M*rho^(-(epsilon/2)))*(M*rho^(-(epsilon/4))) :=
      mul_le_mul (mul_le_mul hnum Hxy (le_trans (by norm_num) hKXY) (by positivity)) hmax
        (le_trans (by norm_num) (le_max_left _ _)) (by positivity)
    _ = M^2*(rho^(-(epsilon/4))*rho^(-(epsilon/2))*rho^(-(epsilon/4))) := by ring
    _ = _ := by rw [←Real.rpow_add hrho,←Real.rpow_add hrho]; congr 1; ring

end NativePaidThirdReadback
