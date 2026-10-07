import Theorems.Thm_StickyKakeya4_native_paid_third_budget
import Theorems.Thm_StickyKakeya4_native_window_source_constant
import Theorems.Thm_StickyKakeya4_native_window_budget_cutoff
import Theorems.Thm_StickyKakeya4_native_quotient_constant_bound

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeActualWindowBudget
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeRetainedSliceCore
open NativePaidThirdBudget NativeActualXYBudgetComparison NativeXYPreLossBudget
open NativeThirdXYData NativeThirdXYSourceData NativeEncodedQuotientAD NativeQuotientConstantBound
open NativeSharpXPowerAlgebra NativeRetainedSliceBudgetAlgebra NativeReferenceSliceBudgetAlgebra
open NativeRankExponentHierarchy NativeFixedCompactKakeyaExponent NativeAllTwoScaleConfiguration
open NativeActivePhasePopulation NativeParentHeightGraphCore NativeRetainedSliceBudgetExtra
open NativeSourceParentGrainCleanup NativeActualProjectedGrainCount NativeActualRichPacketLayers
open NativeThirdXYFixedBudget

open NativeRetainedSliceBudgetSource NativeWindowSourceConstant NativeWindowPowerPayment
open NativeActualWindowXYAD NativeWindowXYMetric

/-- Literal prepared-window constant with the actual retained-parent
profiles. This is distinct from the fixed-height xyConstant. -/
def actualWindowXYConstant (delta eta zeta lambda b tau seed c2 w Cpre Lip : ℝ)
    (F1 G Q2 F3 Q3 J m K : ℕ) : ℝ :=
  let pop := population delta eta lambda b F1 G
  let eps := columnEpsilon delta lambda (seed / 8) c2
  let fullLower := (pop / rowConstant) * delta ^ (tau + seed / 8 + 10 * w)
  let fullUpper := delta ^ (-3 * tau)
  let Cnew := NativeVariableHeightSourceBridge.comparisonCost
  let Ln := lowerCountCoefficient delta zeta pop ((Cnew / eps) * fullUpper)
  let Un := 8 * (NativeVariableHeightNumeratorUpper.pairUpperConstant * delta ^ (-2 * zeta)) /
    ((eps / Cnew) * fullLower)
  windowConstant Ln Un (pop / rowConstant) ((selectionCost K : ℝ) * Cpre * F3) Q2 Q3
    ((2 * menuRadius Lip + 1) ^ 3) ((phaseDepth m - m) / J + 1)

/-- One actual pre-D HasBudget pays the base retained and X constants on
its full d+2 relation allowance and the actual pre-third S.card. The extra
geometry cutoff is also fixed before D. The new-cut multiplier is kept
once in prepared window XY and twice in its quotient Y. No AD or desired
window-constant bound is supplied as a premise. -/
theorem window_constants_from_budget {epsilon eta0 c delta0 : ℝ} {g K d J L3 n : ℕ}
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
    (Cpre : ℝ) (hCpre : 0 < Cpre)
    (Lip geometryTolerance : ℝ) (hLip0 : 0 ≤ Lip) (hgeo : 0 ≤ geometryTolerance)
    (hgeoSmall : geometryTolerance ≤ epsilon / 144)
    (hLip : Lip ≤ 3 * r ^ (-2 * geometryTolerance))
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hsmallWindow : D.thickness ≤ NativeWindowBudgetCutoff.sourceCutoff epsilon c geometryTolerance he hc) :
    let F3 := refinementCost (d + 2) (J + 1) L3
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let rho := (64 : ℝ) / ((2 ^ m : ℕ) : ℝ)
    let w := min (boundaryWindow tau) ((tau / 16) / 1000)
    let CXbase := fiberCoefficient D.thickness eta zeta tau (seed / 8) c2 lambda b F1 G Q2 F3 Q3 q (i.val + 1)
    let M := max 1 (Cpre / quotientCost q)
    let KXY := actualWindowXYConstant D.thickness eta zeta lambda b tau seed c2 w Cpre Lip F1 G Q2 F3 Q3 J m K
    let CX := (Cpre / quotientCost q) * CXbase
    CXbase ≤ rho ^ (-(epsilon / 4)) ∧
      KXY ≤ M * rho ^ (-(3 * epsilon / 4)) ∧
      quotientConstant (i.val + 1 - 1) (4 - (i.val + 1)) (1 / ((32 : ℝ) ^ (i.val + 1 - 1) * CX)) KXY
        (3 - extremalExponent) ≤ M ^ 2 * rho ^ (-epsilon) := by
  intro F3 Q3 rho w CXbase M KXY CX
  obtain ⟨_H3, Hret, _Hxy, _Hfixed, HxBase⟩ := Hbudget.2 n D eta h hsmall heta original horiginal S hS hSn
    F1 F2 G Q1 Q2 m hF1 hG hQ1 hQ2 hGF hm6 i hell zeta lambda b tau seed c2 r q
    hetaSeed htau0 htau hseed hzeta hc2 H1 H2 hr hr1 hrdelta hlambda hb hq hq1 hgrid hqraw hscale
  have hd := h.1.2.1
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    have hp : (64 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
      exact_mod_cast (show (2 ^ 6 : ℕ) ≤ 2 ^ m from Nat.pow_le_pow_right (by norm_num) hm6)
    exact (div_le_one (by positivity : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ))).mpr hp
  have hlp : 0 < lambda := by rw [hlambda]; positivity
  have hbp : 0 < b := (Real.rpow_pos_of_pos hr _).trans_le hb
  have hQ3 : 0 < Q3 := (by norm_num : 0 < (4 : ℕ)).trans_le (NativeSourceSizeBounds.radix_four_le _ _)
  have hF3 : 0 < F3 := refinementCost_pos _ _ _
  have hquot := quotientCost_pos hq
  let pop := population D.thickness eta lambda b F1 G
  let eps := columnEpsilon D.thickness lambda (seed / 8) c2
  let fl := (pop / rowConstant) * D.thickness ^ (tau + seed / 8 + 10 * w)
  let fu := D.thickness ^ (-3 * tau)
  let Cnew := NativeVariableHeightSourceBridge.comparisonCost
  let Ln := lowerCountCoefficient D.thickness zeta pop ((Cnew / eps) * fu)
  let Un := 8 * (NativeVariableHeightNumeratorUpper.pairUpperConstant * D.thickness ^ (-2 * zeta)) /
    ((eps / Cnew) * fl)
  let Kbase := actualWindowXYConstant D.thickness eta zeta lambda b tau seed c2 w (quotientCost q) Lip
    F1 G Q2 F3 Q3 J m K
  let Kret := actualRetainedConstant D.thickness eta zeta lambda b F1 G Q2 tau seed c2 w F3 Q3 q J m K
    (3 - extremalExponent)
  have hrow := rowConstant_pos
  have hgraph := graphCost_pos K
  have hpop : 0 < pop := by dsimp [pop, population]; positivity
  have heps : 0 < eps := by dsimp [eps, columnEpsilon]; positivity
  have hfl : 0 < fl := by dsimp [fl]; positivity
  have hfu : 0 < fu := by dsimp [fu]; positivity
  have hCnew : 0 < Cnew := NativeVariableHeightSourceBridge.comparisonCost_pos
  have hpair := NativeVariableHeightNumeratorUpper.pairUpperConstant_pos
  have hLn : 0 < Ln := by dsimp [Ln, lowerCountCoefficient]; positivity
  have hUn : 0 < Un := by dsimp [Un]; positivity
  have Hpre : KXY ≤ M * Kbase := by
    dsimp only [KXY, M, Kbase, actualWindowXYConstant]
    exact windowConstant_pre_loss Q2 Q3 ((2 * menuRadius Lip + 1) ^ 3) ((phaseDepth m - m) / J + 1) F3
      hLn hUn (div_pos hpop hrow) hgraph hquot hCpre hQ2 hQ3 (by positivity) hF3
  have Hgeom0 := windowConstant_le_retained_power (delta := D.thickness) (zeta := zeta)
    (population := pop) (eps := eps) (fullLower := fl) (fullUpper := fu)
    (retain := pop / rowConstant) (loss := (selectionCost K : ℝ) * quotientCost q * F3)
    (Lip := Lip) (A := 3) (r := r) (e := 2 * geometryTolerance) Q2 Q3 ((phaseDepth m - m) / J + 1)
    hd hpop heps hfl hfu (div_pos hpop hrow) (by positivity) hQ2 hQ3 hLip0 (by norm_num)
    hr hr1 (by positivity) (by simpa only [neg_mul] using hLip)
  have Hgeom : Kbase ≤ coordinateCost 3 * r ^ (-(18 * geometryTolerance)) * Kret := by
    have hexp : 9 * (2 * geometryTolerance) = 18 * geometryTolerance := by ring
    simpa only [Kbase, Kret, actualWindowXYConstant, actualRetainedConstant, profileLower, profileUpper,
      coordinateCost, pop, eps, fl, fu, Cnew, hexp, mul_assoc] using Hgeom0
  have Hcut := (NativeWindowBudgetCutoff.sourceCutoff_spec epsilon c geometryTolerance he hc).2.2
    D.thickness hd hsmallWindow rho r (cutoff c i) hrho (cutoff_bounds hc hc1 i).2.2 hrdelta hscale
  have hKret0 : 0 ≤ Kret := by
    dsimp only [Kret, actualRetainedConstant]
    exact le_trans (by norm_num) (NativeSliceADConstant.one_le_constant _ _ _ _)
  have hKbase0 : 0 ≤ Kbase := by
    dsimp only [Kbase, actualWindowXYConstant, windowConstant]
    exact le_trans (by norm_num) (NativeSliceADConstant.one_le_constant _ _ _ _)
  have hKXYone : 1 ≤ KXY := by
    dsimp only [KXY, actualWindowXYConstant, windowConstant]
    exact NativeSliceADConstant.one_le_constant _ _ _ _
  have hM : 1 ≤ M := le_max_left _ _
  have hu : 0 < Cpre / quotientCost q := div_pos hCpre hquot
  have hPG : 0 < parentGrainConstant := by
    have hh := NativeParentVertexMassCap.parentCapConstant_pos
    unfold parentGrainConstant
    positivity
  have hTrans := transverseCost_pos hq (i.val + 1)
  have hRef := referenceConstant_pos
  have hCXbase : 0 < CXbase := by dsimp only [CXbase, fiberCoefficient]; positivity
  have hCX : 0 < CX := mul_pos hu hCXbase
  have hCXpre : CX ≤ M * CXbase := mul_le_mul_of_nonneg_right (le_max_right _ _) hCXbase.le
  have HY := quotientConstant_le (i.val + 1) (by omega) hell extremalExponent KXY CX
    extremalExponent_nonneg hKXYone hCX
  have HH := pay_factory_window_with_pre_loss hrho hrho1 he hgeo hgeoSmall hscale hKret0 hKbase0
    Hcut Hret HxBase Hgeom hM Hpre hCXpre (le_trans (by norm_num) hKXYone) HY
  exact ⟨HxBase, HH⟩

end NativeActualWindowBudget
