import Theorems.Thm_StickyKakeya4_native_paid_third_readback
import Theorems.Thm_StickyKakeya4_native_paid_third_budget
import Theorems.Thm_StickyKakeya4_native_XY_pre_loss_budget
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data
import Theorems.Thm_StickyKakeya4_native_quotient_constant_bound

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
noncomputable section
namespace NativePaidThirdData
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeRetainedSliceCore
open NativePaidThirdBudget NativeActualXYBudgetComparison NativeXYPreLossBudget
open NativeThirdXYData NativeThirdXYSourceData NativeEncodedQuotientAD NativeQuotientConstantBound
open NativeSharpXPowerAlgebra NativeRetainedSliceBudgetAlgebra NativeReferenceSliceBudgetAlgebra
open NativeRankExponentHierarchy NativeFixedCompactKakeyaExponent NativeAllTwoScaleConfiguration
open NativeActivePhasePopulation NativeParentHeightGraphCore NativeRetainedSliceBudgetExtra
open NativeSourceParentGrainCleanup NativeActualProjectedGrainCount NativeActualRichPacketLayers
open NativeThirdXYFixedBudget

open NativePaidThirdReadback NativeHorizontalGrainSlice NativeGrainQuotientFibers
open NativeReferenceXYGridField NativeReferenceXYGridMaps NativeTwoMapRetainedSliceActualCaps
open NativeTranslatedGrainHeightFibers NativeQuotientLatticeTransport NativeSliceClassBalls
open FiniteVoronoiRealADCoarsening
open scoped Matrix.Norms.Elementwise

/-- Increasing an actual positive AD constant preserves the same carrier. -/
lemma ADBounds_mono_constant {X : Type*} [PseudoMetricSpace X]
    (A : Finset X) {mu K K' s : ℝ} (hmu : 0 < mu) (hK : 0 < K) (hKK : K ≤ K')
    (H : ADBounds A mu K s) : ADBounds A mu K' s := by
  intro x hx r hr hr1
  have hh := H x hx r hr hr1
  have hp : 0 ≤ (r/mu)^s := by have hrr := hmu.trans_le hr; positivity
  exact ⟨(div_le_div_of_nonneg_left hp hK hKK).trans hh.1,
    hh.2.trans (mul_le_mul_of_nonneg_right hKK hp)⟩

/-- Source-derived scalar payment on the already chosen third T. This only
weakens its proved constants; no incidence, chart, or point set is changed. -/
theorem paid_data_from_budget {epsilon eta0 c delta0 : ℝ} {g K d J L3 n : ℕ}
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
    (a : ℝ) (plane : Index → Submodule ℝ E4) (E Hgraph T : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hdim : Module.finrank ℝ P=i.val+1-1)
    (Fraw : ℤ → Matrix (Fin (4-(i.val+1))) (Fin (i.val+1-1)) ℝ)
    (p : Parent) (t : ℝ) (Rel3 : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hdata :
      let F3 := refinementCost (d+2) (J+1) L3
      let Q3 := NativeSourceSizeBounds.radix S.card L3
      let w := min (boundaryWindow tau) ((tau/16)/1000)
      let pop := population D.thickness eta lambda b F1 G
      let eps := columnEpsilon D.thickness lambda (seed/8) c2
      let CX := (Cpre/quotientCost q)*fiberCoefficient D.thickness eta zeta tau (seed/8) c2 lambda b
        F1 G Q2 F3 Q3 q (i.val+1)
      HasThirdXYSourceData (J:=J) D zeta a m plane E Hgraph S T P hP (by omega) (by omega) hdim Fraw p
        pop (profileLower D.thickness pop eps tau (seed/8) w) (profileUpper D.thickness eps tau)
        Q2 (pop/rowConstant) (selectionCost K) Cpre t L3 Rel3 CX) :
    let F3 := refinementCost (d+2) (J+1) L3
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let rho := (64:ℝ)/((2^m:ℕ):ℝ)
    let w := min (boundaryWindow tau) ((tau/16)/1000)
    let CXbase := fiberCoefficient D.thickness eta zeta tau (seed/8) c2 lambda b F1 G Q2 F3 Q3 q (i.val+1)
    let M := max 1 (Cpre/quotientCost q)
    let KXY := actualXYConstant D.thickness eta zeta lambda b tau seed c2 w q Cpre F1 G Q2 F3 Q3 J m K
    let CX := (Cpre/quotientCost q)*CXbase
    let mu := physicalMesh m (NativeSquaredGrainQueries.phaseDepth m)/8
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m (i.val+1) plane Hgraph P hP (by omega) (by omega) hdim mu
    let field := fixedField D a m (i.val+1) plane Sq Fraw
    let xy := fun z : Fin n × Index => encodedPoint D a m (i.val+1) p P hP (by omega) (by omega) hdim field z.2
    CXbase ≤ rho^(-(epsilon/4)) ∧ KXY ≤ M*rho^(-(epsilon/2)) ∧
      quotientConstant (i.val+1-1) (4-(i.val+1)) (1/((32:ℝ)^(i.val+1-1)*CX)) KXY (3-extremalExponent) ≤
        M^2*rho^(-epsilon) ∧
      (∀height : ℤ,ADBounds (realizedSlice (T.image xy) (NativeReferenceXYGridPoints.mu m) height)
        (NativeReferenceXYGridPoints.mu m) (M*rho^(-(epsilon/2))) (3-extremalExponent)) ∧
      (∀height : ℤ,ADBounds
        (((productSlice (T.image (fun z => pxy D a m (i.val+1) p P hP (by omega) (by omega) hdim field z.2)) height).image
          Prod.snd).image (NativeQuotientGridCenters.center (NativeReferenceXYGridPoints.mu m)))
        (NativeReferenceXYGridPoints.mu m) (M^2*rho^(-epsilon)) (4-((i.val+1:ℕ):ℝ)-extremalExponent)) ∧
      ∀x∈T,rho^(epsilon/4)*rho^(-(((i.val+1:ℕ):ℝ)-1)) ≤ M*
        (referenceX D a m (i.val+1) plane T P hP (by omega) (by omega) hdim mu
          (referenceKey D a m (i.val+1) plane P hP (by omega) (by omega) hdim mu x)).card := by
  intro F3 Q3 rho w CXbase M KXY CX mu Sq field xy
  have Hbounds := constants_from_budget Hbudget he h hsmall heta original horiginal S hS hSn
    F1 F2 G Q1 Q2 m hF1 hG hQ1 hQ2 hGF hm6 i hi hell zeta lambda b tau seed c2 r q
    hetaSeed htau0 htau hseed hzeta hc2 H1 H2 hr hr1 hrdelta hlambda hb hq hq1 hgrid hqraw hscale Cpre hCpre
  have hKXYone : 1 ≤ KXY := by
    dsimp only [KXY,actualXYConstant]
    exact xyConstant_one_le _ _ _ _ _ _ _ _ _ _ _
  have hKXYpos : 0 < KXY := lt_of_lt_of_le (by norm_num) hKXYone
  have Hcopy := Hdata.1
  rcases Hcopy with ⟨_hTS,_hTn,_hCost,_hTH,_hFinal,_hExtra,_hOld,_hXY,_hClass,_hGrain,_hKey,_hThreshold,_hRet,Hxy,_hRead,_hNorm⟩
  refine ⟨Hbounds.1,Hbounds.2.1,Hbounds.2.2,?_,?_,?_⟩
  · intro height
    exact ADBounds_mono_constant _ (NativeReferenceXYGridPoints.mu_pos m) hKXYpos Hbounds.2.1 (Hxy height)
  · intro height
    have hKY : 0 < quotientConstant (i.val+1-1) (4-(i.val+1))
        (1/((32:ℝ)^(i.val+1-1)*CX)) KXY (3-extremalExponent) :=
      lt_of_lt_of_le (by norm_num) (quotientConstant_one_le _ _ _ _ _)
    exact ADBounds_mono_constant _ (NativeReferenceXYGridPoints.mu_pos m) hKY Hbounds.2.2 (Hdata.2.2.2.1 height)
  · intro x hx
    have hrho : 0 < rho := by dsimp [rho]; positivity
    have hquot := quotientCost_pos hq
    have hu : 0 ≤ Cpre/quotientCost q := (div_pos hCpre hquot).le
    have hCXbound : CX ≤ M*rho^(-(epsilon/4)) :=
      (mul_le_mul_of_nonneg_left Hbounds.1 hu).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 (Cpre/quotientCost q)) (by positivity))
    have hh := (Hdata.2.2.1 x hx).trans (mul_le_mul_of_nonneg_right hCXbound (Nat.cast_nonneg _))
    calc
      _ ≤ rho^(epsilon/4)*(M*rho^(-(epsilon/4))*
          (referenceX D a m (i.val+1) plane T P hP (by omega) (by omega) hdim mu
            (referenceKey D a m (i.val+1) plane P hP (by omega) (by omega) hdim mu x)).card) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = M*(referenceX D a m (i.val+1) plane T P hP (by omega) (by omega) hdim mu
            (referenceKey D a m (i.val+1) plane P hP (by omega) (by omega) hdim mu x)).card*
          (rho^(epsilon/4)*rho^(-(epsilon/4))) := by ring
      _ = _ := by rw [←Real.rpow_add hrho,add_neg_cancel,Real.rpow_zero,mul_one]

end NativePaidThirdData
