import Theorems.Thm_StickyKakeya4_native_actual_physical_third_prerequisites
/- Originally drafted without verification; consult current verification receipts. -/
import Theorems.Thm_StickyKakeya4_native_htotal_implementation
import Theorems.Thm_StickyKakeya4_native_extra_paid_XY_configuration
import Theorems.Thm_StickyKakeya4_native_paid_third_budget
import Theorems.Thm_StickyKakeya4_native_extra_graph_configuration
import Theorems.Thm_StickyKakeya4_native_generic_XY_rank
import Theorems.Thm_StickyKakeya4_native_retained_slice_budget
import Theorems.Thm_StickyKakeya4_native_generic_graph_rank
import Theorems.Thm_StickyKakeya4_native_physical_queried_rank_configuration
import Theorems.Thm_StickyKakeya4_native_conditional_reference_menu
import Theorems.Thm_StickyKakeya4_native_generic_reference_data
import Theorems.Thm_StickyKakeya4_native_same_reference_chart_bounds
import Theorems.Thm_StickyKakeya4_native_retention_output_power
import Theorems.Thm_StickyKakeya4_native_actual_configured_base
import Theorems.Thm_StickyKakeya4_native_middle_grain_parent_budget
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data
import Theorems.Thm_StickyKakeya4_native_reference_slice_budget_readback
import Theorems.Thm_StickyKakeya4_native_sharp_X_power_algebra

/- Frozen origin: Thm_StickyKakeya4_native_prescribed_extra_paid_XY_configuration.lean; SHA256 5f859b0b9b44c1ba99d5039a6b63322febdb67ece8fdbc2028e35f63e4dc0954. -/
/- Originally drafted without verification; consult current verification receipts. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace NativePrescribedExtraPaidXYConfiguration
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization NativeFixedCompactKakeyaExponent SelfUniform
open NativeJointUniformCoarseRelations NativeJointQuantitativeMenu NativeBalancedConfiguration
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeConditionedPairMenu
open NativeAllTwoScaleConfiguration NativeActualMesoscopicRankConfiguration NativeRankExponentHierarchy
open NativeGenericReferenceData NativeGenericReferenceRank NativeGenericReferenceSecondStage NativeGenericQueryRank
open NativeExtraQueriedRankConfiguration NativeCandidateReferenceConfiguration NativeMiddleGrainParentBudget
open NativeGenericGraphRankData NativeGenericGraphRank NativePhysicalReferenceData
open NativeGenericFinalAttachment NativeGeneralRankScalarBudget
open NativePaidThirdBudget NativeRetainedSliceBudgetSource
open scoped ENNReal

open NativeExtraGraphConfiguration NativeGenericXYRank NativeRetainedSliceBudget NativeRetainedSliceCore
open NativePrescribedReferenceAdmission NativeReferenceAdmissionInvariance
open NativeReferenceParentPopulation NativeActualRelativeCoarseAdmission
theorem exists_prescribed_extra_paid_XY_configuration (d Jhorizontal d3 Khalf : ℕ) (extraCount : ℕ → ℕ)
    (hHalf3 : 3 ≤ Khalf) (hHorizontal : 0 < Jhorizontal) (hk : 0 < extremalExponent)
    (eta0 c epsilonGraph : ℝ) (he0 : 0 < eta0) (heK : eta0 ≤ extremalExponent/2)
    (hc : 0 < c) (hcsmall : c ≤ 1/2)
    (hcUnit : c ≤ 1/(eta0+1)) (hcGap : c ≤ positiveGap extremalExponent/(256*(eta0+1)))
    (heGraph : 0 < epsilonGraph) (heps : eta0 ≤ epsilonGraph) (hceps : c ≤ epsilonGraph/24)
    (hgrain : 1/((2*Khalf:ℕ):ℝ) ≤ epsilonGraph/2)
    (tauBound : ℝ) (hTauBound : 0 < tauBound)
    (epsilonPaid : ℝ) (hePaid : 0 < epsilonPaid) (he01 : eta0 ≤ 1)
    (hePaidSmall : eta0 ≤ epsilonPaid/8192)
    (hcQXY : c ≤ quotientTolerance (epsilonPaid/4)/24)
    (hcQX : c ≤ quotientTolerance (epsilonPaid/16)/24)
    (hHorizontalLoss : 3/(Jhorizontal:ℝ) ≤ epsilonPaid/32)
    (etaNative profileExp sigma0 : ℝ)
    (hNative : 0 < etaNative) (hProfile : 0 < profileExp) (hSigma0 : 0 < sigma0) :
    ∃(tau : ℝ) (htau : 0 < tau) (seed e zeta : ℝ) (L g L2 : ℕ),
      tau ≤ tauBound ∧ tau ≤ commonBudget eta0 c/(1000*(((2*Khalf:ℕ):ℝ)+1)) ∧
      tau ≤ commonBudget eta0 c/1024 ∧ tau ≤ 1/2 ∧ tau ≤ c^3/8 ∧
      0 < seed ∧ seed ≤ tau/16384 ∧ 0 < e ∧ 0 < zeta ∧ zeta ≤ seed/256 ∧
      0 < L ∧ 0 < g ∧ 1/(g:ℝ) < rankWindow tau/4 ∧ 0 < L2 ∧
      ∃deltaGraph : ℝ,0 < deltaGraph ∧ deltaGraph ≤ 1/8 ∧
      ∃L3 : ℕ,0 < L3 ∧ ∃delta3 : ℝ,0 < delta3 ∧ delta3 ≤ 1 ∧
      HasBudget epsilonPaid eta0 c g Khalf d3 Jhorizontal L3 delta3 ∧
      ∀menu : MenuFactory g (extraCount g),MenuRefl menu → MenuSymm menu →
      ∀slot : Fin (g+1) → Fin (extraCount g),
      (∀n D eta h a level R original schedule i,
        menu n D eta h a level R original schedule (slot i)=
          (fun x y => parentLabel D a (2^(middleDepth (schedule i).val)) x.1=
            parentLabel D a (2^(middleDepth (schedule i).val)) y.1)) →
      ∀etaBound deltaBound : ℝ,0 < etaBound → 0 < deltaBound →
      ∃(eta : ℝ) (n : ℕ) (D : FiniteScaleSource n) (h : IsWangZakharovNativeFiniteInput D eta),
        0 < eta ∧ eta < etaBound ∧ eta < seed/8 ∧ eta < (commonBudget eta0 c/4)/8 ∧
        D.thickness < deltaBound ∧ D.thickness ≤ deltaGraph ∧ D.thickness ≤ delta3 ∧
        (∀i,D.line i∈fixedCompactClass) ∧
        volume (sourceUnion D) ≤ (ENNReal.ofReal D.thickness).rpow (extremalExponent-eta) ∧
        D.thickness^(-extremalExponent+eta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal ∧
        ∃ref : Reference h tau htau seed e zeta L g,
          ref.dimension=menuSize (pairMenuSize
            (extraCount g+(1+(g+1))) (g+1)) (g+1) ∧
          HasCallerUniformities ref menu ∧
          HasPhysicalUniformities ref ∧
          (∀i : Fin (g+1),∀p : Parent,
            (parentEdges D ref.a (2^(middleDepth (ref.schedule i).val)) ref.E1 p).Nonempty →
            let m := middleDepth (ref.schedule i).val
            IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h ref.R ref.E1 ref.a m p) etaNative ∧
            (∀j,(NativeLocalParentSource.source h ref.R ref.E1 ref.a m p).line j∈fixedCompactClass) ∧
            (NativeLocalParentSource.source h ref.R ref.E1 ref.a m p).thickness ≤ sigma0 ∧
            (64:ℝ)^3*(NativeLocalParentSource.source h ref.R ref.E1 ref.a m p).thickness^profileExp ≤
              D.thickness^zeta ∧
            OriginalPopulationLaw (NativeLocalParentSource.source h ref.R ref.E1 ref.a m p)
              univ 0 profileExp (ref.level-m+6)) ∧
          D.thickness^(-extremalExponent+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity ref.E1 ∧
          (∀U⊆incidences ref.original,U.Nonempty →
            (refinementCost (d3+2) (Jhorizontal+1) L3:ℝ)*
              (NativeSourceSizeBounds.radix U.card L3:ℝ)^4 ≤ D.thickness^(-(commonBudget eta0 c/4))) ∧
          HasXYRankSelection ref d (2*Khalf) Jhorizontal d3 Khalf L2 L3 eta0 c (commonBudget eta0 c/4) epsilonGraph := by
  obtain ⟨deltaAdmission,hDeltaAdmission,_hDeltaAdmission8,Hadmit⟩ :=
    exists_prescribed_parent_admission etaNative profileExp sigma0 hNative hProfile hSigma0
  let tauCut := min tauBound (min etaNative profileExp)
  have hTauCut : 0 < tauCut := lt_min hTauBound (lt_min hNative hProfile)
  obtain ⟨tau,htau,seed,e,zeta,L,g,L2,htauCut,htauHalfBudget,htauBudget,htauHalf,htauC,
    hseed,hseedTau,he,hzeta,hzseed,hL,hg,hgrid,hL2,
    deltaGraph,hDeltaGraph,hDeltaGraph8,L3,hL3,delta3,hDelta3,hDelta31,Hbudget,Hsource⟩ :=
    NativeExtraPaidXYConfiguration.exists_extra_paid_XY_configuration d Jhorizontal d3 Khalf extraCount
      hHalf3 hHorizontal hk eta0 c epsilonGraph he0 heK hc hcsmall hcUnit hcGap
      heGraph heps hceps hgrain tauCut hTauCut epsilonPaid hePaid he01 hePaidSmall
      hcQXY hcQX hHorizontalLoss
  have htauBound := htauCut.trans (min_le_left _ _)
  have htauRest := htauCut.trans (min_le_right _ _)
  have hseedNative : seed ≤ etaNative := by
    have hh := htauRest.trans (min_le_left _ _)
    linarith only [hseedTau,hh,htau]
  have hseedProfile : seed ≤ profileExp := by
    have hh := htauRest.trans (min_le_right _ _)
    linarith only [hseedTau,hh,htau]
  refine ⟨tau,htau,seed,e,zeta,L,g,L2,htauBound,htauHalfBudget,htauBudget,htauHalf,htauC,
    hseed,hseedTau,he,hzeta,hzseed,hL,hg,hgrid,hL2,
    deltaGraph,hDeltaGraph,hDeltaGraph8,L3,hL3,delta3,hDelta3,hDelta31,Hbudget,?_⟩
  intro menu hMenuRefl hMenuSymm slot hSlot etaBound deltaBound hEtaBound hDeltaBound
  let deltaCut := min deltaBound (min deltaAdmission ((2:ℝ)⁻¹^6))
  have hDeltaCut : 0 < deltaCut := lt_min hDeltaBound (lt_min hDeltaAdmission (by positivity))
  obtain ⟨eta,n,D,h,heta,hetaBound,hetaSeed,hetaThird,hsmall,hGraphSmall,hThirdSmall,
    hcompact,hvolume,hnear,ref,hDim,Hcaller,Hphysical,hNearE,Hraw,HXY⟩ :=
    Hsource menu hMenuRefl hMenuSymm etaBound deltaCut hEtaBound hDeltaCut
  have hDeltaAdm : D.thickness ≤ deltaAdmission :=
    (hsmall.le.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hDeltaSix : D.thickness ≤ (2:ℝ)⁻¹^6 :=
    (hsmall.le.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hlevel : 6 ≤ ref.level := NativeFixedSizeScaleMenu.depth_le_of_dyadic_cutoff
    ref.level 6 ref.backbone.2.1 hDeltaSix
  refine ⟨eta,n,D,h,heta,hetaBound,hetaSeed,hetaThird,
    hsmall.trans_le (min_le_left _ _),hGraphSmall,hThirdSmall,hcompact,hvolume,hnear,
    ref,hDim,Hcaller,Hphysical,?_,hNearE,Hraw,HXY⟩
  intro i p hp m
  have hstop : (ref.schedule i).val ≤ ref.level := Nat.le_of_lt_succ (ref.schedule i).isLt
  have hm : m ≤ ref.level := (candidate_middle_bounds ref.level (ref.schedule i).val hlevel hstop).2
  have hscale := candidate_middle_square ref.level (ref.schedule i).val ref.backbone.2.1 hstop
  have Hparent : ∀x y,x∈ref.E1 → y∈ref.E1 →
      (parentEdges D ref.a (2^m) ref.E1 (parentLabel D ref.a (2^m) x.1)).card ≤
        (coreRadix ref.original ref.R L)^2*
          (parentEdges D ref.a (2^m) ref.E1 (parentLabel D ref.a (2^m) y.1)).card := by
    intro x y hx hy
    have hh := Hcaller (slot i) x y hx hy
    rw [hSlot n D eta h ref.a ref.level ref.R ref.original ref.schedule i] at hh
    simpa only [unit_degree_eq_parentEdges] using hh
  obtain ⟨_hParentNative,hParentCompact,hParentSmall,hParentProfile,_hParentLaw,hFullNative,hFullLaw⟩ :=
    Hadmit n D eta zeta seed ref.a h hzeta.le hetaSeed.le hzseed hseedNative hseedProfile
      hDeltaAdm ref.original ref.R ref.level ref.backbone ref.E1 ref.core.1
      (factor ref.dimension (g+1) L) (coreRadix ref.original ref.R L) m hm hscale
      ref.core.2.2.1 Hparent ref.cost p hp
  have hEq := source_parent_eq h ref.R ref.E1 ref.a m p
  refine ⟨hFullNative,?_,?_,?_,hFullLaw⟩
  · simpa only [hEq] using hParentCompact
  · simpa only [hEq] using hParentSmall
  · simpa only [hEq] using hParentProfile

end NativePrescribedExtraPaidXYConfiguration
end -- original anonymous section NativePrescribedExtraPaidXYConfiguration

/- Frozen origin: Thm_StickyKakeya4_native_conditional_reference_parent_slots.lean; SHA256 dac9e2e065d655eb11266d1bf4efa847bb30353e274d9d9b11bf370bc7fbe1a7. -/
/- Originally drafted without verification; consult current verification receipts. -/

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace NativeConditionalReferenceParentSlots
open Classical Finset StickyKakeya4 NativeOriginalParentSelection
open NativeConditionalReferenceMenu NativeMiddleGrainParentBudget
open NativeCommonCubicalMesh NativeOriginalParentDensityCore

/-- The existing (0,0) two-scale query already asks for the outer middle
parent. No extra slot or source refinement is required. -/
def baseQuery (g K : ℕ) (i : Fin (g+1)) : Fin (queryCount g K) :=
  finProdFinEquiv (i,finProdFinEquiv ((0:Fin (K+1)),(0:Fin (K+1))))

lemma parentDepth_baseQuery {g K level : ℕ}
    (schedule : Fin (g+1) → Fin (level+1)) (i : Fin (g+1)) :
    parentDepth schedule (baseQuery g K i)=middleDepth (schedule i).val := by
  simp [parentDepth,outerDepth,sigmaDepth,candidate,pair,gridDepth,baseQuery]

def parentSlot (g K : ℕ) (i : Fin (g+1)) : Fin (relationCount g K) :=
  Fin.castAdd (queryCount g K*(1+1)) (baseQuery g K i)

/-- Exact equality of the relation in the actual coherence menu. This is
the static readback consumed by the prescribed-admission source factory. -/
theorem factory_parent_slot (g K n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (level : ℕ)
    (R : Finset (Fin n)) (original : Fin n → Finset Index)
    (schedule : Fin (g+1) → Fin (level+1)) (i : Fin (g+1)) :
    factory g K n D eta h a level R original schedule (parentSlot g K i)=
      (fun x y => parentLabel D a (2^(middleDepth (schedule i).val)) x.1=
        parentLabel D a (2^(middleDepth (schedule i).val)) y.1) := by
  simp only [factory,NativeReferenceRelativeMenu.relations,parentSlot,Fin.addCases_left,
    parentDepth_baseQuery]

end NativeConditionalReferenceParentSlots
end -- original anonymous section NativeConditionalReferenceParentSlots

/- Frozen origin: Thm_StickyKakeya4_native_prescribed_conditional_paid_XY_configuration.lean; SHA256 eae87b8b65507f4ba2e89e6466aee683dbe5d2286bbf1cf5d3ef9f0468c377c1. -/
/- Originally drafted without verification; consult current verification receipts. -/
/- Originally drafted without verification; consult current verification receipts. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace NativePrescribedConditionalPaidXYConfiguration
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization NativeFixedCompactKakeyaExponent SelfUniform
open NativeJointUniformCoarseRelations NativeJointQuantitativeMenu NativeBalancedConfiguration
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeConditionedPairMenu
open NativeAllTwoScaleConfiguration NativeActualMesoscopicRankConfiguration NativeRankExponentHierarchy
open NativeGenericReferenceData NativeGenericReferenceRank NativeGenericReferenceSecondStage NativeGenericQueryRank
open NativeExtraQueriedRankConfiguration NativeCandidateReferenceConfiguration NativeMiddleGrainParentBudget
open NativeGenericGraphRankData NativeGenericGraphRank NativePhysicalReferenceData
open NativeGenericFinalAttachment NativeGeneralRankScalarBudget
open NativePaidThirdBudget NativeRetainedSliceBudgetSource
open scoped ENNReal

open NativeExtraGraphConfiguration NativeGenericXYRank NativeRetainedSliceBudget NativeRetainedSliceCore
open NativePrescribedReferenceAdmission NativeReferenceAdmissionInvariance
open NativeReferenceParentPopulation NativeActualRelativeCoarseAdmission
open NativeConditionalReferenceMenu NativeConditionalReferenceParentSlots
theorem exists_prescribed_conditional_paid_XY_configuration (d Jhorizontal d3 Khalf : ℕ) (Kupper : ℕ)
    (hHalf3 : 3 ≤ Khalf) (hHorizontal : 0 < Jhorizontal) (hk : 0 < extremalExponent)
    (eta0 c epsilonGraph : ℝ) (he0 : 0 < eta0) (heK : eta0 ≤ extremalExponent/2)
    (hc : 0 < c) (hcsmall : c ≤ 1/2)
    (hcUnit : c ≤ 1/(eta0+1)) (hcGap : c ≤ positiveGap extremalExponent/(256*(eta0+1)))
    (heGraph : 0 < epsilonGraph) (heps : eta0 ≤ epsilonGraph) (hceps : c ≤ epsilonGraph/24)
    (hgrain : 1/((2*Khalf:ℕ):ℝ) ≤ epsilonGraph/2)
    (tauBound : ℝ) (hTauBound : 0 < tauBound)
    (epsilonPaid : ℝ) (hePaid : 0 < epsilonPaid) (he01 : eta0 ≤ 1)
    (hePaidSmall : eta0 ≤ epsilonPaid/8192)
    (hcQXY : c ≤ quotientTolerance (epsilonPaid/4)/24)
    (hcQX : c ≤ quotientTolerance (epsilonPaid/16)/24)
    (hHorizontalLoss : 3/(Jhorizontal:ℝ) ≤ epsilonPaid/32)
    (etaNative profileExp sigma0 : ℝ)
    (hNative : 0 < etaNative) (hProfile : 0 < profileExp) (hSigma0 : 0 < sigma0) :
    ∃(tau : ℝ) (htau : 0 < tau) (seed e zeta : ℝ) (L g L2 : ℕ),
      tau ≤ tauBound ∧ tau ≤ commonBudget eta0 c/(1000*(((2*Khalf:ℕ):ℝ)+1)) ∧
      tau ≤ commonBudget eta0 c/1024 ∧ tau ≤ 1/2 ∧ tau ≤ c^3/8 ∧
      0 < seed ∧ seed ≤ tau/16384 ∧ 0 < e ∧ 0 < zeta ∧ zeta ≤ seed/256 ∧
      0 < L ∧ 0 < g ∧ 1/(g:ℝ) < rankWindow tau/4 ∧ 0 < L2 ∧
      ∃deltaGraph : ℝ,0 < deltaGraph ∧ deltaGraph ≤ 1/8 ∧
      ∃L3 : ℕ,0 < L3 ∧ ∃delta3 : ℝ,0 < delta3 ∧ delta3 ≤ 1 ∧
      HasBudget epsilonPaid eta0 c g Khalf d3 Jhorizontal L3 delta3 ∧
      ∀etaBound deltaBound : ℝ,0 < etaBound → 0 < deltaBound →
      ∃(eta : ℝ) (n : ℕ) (D : FiniteScaleSource n) (h : IsWangZakharovNativeFiniteInput D eta),
        0 < eta ∧ eta < etaBound ∧ eta < seed/8 ∧ eta < (commonBudget eta0 c/4)/8 ∧
        D.thickness < deltaBound ∧ D.thickness ≤ deltaGraph ∧ D.thickness ≤ delta3 ∧
        (∀i,D.line i∈fixedCompactClass) ∧
        volume (sourceUnion D) ≤ (ENNReal.ofReal D.thickness).rpow (extremalExponent-eta) ∧
        D.thickness^(-extremalExponent+eta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal ∧
        ∃ref : Reference h tau htau seed e zeta L g,
          ref.dimension=menuSize (pairMenuSize
            (relationCount g Kupper+(1+(g+1))) (g+1)) (g+1) ∧
          HasCallerUniformities ref (factory g Kupper) ∧
          HasPhysicalUniformities ref ∧
          (∀i : Fin (g+1),∀p : Parent,
            (parentEdges D ref.a (2^(middleDepth (ref.schedule i).val)) ref.E1 p).Nonempty →
            let m := middleDepth (ref.schedule i).val
            IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h ref.R ref.E1 ref.a m p) etaNative ∧
            (∀j,(NativeLocalParentSource.source h ref.R ref.E1 ref.a m p).line j∈fixedCompactClass) ∧
            (NativeLocalParentSource.source h ref.R ref.E1 ref.a m p).thickness ≤ sigma0 ∧
            (64:ℝ)^3*(NativeLocalParentSource.source h ref.R ref.E1 ref.a m p).thickness^profileExp ≤
              D.thickness^zeta ∧
            OriginalPopulationLaw (NativeLocalParentSource.source h ref.R ref.E1 ref.a m p)
              univ 0 profileExp (ref.level-m+6)) ∧
          D.thickness^(-extremalExponent+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity ref.E1 ∧
          (∀U⊆incidences ref.original,U.Nonempty →
            (refinementCost (d3+2) (Jhorizontal+1) L3:ℝ)*
              (NativeSourceSizeBounds.radix U.card L3:ℝ)^4 ≤ D.thickness^(-(commonBudget eta0 c/4))) ∧
          HasXYRankSelection ref d (2*Khalf) Jhorizontal d3 Khalf L2 L3 eta0 c (commonBudget eta0 c/4) epsilonGraph := by
  obtain ⟨tau,htau,seed,e,zeta,L,g,L2,htauBound,htauHalfBudget,htauBudget,htauHalf,htauC,
    hseed,hseedTau,he,hzeta,hzseed,hL,hg,hgrid,hL2,
    deltaGraph,hDeltaGraph,hDeltaGraph8,L3,hL3,delta3,hDelta3,hDelta31,Hbudget,Hsource⟩ :=
    NativePrescribedExtraPaidXYConfiguration.exists_prescribed_extra_paid_XY_configuration
      d Jhorizontal d3 Khalf (fun g => relationCount g Kupper) hHalf3 hHorizontal hk
      eta0 c epsilonGraph he0 heK hc hcsmall hcUnit hcGap heGraph heps hceps hgrain
      tauBound hTauBound epsilonPaid hePaid he01 hePaidSmall hcQXY hcQX hHorizontalLoss
      etaNative profileExp sigma0 hNative hProfile hSigma0
  refine ⟨tau,htau,seed,e,zeta,L,g,L2,htauBound,htauHalfBudget,htauBudget,htauHalf,htauC,
    hseed,hseedTau,he,hzeta,hzseed,hL,hg,hgrid,hL2,
    deltaGraph,hDeltaGraph,hDeltaGraph8,L3,hL3,delta3,hDelta3,hDelta31,Hbudget,?_⟩
  exact Hsource (factory g Kupper) (factory_refl g Kupper) (factory_symm g Kupper)
    (parentSlot g Kupper) (factory_parent_slot g Kupper)

end NativePrescribedConditionalPaidXYConfiguration
end -- original anonymous section NativePrescribedConditionalPaidXYConfiguration

/- Frozen origin: Thm_StickyKakeya4_native_prescribed_physical_reference_configuration.lean; SHA256 74f1f71cff95ea48dea1d1c8aa801aa640ffc354d3125064d10daa9dd586ff8f. -/
/- Originally drafted without verification; consult current verification receipts. -/
/- Originally drafted without verification; consult current verification receipts. -/
/- Originally drafted without verification; consult current verification receipts. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace NativePrescribedPhysicalReferenceConfiguration
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization NativeFixedCompactKakeyaExponent SelfUniform
open NativeJointUniformCoarseRelations NativeJointQuantitativeMenu NativeBalancedConfiguration
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeConditionedPairMenu
open NativeAllTwoScaleConfiguration NativeActualMesoscopicRankConfiguration NativeRankExponentHierarchy
open NativeGenericReferenceData NativeGenericReferenceRank NativeGenericReferenceSecondStage NativeGenericQueryRank
open NativeExtraQueriedRankConfiguration NativeCandidateReferenceConfiguration NativeMiddleGrainParentBudget
open NativeGenericGraphRankData NativeGenericGraphRank NativePhysicalReferenceData
open NativeGenericFinalAttachment NativeGeneralRankScalarBudget
open NativePaidThirdBudget NativeRetainedSliceBudgetSource
open scoped ENNReal

open NativeExtraGraphConfiguration NativeGenericXYRank NativeRetainedSliceBudget NativeRetainedSliceCore
open NativePrescribedReferenceAdmission NativeReferenceAdmissionInvariance
open NativeReferenceParentPopulation NativeActualRelativeCoarseAdmission
open NativeConditionalReferenceMenu NativeConditionalReferenceParentSlots
open NativeSourcePhysicalCoherence NativePaidMeshAngularBounds
theorem exists_prescribed_physical_reference_configuration (d Jhorizontal d3 Khalf : ℕ)
    (hHalf3 : 3 ≤ Khalf) (hHorizontal : 0 < Jhorizontal) (hk : 0 < extremalExponent)
    (eta0 c epsilonGraph : ℝ) (he0 : 0 < eta0) (heK : eta0 ≤ extremalExponent/2)
    (hc : 0 < c) (hcsmall : c ≤ 1/2)
    (hcUnit : c ≤ 1/(eta0+1)) (hcGap : c ≤ positiveGap extremalExponent/(256*(eta0+1)))
    (heGraph : 0 < epsilonGraph) (heps : eta0 ≤ epsilonGraph) (hceps : c ≤ epsilonGraph/24)
    (hgrain : 1/((2*Khalf:ℕ):ℝ) ≤ epsilonGraph/2)
    (tauBound : ℝ) (hTauBound : 0 < tauBound)
    (epsilonPaid : ℝ) (hePaid : 0 < epsilonPaid) (he01 : eta0 ≤ 1)
    (hePaidSmall : eta0 ≤ epsilonPaid/8192)
    (hcQXY : c ≤ quotientTolerance (epsilonPaid/4)/24)
    (hcQX : c ≤ quotientTolerance (epsilonPaid/16)/24)
    (hHorizontalLoss : 3/(Jhorizontal:ℝ) ≤ epsilonPaid/32)
    (etaNative profileExp sigma0 : ℝ)
    (hNative : 0 < etaNative) (hProfile : 0 < profileExp) (hSigma0 : 0 < sigma0)
    (loss : ℝ) (hLoss : 0 < loss) (hLoss1 : loss ≤ 1) :
    ∃(Kupper : ℕ) (seedCap deltaUpper : ℝ),0 < Kupper ∧ 0 < seedCap ∧ 0 < deltaUpper ∧
      deltaUpper ≤ 1/8 ∧ HasUpperEngine Kupper (c^3/8) loss seedCap deltaUpper ∧
    ∃(tau : ℝ) (htau : 0 < tau) (seed e zeta : ℝ) (L g L2 : ℕ),
      tau ≤ tauBound ∧ tau ≤ commonBudget eta0 c/(1000*(((2*Khalf:ℕ):ℝ)+1)) ∧
      tau ≤ commonBudget eta0 c/1024 ∧ tau ≤ 1/2 ∧ tau ≤ c^3/8 ∧
      0 < seed ∧ seed ≤ tau/16384 ∧ 0 < e ∧ 0 < zeta ∧ zeta ≤ seed/256 ∧
      0 < L ∧ 0 < g ∧ 1/(g:ℝ) < rankWindow tau/4 ∧ 0 < L2 ∧
      ∃deltaGraph : ℝ,0 < deltaGraph ∧ deltaGraph ≤ 1/8 ∧
      ∃L3 : ℕ,0 < L3 ∧ ∃delta3 : ℝ,0 < delta3 ∧ delta3 ≤ 1 ∧
      HasBudget epsilonPaid eta0 c g Khalf d3 Jhorizontal L3 delta3 ∧ seed ≤ seedCap ∧
      ∀etaBound deltaBound : ℝ,0 < etaBound → 0 < deltaBound →
      ∃(eta : ℝ) (n : ℕ) (D : FiniteScaleSource n) (h : IsWangZakharovNativeFiniteInput D eta),
        0 < eta ∧ eta < etaBound ∧ eta < seed/8 ∧ eta < (commonBudget eta0 c/4)/8 ∧
        D.thickness < deltaBound ∧ D.thickness ≤ deltaGraph ∧ D.thickness ≤ delta3 ∧
        D.thickness ≤ deltaUpper ∧
        (∀i,D.line i∈fixedCompactClass) ∧
        volume (sourceUnion D) ≤ (ENNReal.ofReal D.thickness).rpow (extremalExponent-eta) ∧
        D.thickness^(-extremalExponent+eta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal ∧
        ∃ref : Reference h tau htau seed e zeta L g,
          ref.dimension=menuSize (pairMenuSize
            (relationCount g Kupper+(1+(g+1))) (g+1)) (g+1) ∧
          HasCallerUniformities ref (factory g Kupper) ∧
          HasPhysicalUniformities ref ∧
          (∀i : Fin (g+1),∀p : Parent,
            (parentEdges D ref.a (2^(middleDepth (ref.schedule i).val)) ref.E1 p).Nonempty →
            let m := middleDepth (ref.schedule i).val
            IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h ref.R ref.E1 ref.a m p) etaNative ∧
            (∀j,(NativeLocalParentSource.source h ref.R ref.E1 ref.a m p).line j∈fixedCompactClass) ∧
            (NativeLocalParentSource.source h ref.R ref.E1 ref.a m p).thickness ≤ sigma0 ∧
            (64:ℝ)^3*(NativeLocalParentSource.source h ref.R ref.E1 ref.a m p).thickness^profileExp ≤
              D.thickness^zeta ∧
            OriginalPopulationLaw (NativeLocalParentSource.source h ref.R ref.E1 ref.a m p)
              univ 0 profileExp (ref.level-m+6)) ∧
          D.thickness^(-extremalExponent+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity ref.E1 ∧
          (∀U⊆incidences ref.original,U.Nonempty →
            (refinementCost (d3+2) (Jhorizontal+1) L3:ℝ)*
              (NativeSourceSizeBounds.radix U.card L3:ℝ)^4 ≤ D.thickness^(-(commonBudget eta0 c/4))) ∧
          HasXYRankSelection ref d (2*Khalf) Jhorizontal d3 Khalf L2 L3 eta0 c (commonBudget eta0 c/4) epsilonGraph := by
  obtain ⟨Kupper,seedCap,deltaUpper,hKupper,hSeedCap,hDeltaUpper,hDeltaUpper8,Hupper⟩ :=
    exists_paid_mesh_angular_bounds (c^3/8) loss (by positivity) hLoss hLoss1
  let tauCut := min tauBound seedCap
  have hTauCut : 0 < tauCut := lt_min hTauBound hSeedCap
  obtain ⟨tau,htau,seed,e,zeta,L,g,L2,htauCut,htauHalfBudget,htauBudget,htauHalf,htauC,
    hseed,hseedTau,he,hzeta,hzseed,hL,hg,hgrid,hL2,
    deltaGraph,hDeltaGraph,hDeltaGraph8,L3,hL3,delta3,hDelta3,hDelta31,Hbudget,Hsource⟩ :=
    NativePrescribedConditionalPaidXYConfiguration.exists_prescribed_conditional_paid_XY_configuration
      d Jhorizontal d3 Khalf Kupper hHalf3 hHorizontal hk eta0 c epsilonGraph he0 heK hc hcsmall
      hcUnit hcGap heGraph heps hceps hgrain tauCut hTauCut epsilonPaid hePaid he01 hePaidSmall
      hcQXY hcQX hHorizontalLoss etaNative profileExp sigma0 hNative hProfile hSigma0
  have htauBound := htauCut.trans (min_le_left _ _)
  have hSeed : seed ≤ seedCap := by
    have hh := htauCut.trans (min_le_right _ _)
    linarith only [hseedTau,htau,hh]
  refine ⟨Kupper,seedCap,deltaUpper,hKupper,hSeedCap,hDeltaUpper,hDeltaUpper8,Hupper,
    tau,htau,seed,e,zeta,L,g,L2,htauBound,htauHalfBudget,htauBudget,htauHalf,htauC,
    hseed,hseedTau,he,hzeta,hzseed,hL,hg,hgrid,hL2,
    deltaGraph,hDeltaGraph,hDeltaGraph8,L3,hL3,delta3,hDelta3,hDelta31,Hbudget,hSeed,?_⟩
  intro etaBound deltaBound hEtaBound hDeltaBound
  obtain ⟨eta,n,D,h,heta,hetaBound,hetaSeed,hetaThird,hsmall,hGraphSmall,hThirdSmall,
    hcompact,hvolume,hnear,ref,hDim,Hcaller,Hphysical,Hnative,hNearE,Hraw,HXY⟩ :=
    Hsource etaBound (min deltaBound deltaUpper) hEtaBound (lt_min hDeltaBound hDeltaUpper)
  exact ⟨eta,n,D,h,heta,hetaBound,hetaSeed,hetaThird,
    hsmall.trans_le (min_le_left _ _),hGraphSmall,hThirdSmall,
    hsmall.le.trans (min_le_right _ _),hcompact,hvolume,hnear,
    ref,hDim,Hcaller,Hphysical,Hnative,hNearE,Hraw,HXY⟩

end NativePrescribedPhysicalReferenceConfiguration
end -- original anonymous section NativePrescribedPhysicalReferenceConfiguration

/- Frozen origin: Thm_StickyKakeya4_native_actual_baseline_scale_guards.lean; SHA256 f7e452dc66104d235a8c73cda3430653c7b2fbbce7382041338c36b50d8adab7. -/
/- Originally drafted without verification; consult current verification receipts. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeActualBaselineScaleGuards
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeMiddleGrainParentBudget NativeSquaredGrainQueries NativeGenericReferenceData
open NativeLocalParentSource NativeReferenceXYGridPoints NativeSameReferenceChartBounds
open NativeRetentionOutputPower NativeQuarterScaleParameters

/-- The actual stopping-depth cap and the actual base chooser give the
strong guard required by baseline sparse admission. The square guard alone
is not used to infer this inequality. -/
theorem depth_guard (stop level u : ℕ) (hstop : 6 ≤ stop) (hcap : stop ≤ level/4)
    (hu : u+6 ≤ middleDepth stop) : middleDepth stop+(u+12) ≤ level := by
  dsimp only [middleDepth] at hu ⊢
  omega

theorem reference_depth_guard {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0 < tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (j : Fin (g+1))
    (hj : j∈NativeRankMesoscopicRadiusMenu.menu
      (NativeActualMesoscopicRankConfiguration.rankWindow tau)
      (NativeActualMesoscopicRankConfiguration.rankWindow_pos htau).le g ref.level)
    (hstop : 6 ≤ (ref.schedule j).val) (u : ℕ)
    (hu : u+6 ≤ middleDepth (ref.schedule j).val) :
    middleDepth (ref.schedule j).val+(u+12) ≤ ref.level :=
  depth_guard _ _ _ hstop (stopping_depth_cap htau g ref.level ref.schedule ref.schedule_eq j hj) hu

/-- In literal source units the stronger depth guard gives eps>=64r.
Here r is the E1-parent source thickness, not the rank stopping radius. -/
theorem source_mesh_lower {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (level m u : ℕ) (p : Parent)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hdepth : m+(u+12) ≤ level) :
    64*(source h R Eref a m p).thickness ≤ 64/((2^(u+12):ℕ):ℝ) := by
  have hh := source_scale_guard (a:=a) h R Eref level m (u+12) p hdy hdepth
  apply (le_div_iff₀ (show (0:ℝ)<((2^(u+12):ℕ):ℝ) by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤64)
  nlinarith only [hm]

lemma source_thickness_ge_original {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (m : ℕ) (p : Parent) (hRho : rho m ≤ 1) :
    D.thickness ≤ (source h R Eref a m p).thickness := by
  have hr : 0 ≤ (source h R Eref a m p).thickness := by
    rw [source_thickness]
    have hd := h.1.2.1
    positivity
  have hid : (source h R Eref a m p).thickness*rho m=D.thickness := by
    rw [source_thickness]
    unfold rho
    field_simp
  have hh := mul_le_mul_of_nonneg_left hRho hr
  simpa only [hid,mul_one] using hh

/-- The actual configured base envelope also supplies its UPPER power
window, after one cutoff chosen from amin before the original source.
Together with depth_guard this proves both distinct baseline scale guards. -/
theorem exists_source_mesh_window (amin : ℝ) (hamin : 0 < amin) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta a : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta)
        (R : Finset (Fin n)) (Eref : Finset (Fin n × Index)) (m : ℕ) (p : Parent)
        (rStop power epsilonGeom eps : ℝ),
      D.thickness ≤ delta0 → amin ≤ power → rStop ≤ D.thickness^power →
      (rho m)^2 ≤ 6144*rStop → rho m ≤ 1 → 0 < eps →
      0 ≤ epsilonGeom → epsilonGeom ≤ 1/4 →
      64*eps ≤ 2*max ((5/4:ℝ)*(rho m)^(1-2*epsilonGeom)) (rho m) →
      eps ≤ (source h R Eref a m p).thickness^(amin/8) := by
  obtain ⟨delta0,hd0,hd01,Hcut⟩ := exists_small_power_cutoff
    (show 0 < amin/2 by positivity) (by norm_num : (0:ℝ)<1/6144)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro n D eta a h R Eref m p rStop power epsilonGeom eps
    hsmall hpower hstop hRhoStop hRho1 heps heGeom heGeom4 hbase
  have hd := h.1.2.1
  have hd1 := hsmall.trans hd01
  have hRho := rho_pos m
  have hshape := configured_square_le_reference hRho hRho1 heps.le heGeom heGeom4 hbase
  have hfour := output_fourth_le_stop hRho.le hshape hRhoStop
  have hstop' : rStop ≤ D.thickness^amin :=
    hstop.trans (Real.rpow_le_rpow_of_exponent_ge hd hd1 hpower)
  have hpay := Hcut D.thickness hd hsmall
  have hpositive := Real.rpow_nonneg hd.le (amin/2)
  have hsplit : D.thickness^amin=D.thickness^(amin/2)*D.thickness^(amin/2) := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  have hfour' : eps^4 ≤ D.thickness^(amin/2) := by
    rw [hsplit] at hstop'
    have hpaidMultiply := mul_le_mul_of_nonneg_left hpay hpositive
    nlinarith only [hfour,hstop',hpaidMultiply]
  have hpow : (D.thickness^(amin/8))^(4:ℕ)=D.thickness^(amin/2) := by
    rw [←Real.rpow_mul_natCast hd.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hepsDelta : eps ≤ D.thickness^(amin/8) :=
    (pow_le_pow_iff_left₀ heps.le (Real.rpow_nonneg hd.le _) (by norm_num : (4:ℕ)≠0)).mp
      (hfour'.trans_eq hpow.symm)
  exact hepsDelta.trans (Real.rpow_le_rpow hd.le
    (source_thickness_ge_original (a:=a) h R Eref m p hRho1) (by positivity))

end NativeActualBaselineScaleGuards
end -- original anonymous section NativeActualBaselineScaleGuards

/- Frozen origin: Thm_StickyKakeya4_native_source_baseline_base.lean; SHA256 786b73027017909af6b6faf4b6663f6c87f17224dce91dee11a0c471619fc9c7. -/
/- Originally drafted without verification; consult current verification receipts. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeSourceBaselineBase
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeReferenceXYGridPoints NativeMiddleGrainParentBudget
open NativeActualBaselineScaleGuards NativeActualConfiguredBase NativeCommonYTotalBudget

/-- All baseline scale obligations are imposed through ONE original-source
cutoff, before D. finalBound can be the intersection of the actual g-dependent
retention/planar cutoffs. The base u/R0 is then constructed once from the
actual middle parent and works for its unchanged source at every Eref,p. -/
theorem exists_source_baseline_base (amin finalBound rBound : ℝ)
    (ha : 0 < amin) (hFinal : 0 < finalBound) (hBound : 0 < rBound) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta a : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta)
        (R : Finset (Fin n)) (Eref : Finset (Fin n × Index)) (p : Parent)
        (level stop : ℕ) (rStop power epsilonGeom : ℝ),
      D.thickness ≤ delta0 → D.thickness=(2:ℝ)⁻¹^level →
      6 ≤ stop → stop ≤ level/4 →
      amin ≤ power → rStop ≤ D.thickness^power →
      (rho (middleDepth stop))^2 ≤ 6144*rStop →
      D.thickness ≤ (rho (middleDepth stop))^2 →
      0 ≤ epsilonGeom → epsilonGeom ≤ 1/4 →
      let m := middleDepth stop
      ∃u : ℕ,6 ≤ u ∧ u+6 ≤ m ∧
      let R0 : ℕ := 2^(m-u)
      let eps : ℝ := 64/((2^(u+12):ℕ):ℝ)
      0 < R0 ∧ mu m*(R0:ℝ)=(2:ℝ)⁻¹^u ∧
      rho m ≤ mu m*(R0:ℝ) ∧
      (5/4:ℝ)*(rho m)^(1-2*epsilonGeom) ≤ mu m*(R0:ℝ) ∧
      mu m*(R0:ℝ) ≤ 2*max ((5/4:ℝ)*(rho m)^(1-2*epsilonGeom)) (rho m) ∧
      mu m*(R0:ℝ) ≤ 1 ∧
      ((8*R0:ℕ):ℝ) ≤ 1280*(mu m)^(-2*epsilonGeom) ∧
      mu m*(R0:ℝ)=4096/((2^(u+12):ℕ):ℝ) ∧
      0 < eps ∧ eps < finalBound ∧ m+(u+12) ≤ level ∧
      64*(source h R Eref a m p).thickness ≤ eps ∧
      eps ≤ (source h R Eref a m p).thickness^(amin/8) ∧
      (source h R Eref a m p).thickness ≤ rBound := by
  obtain ⟨deltaBase,hdBase,hdBase1,Hbase⟩ := exists_source_base amin finalBound ha hFinal
  obtain ⟨deltaWindow,hdWindow,_hdWindow1,Hwindow⟩ := exists_source_mesh_window amin ha
  let delta0 := min deltaBase (min deltaWindow (rBound^2))
  have hd0 : 0 < delta0 := lt_min hdBase (lt_min hdWindow (sq_pos_of_pos hBound))
  refine ⟨delta0,hd0,(min_le_left _ _).trans hdBase1,?_⟩
  intro n D eta a h R Eref p level stop rStop power epsilonGeom
    hsmall hdy hstop hstopCap hpower hStop hRhoStop hscale heGeom heGeom4 m
  have hBaseSmall : D.thickness ≤ deltaBase := hsmall.trans (min_le_left _ _)
  have hWindowSmall : D.thickness ≤ deltaWindow :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hBoundSmall : D.thickness ≤ rBound^2 :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨u,hu6,huM,hR0,hbaseEq,hRho,hError,hHigh,hBase1,hHeight,hFinalSmall⟩ :=
    Hbase D.thickness rStop power h.1.2.1 hBaseSmall hpower hStop m hRhoStop
      epsilonGeom heGeom heGeom4
  let R0 : ℕ := 2^(m-u)
  let eps : ℝ := 64/((2^(u+12):ℕ):ℝ)
  have heps : 0 < eps := by dsimp [eps]; positivity
  change mu m*(R0:ℝ)=(2:ℝ)⁻¹^u at hbaseEq
  change mu m*(R0:ℝ)/64 < finalBound at hFinalSmall
  have hmesh : (mu m*(R0:ℝ))/64=eps := by
    change (mu m*(R0:ℝ))/64=64/((2^(u+12):ℕ):ℝ)
    rw [hbaseEq,fine_mesh_eq]
    rw [pow_add]
    norm_num; ring
  have hmatch : mu m*(R0:ℝ)=4096/((2^(u+12):ℕ):ℝ) := by
    calc
      mu m*(R0:ℝ) = 64*eps := by linarith only [hmesh]
      _ = 4096/((2^(u+12):ℕ):ℝ) := by dsimp [eps]; ring
  have hdepth := depth_guard stop level u hstop hstopCap huM
  have hLower := source_mesh_lower (a:=a) h R Eref level m u p hdy hdepth
  have hRho1 : rho m ≤ 1 := hRho.trans hBase1
  have hshapeBound : 64*eps ≤ 2*max ((5/4:ℝ)*(rho m)^(1-2*epsilonGeom)) (rho m) := by
    have he : 64*eps=mu m*(R0:ℝ) := by rw [←hmesh]; ring
    rwa [he]
  have hUpper := Hwindow n D eta a h R Eref m p rStop power epsilonGeom eps
    hWindowSmall hpower hStop hRhoStop hRho1 heps heGeom heGeom4 hshapeBound
  have hSq := source_thickness_sq_le_original (a:=a) h R Eref m p hscale
  have hSource0 : 0 ≤ (source h R Eref a m p).thickness := by
    rw [source_thickness]
    have hh := h.1.2.1
    positivity
  have hSourceBound : (source h R Eref a m p).thickness ≤ rBound := by
    nlinarith only [hSq,hBoundSmall,hSource0,hBound]
  refine ⟨u,hu6,huM,hR0,hbaseEq,hRho,hError,hHigh,hBase1,hHeight,hmatch,heps,?_,
    hdepth,hLower,hUpper,hSourceBound⟩
  rwa [hmesh] at hFinalSmall

end NativeSourceBaselineBase
end -- original anonymous section NativeSourceBaselineBase

/- Frozen origin: Thm_StickyKakeya4_native_final_source_scope_readback.lean; SHA256 f12cfe2650f22019f8556ba62a6b931a703eca054ba0957adb9c6b4d88c741c4. -/
/- Originally drafted without verification; consult current verification receipts. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeFinalSourceScopeReadback
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeGenericReferenceData
open NativeLocalParentSource NativeMiddleGrainParentBudget NativeSquaredGrainQueries
open NativeReferenceXYGridPoints NativeSameReferenceChartBounds

/-- Both original-label fields needed by sparse admission come from the
actual first IsCore. The enlarged first dimension is never changed. -/
theorem original_scope {n L g : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau}
    (ref : Reference h tau htau seed e zeta L g) :
    ref.E1⊆incidences ref.original ∧ ∀z∈ref.E1,z.1∈ref.R := by
  refine ⟨ref.core.1.trans (filter_subset _ _),?_⟩
  intro z hz
  exact (mem_filter.mp (ref.core.1 hz)).2

/-- All final incidences are in the literal SAME original parent, including
membership in the unchanged R, rather than just equality of phase labels. -/
theorem parent_scope {n L g : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau}
    (ref : Reference h tau htau seed e zeta L g)
    (m : ℕ) (p : Parent) (T : Finset (Fin n × Index))
    (hT : T⊆ref.E1) (hp : ∀z∈T,parentLabel D ref.a (2^m) z.1=p) :
    ∀z∈T,z.1∈parentLabels D ref.R ref.a (2^m) p := by
  intro z hz
  exact (mem_parentLabels D ref.R ref.a (2^m) p z.1).mpr
    ⟨(original_scope ref).2 z (hT hz),hp z hz⟩

/-- The final nonempty T activates the already installed E1-parent native
supplier. No source is reselected and no nonemptiness certificate is added. -/
theorem active_reference_parent {n L g : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau}
    (ref : Reference h tau htau seed e zeta L g)
    (m : ℕ) (p : Parent) (T : Finset (Fin n × Index))
    (hT : T⊆ref.E1) (hTn : T.Nonempty)
    (hp : ∀z∈T,parentLabel D ref.a (2^m) z.1=p) :
    (parentEdges D ref.a (2^m) ref.E1 p).Nonempty := by
  obtain ⟨z,hz⟩ := hTn
  exact ⟨z,mem_filter.mpr ⟨hT hz,hp z hz⟩⟩

/-- The actual stopping cap and scale identity give the original fine-depth
and initial square guards used by the SAME final-third and parent readers. -/
theorem middle_guards (stop level : ℕ) (delta r : ℝ)
    (hs : 6 ≤ stop) (hcap : stop ≤ level/4) (_hd : 0 < delta)
    (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 64*delta ≤ r^2)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1) :
    let m := middleDepth stop
    phaseDepth m ≤ level ∧ delta ≤ (rho m)^2 ∧
      3072*r ≤ (rho m)^2 ∧ (rho m)^2 ≤ 6144*r := by
  intro m
  obtain ⟨_hm6,_hms,_hlo,hfine⟩ := middle_depth_bounds stop hs
  obtain ⟨_hRho,_hRho1,_hSquare,hRlo,hRhi⟩ := middle_scale_bounds stop hs r hidentity
  have hFine : phaseDepth m ≤ level := hfine.trans (by omega)
  have hrSquare : r^2 ≤ r := by nlinarith only [hr,hr1]
  change 3072*r ≤ (rho m)^2 at hRlo
  refine ⟨hFine,?_,hRlo,hRhi⟩
  nlinarith only [hsmall,hrSquare,hRlo,hr]

end NativeFinalSourceScopeReadback
end -- original anonymous section NativeFinalSourceScopeReadback

/- Frozen origin: Thm_StickyKakeya4_native_actual_third_history_readback.lean; SHA256 b06797f7ce830b6ab7d4514036b51083d0bdc01b7d3c14c88acb6c63ab9d0f6e. -/
/- Originally drafted without verification; consult current verification receipts. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeActualThirdHistoryReadback
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeThirdXYSourceData NativeRetainedSliceCore NativeReferenceSliceBudgetAlgebra
open NativeReferenceSliceBudgetReadback NativeActivePhasePopulation NativeAllTwoScaleConfiguration
open NativeHorizontalGrainSlice NativeReferenceXYGridPoints NativeSquaredGrainQueries
open NativeSharpXPowerAlgebra NativeParentHeightGraphCore NativeRetainedSliceBudgetAlgebra

/-- The actual history mass inequality gives the scalar b used by the
raw budget on that same E2, without replacing its original point weights. -/
theorem fraction_lower {n : ℕ} (E2 : Finset (Fin n × Index)) (hE2 : E2.Nonempty)
    (r rankLoss W : ℝ) (H : r^(5*rankLoss)*(E2.card:ℝ) ≤ W) :
    r^(5*rankLoss) ≤ W/(E2.card:ℝ) := by
  have hcard : (0:ℝ)<E2.card := by exact_mod_cast card_pos.mpr hE2
  exact (le_div_iff₀ hcard).mpr H

/-- The selected-parent population and the scalar budget population are
literally equal by population_mass_ratio. Every set, raw label, final radix,
field, and full third relation count stays identical in this readback. -/
theorem source_record {n d J : ℕ} (D : FiniteScaleSource n)
    (eta zeta a : ℝ) (m : ℕ) (plane : Index → Submodule ℝ E4)
    (E2 Hgraph U T : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (f : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (p : Parent)
    (lambda W tau seed c2 q Cpre threshold : ℝ) (F1 G Q2 K L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) :
    let b := W/(E2.card:ℝ)
    let pop := (lambda*W/(2*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ)))*D.thickness^eta
    let popBudget := population D.thickness eta lambda b F1 G
    let col := columnEpsilon D.thickness lambda (seed/8) c2
    let window := min (boundaryWindow tau) ((tau/16)/1000)
    let F3 := refinementCost (d+2) (J+1) L3
    let Q3 := NativeSourceSizeBounds.radix U.card L3
    let CX := (Cpre/quotientCost q)*fiberCoefficient D.thickness eta zeta tau (seed/8) c2
      lambda b F1 G Q2 F3 Q3 q 2
    HasThirdXYSourceData (J:=J) (ell:=2) D zeta a m plane E2 Hgraph U T P hP
      (by norm_num) (by norm_num) hd f p pop
      (profileLower D.thickness pop col tau (seed/8) window) (profileUpper D.thickness col tau)
      Q2 (pop/rowConstant) (selectionCost K) Cpre threshold L3 Rel CX →
    HasThirdXYSourceData (J:=J) (ell:=2) D zeta a m plane E2 Hgraph U T P hP
      (by norm_num) (by norm_num) hd f p popBudget
      (profileLower D.thickness popBudget col tau (seed/8) window) (profileUpper D.thickness col tau)
      Q2 (popBudget/rowConstant) (selectionCost K) Cpre threshold L3 Rel CX := by
  intro b pop popBudget col window F3 Q3 CX H
  have hpop : popBudget=pop := population_mass_ratio D.thickness eta lambda W E2.card F1 G
  simpa only [hpop] using H

end NativeActualThirdHistoryReadback
end -- original anonymous section NativeActualThirdHistoryReadback
