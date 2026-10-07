/- UNVERIFIED source draft. No strict Lean check has run. -/
import Theorems.Thm_StickyKakeya4_native_prescribed_reference_admission
import Theorems.Thm_StickyKakeya4_native_extra_paid_XY_configuration
import Theorems.Thm_StickyKakeya4_native_paid_third_budget
import Theorems.Thm_StickyKakeya4_native_extra_graph_configuration
import Theorems.Thm_StickyKakeya4_native_generic_XY_rank
import Theorems.Thm_StickyKakeya4_native_retained_slice_budget
import Theorems.Thm_StickyKakeya4_native_generic_graph_rank
import Theorems.Thm_StickyKakeya4_native_physical_queried_rank_configuration
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
