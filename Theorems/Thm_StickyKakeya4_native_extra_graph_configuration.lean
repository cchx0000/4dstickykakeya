import Theorems.Thm_StickyKakeya4_native_generic_graph_rank
import Theorems.Thm_StickyKakeya4_native_physical_queried_rank_configuration
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeExtraGraphConfiguration
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization NativeFixedCompactKakeyaExponent SelfUniform
open NativeJointUniformCoarseRelations NativeJointQuantitativeMenu NativeBalancedConfiguration
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeConditionedPairMenu
open NativeAllTwoScaleConfiguration NativeActualMesoscopicRankConfiguration NativeRankExponentHierarchy
open NativeGenericReferenceData NativeGenericReferenceRank NativeGenericReferenceSecondStage NativeGenericQueryRank
open NativeCandidateReferenceConfiguration NativeMiddleGrainParentBudget
open NativeGenericGraphRankData NativeGenericGraphRank NativePhysicalReferenceData
open NativeGenericFinalAttachment NativeGeneralRankScalarBudget NativeExtraQueriedRankConfiguration
open scoped ENNReal

/-- One actual source with arbitrary prescribed extra relations carries its enlarged reference cost,
prescribed history, saturated parent and graph. Every cutoff is fixed before D. -/
theorem exists_extra_graph_configuration (d Kmenu Khalf : ℕ) (extraCount : ℕ → ℕ)
    (hHalf : 0 < Khalf) (hk : 0 < extremalExponent)
    (eta0 c epsilonGraph : ℝ) (he0 : 0 < eta0) (heK : eta0 ≤ extremalExponent/2)
    (hc : 0 < c) (hcsmall : c ≤ 1/2)
    (hcUnit : c ≤ 1/(eta0+1)) (hcGap : c ≤ positiveGap extremalExponent/(256*(eta0+1)))
    (heGraph : 0 < epsilonGraph) (heps : eta0 ≤ epsilonGraph) (hceps : c ≤ epsilonGraph/24)
    (hgrain : 1/((2*Khalf:ℕ):ℝ) ≤ epsilonGraph/2)
    (tauBound : ℝ) (hTauBound : 0 < tauBound) :
    ∃(tau : ℝ) (htau : 0 < tau) (seed e zeta : ℝ) (L g L2 : ℕ),
      tau ≤ tauBound ∧ tau ≤ commonBudget eta0 c/(1000*(((2*Khalf:ℕ):ℝ)+1)) ∧
      tau ≤ commonBudget eta0 c/1024 ∧ tau ≤ 1/2 ∧ tau ≤ c^3/8 ∧
      0 < seed ∧ seed ≤ tau/16384 ∧ 0 < e ∧ 0 < zeta ∧ zeta ≤ seed/256 ∧
      0 < L ∧ 0 < g ∧ 1/(g:ℝ) < rankWindow tau/4 ∧ 0 < L2 ∧
      ∃deltaGraph : ℝ,0 < deltaGraph ∧ deltaGraph ≤ 1/8 ∧
      ∀menu : MenuFactory g (extraCount g),MenuRefl menu → MenuSymm menu →
      ∀etaBound deltaBound : ℝ,0 < etaBound → 0 < deltaBound →
      ∃(eta : ℝ) (n : ℕ) (D : FiniteScaleSource n) (h : IsWangZakharovNativeFiniteInput D eta),
        0 < eta ∧ eta < etaBound ∧ eta < seed/8 ∧ D.thickness < deltaBound ∧ D.thickness ≤ deltaGraph ∧
        (∀i,D.line i∈fixedCompactClass) ∧
        volume (sourceUnion D) ≤ (ENNReal.ofReal D.thickness).rpow (extremalExponent-eta) ∧
        D.thickness^(-extremalExponent+eta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal ∧
        ∃ref : Reference h tau htau seed e zeta L g,
          ref.dimension=menuSize (pairMenuSize
            (extraCount g+(1+(g+1))) (g+1)) (g+1) ∧
          HasCallerUniformities ref menu ∧
          HasPhysicalUniformities ref ∧
          D.thickness^(-extremalExponent+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity ref.E1 ∧
          HasGraphRankSelection ref d (2*Khalf) Kmenu Khalf L2 eta0 c (commonBudget eta0 c/4) epsilonGraph := by
  have ht : 0 < commonBudget eta0 c := commonBudget_pos he0 hc
  let tauCap := min tauBound (commonBudget eta0 c/(1000*(((2*Khalf:ℕ):ℝ)+1)))
  have hTauCap : 0 < tauCap := lt_min hTauBound (by positivity)
  obtain ⟨tau,htau,seed,e,zeta,L,g,L2,
    htauCap,htauT,htauHalf,htauC,hseed,hseedTau,he,hzeta,hzseed,hL,hg,hgrid,hL2,Hsource⟩ :=
    NativePhysicalQueriedRankConfiguration.exists_extra_queried_rank_configuration
      (NativeParentHorizontalQueryMenu.size d Kmenu) (NativeGenericCompatibleStage.pairedCount (2*Khalf)) extraCount
      hk eta0 c he0 heK hc hcsmall tauCap hTauCap
  have htauB : tau ≤ commonBudget eta0 c/(1000*(((2*Khalf:ℕ):ℝ)+1)) := htauCap.trans (min_le_right _ _)
  have hc1 : c ≤ 1 := hcsmall.trans (by norm_num)
  obtain ⟨deltaMetric,hdMetric,hdMetric8,Hmetric⟩ :=
    NativeHeightMetricPower.exists_uniform_metric_cutoff c epsilonGraph hc hc1 heGraph
  let deltaRange := NativeHistoryDimensionRange.extraCutoff c hc hc1 g
  have hdRange : 0 < deltaRange := (NativeHistoryDimensionRange.extraCutoff_spec c hc hc1 g).1
  let deltaGraph := min (retainedCutoff g (2*Khalf) eta0 c he0 hc) (min deltaRange deltaMetric)
  have hdGraph : 0 < deltaGraph := lt_min (retainedCutoff_pos _ _ _ _ _ _) (lt_min hdRange hdMetric)
  have hdGraph8 : deltaGraph ≤ 1/8 := (min_le_right _ _).trans ((min_le_right _ _).trans hdMetric8)
  refine ⟨tau,htau,seed,e,zeta,L,g,L2,
    htauCap.trans (min_le_left _ _),htauB,htauT,htauHalf,htauC,hseed,hseedTau,he,hzeta,hzseed,hL,hg,hgrid,hL2,
    deltaGraph,hdGraph,hdGraph8,?_⟩
  intro menu hMenuRefl hMenuSymm etaBound deltaBound heB hdB
  obtain ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hK,hvol,hnear,ref,hDim,hCandidate,Hphysical,hNearE,Hquery⟩ :=
    Hsource menu hMenuRefl hMenuSymm etaBound (min deltaBound deltaGraph) heB (lt_min hdB hdGraph)
  have hGraphSmall : D.thickness ≤ deltaGraph := hsmall.le.trans (min_le_right _ _)
  have hcuts : D.thickness ≤ retainedCutoff g (2*Khalf) eta0 c he0 hc ∧
      D.thickness ≤ deltaRange ∧ D.thickness ≤ deltaMetric := by
    simpa only [deltaGraph,le_min_iff] using hGraphSmall
  have Hgraph := graph_rank_of_query h htau L L2 ref Hphysical hk he0 hc hcsmall hcUnit hcGap
    heta.le hetaSeed.le hseed hseedTau hzeta.le hzseed hg hgrid htauB rfl heGraph heps hceps hHalf rfl hgrain
    hcuts.1 hcuts.2.1 (Hmetric D.thickness h.1.2.1 hcuts.2.2) hNearE Hquery
  exact ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall.trans_le (min_le_left _ _),hGraphSmall,hK,hvol,hnear,
    ref,hDim,hCandidate,Hphysical,hNearE,Hgraph⟩

end NativeExtraGraphConfiguration
