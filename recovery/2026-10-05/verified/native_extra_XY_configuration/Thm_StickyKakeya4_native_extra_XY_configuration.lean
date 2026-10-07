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
namespace NativeExtraXYConfiguration
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
open scoped ENNReal

open NativeExtraGraphConfiguration NativeGenericXYRank NativeRetainedSliceBudget NativeRetainedSliceCore
theorem exists_extra_XY_configuration (d Jhorizontal d3 Khalf : ℕ) (extraCount : ℕ → ℕ)
    (hHalf3 : 3 ≤ Khalf) (hHorizontal : 0 < Jhorizontal) (hk : 0 < extremalExponent)
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
      ∃L3 : ℕ,0 < L3 ∧ ∃delta3 : ℝ,0 < delta3 ∧ delta3 ≤ 1 ∧
      ∀menu : MenuFactory g (extraCount g),MenuRefl menu → MenuSymm menu →
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
          D.thickness^(-extremalExponent+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity ref.E1 ∧
          (∀U⊆incidences ref.original,U.Nonempty →
            (refinementCost (d3+2) (Jhorizontal+1) L3:ℝ)*
              (NativeSourceSizeBounds.radix U.card L3:ℝ)^4 ≤ D.thickness^(-(commonBudget eta0 c/4))) ∧
          HasXYRankSelection ref d (2*Khalf) Jhorizontal d3 Khalf L2 L3 eta0 c (commonBudget eta0 c/4) epsilonGraph := by
  have hHalf : 0 < Khalf := by omega
  obtain ⟨tau,htau,seed,e,zeta,L,g,L2,
    htauBound,htauB,htauT,htauHalf,htauC,hseed,hseedTau,he,hzeta,hzseed,hL,hg,hgrid,hL2,
    deltaGraph,hdGraph,hdGraph8,Hsource⟩ :=
    exists_extra_graph_configuration d (Jhorizontal+1) Khalf extraCount hHalf hk eta0 c epsilonGraph
      he0 heK hc hcsmall hcUnit hcGap heGraph heps hceps hgrain
      tauBound hTauBound
  let cost3 := commonBudget eta0 c/4
  have hcost3 : 0 < cost3 := div_pos (commonBudget_pos he0 hc) (by norm_num)
  obtain ⟨L3,hL3,delta3,hd3,hd31,Hbudget⟩ := exists_retained_slice_budget cost3 hcost3 (d3+2) (Jhorizontal+1)
  refine ⟨tau,htau,seed,e,zeta,L,g,L2,
    htauBound,htauB,htauT,htauHalf,htauC,hseed,hseedTau,he,hzeta,hzseed,hL,hg,hgrid,hL2,
    deltaGraph,hdGraph,hdGraph8,L3,hL3,delta3,hd3,hd31,?_⟩
  intro menu hMenuRefl hMenuSymm etaBound deltaBound heB hdB
  obtain ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hGraphSmall,hK,hvol,hnear,
    ref,hDim,hCandidate,Hphysical,hNearE,Hgraph⟩ :=
    Hsource menu hMenuRefl hMenuSymm (min etaBound (cost3/8)) (min deltaBound delta3)
      (lt_min heB (div_pos hcost3 (by norm_num))) (lt_min hdB hd3)
  have heta3 : eta < cost3/8 := hetaB.trans_le (min_le_right _ _)
  have hd3small : D.thickness ≤ delta3 := hsmall.le.trans (min_le_right _ _)
  have HXY := xy_rank_of_graph (d3:=d3) h htau L L2 L3 ref heta.le hseedTau hg hgrid
    (hGraphSmall.trans hdGraph8) hHalf3 rfl hHorizontal hL3 Hgraph
  refine ⟨eta,n,D,h,heta,hetaB.trans_le (min_le_left _ _),hetaSeed,heta3,
    hsmall.trans_le (min_le_left _ _),hGraphSmall,hd3small,hK,hvol,hnear,
    ref,hDim,hCandidate,Hphysical,hNearE,?_,HXY⟩
  exact Hbudget n D eta h hd3small heta.le heta3.le ref.original ref.backbone.1

end NativeExtraXYConfiguration
