import Theorems.Thm_StickyKakeya4_native_generic_graph_rank_data
import Theorems.Thm_StickyKakeya4_native_generic_history_dimension_range
import Theorems.Thm_StickyKakeya4_native_generic_query_rank
import Theorems.Thm_StickyKakeya4_native_generic_parent_graph
import Theorems.Thm_StickyKakeya4_native_generic_final_attachment
import Theorems.Thm_StickyKakeya4_native_generic_reference_queries
import Theorems.Thm_StickyKakeya4_native_retained_query_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7500000
noncomputable section

namespace NativeGenericGraphRank
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization
open NativeFixedCompactKakeyaExponent NativeJointUniformCoarseRelations NativeJointQuantitativeMenu
open NativeBalancedConfiguration NativeFixedSizeScaleMenu NativeLocalMenuInterpolation
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeConditionedPairMenu
open NativeMiddleTwoScaleConfiguration NativeMasterPointRelations NativeAllTwoScaleConfiguration
open NativeDirectionRankDichotomy NativeIncidentRankSelection NativeRankRadiusMenu
open NativeRankExponentHierarchy NativeReferenceCoreGlobalNear NativeRankOneExcludedFromSourceCost
open SelfUniform
open scoped BigOperators ENNReal

open NativeLocalPairUniformCore NativeLocalPairFibers NativeRankRefinedReferenceCore
open NativeRefinedRowRelations NativeRetainedRankCutoffs NativeSecondRefinementCost
open NativeTwoStageTransverseTuples NativeTwoStagePlaneRank NativeRankRadiusRounding
open NativeActualMesoscopicRankConfiguration

open NativeActualRetainedRankConfiguration NativeRetainedQueryMenu

open NativeGenericReferenceData NativeGenericReferenceSecondStage NativeGenericReferenceQueries

open NativeGenericReferenceData NativeGenericFinalAttachment NativeGenericParentGraph
open NativeRetainedGrainHistory NativeActualGrainHistory NativeMiddleGrainParentBudget NativeSquaredGrainQueries
open NativeGenericGraphRankData NativePhysicalReferenceData NativeGeneralRankScalarBudget

/-- Attach the actual compatible history, saturated parent and fixed graph
to one arbitrary enlarged reference. Every output uses its true first cost. -/
theorem graph_rank_of_query {n d J K Khalf g : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta eta0 c c2 epsilon : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau) (L L2 : ℕ)
    (ref : Reference h tau htau seed e zeta L g) (Hphysical : HasPhysicalUniformities ref)
    (hk : 0 < extremalExponent) (he0 : 0 < eta0) (hc : 0 < c) (hcsmall : c ≤ 1/2)
    (hcUnit : c ≤ 1/(eta0+1)) (hcGap : c ≤ positiveGap extremalExponent/(256*(eta0+1)))
    (heta : 0 ≤ eta) (hetaSeed : eta ≤ seed/8) (hseed : 0 < seed)
    (hseedTau : seed ≤ tau/16384) (hzeta : 0 ≤ zeta) (hzseed : zeta ≤ seed/256)
    (hg : 0 < g) (hgrid : 1/(g:ℝ) < rankWindow tau/4)
    (htauB : tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1))) (hc2 : c2=commonBudget eta0 c/4)
    (hepsilon : 0 < epsilon) (heps : eta0 ≤ epsilon) (hceps : c ≤ epsilon/24)
    (hHalf : 0 < Khalf) (hEven : J=2*Khalf) (hgrain : 1/((2*Khalf:ℕ):ℝ) ≤ epsilon/2)
    (hsmallRet : D.thickness ≤ retainedCutoff g J eta0 c he0 hc)
    (hsmallRange : D.thickness ≤ NativeHistoryDimensionRange.extraCutoff c hc
      (hcsmall.trans (by norm_num : (1/2:ℝ)≤1)) g)
    (hmetric : ∀ell : Fin 4,D.thickness^(cutoff c ell*epsilon) ≤ 1/NativeHeightMetricPower.normalizationConstant)
    (hE1Near : D.thickness^(-extremalExponent+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity ref.E1)
    (Hquery : NativeGenericQueryRank.HasQueriedRankSelection ref
      (NativeParentHorizontalQueryMenu.size d K) (NativeGenericCompatibleStage.pairedCount J) L2 eta0 c c2) :
    HasGraphRankSelection ref d J K Khalf L2 eta0 c c2 epsilon := by
  have hc1 : c ≤ 1 := hcsmall.trans (by norm_num)
  have hJ : 0 < J := by rw [hEven]; positivity
  obtain ⟨ell,j,hell,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hstopK,hSelect⟩ := Hquery
  have hsix : 6 ≤ (ref.schedule j).val := by omega
  have Hfinal (Rel : Fin (NativeParentHorizontalQueryMenu.size d K) → (Fin n × Index) → (Fin n × Index) → Prop)
      (hrefl : ∀i x,Rel i x x) (hsym : ∀i x y,Rel i x y → Rel i y x) :
      NativeGenericFinalHistory.HasPrescribedFinalStage (J:=J) h ref.original ref.R ref.E1 F P ref.a ref.level
        ref.schedule ref.dimension L L2 eta0 c tau seed htau c2 ell j Rel :=
    select_final_stage h htau L L2 ref F P eta0 c c2 ell j hJ he0 hc hcsmall heta hseed hseedTau hg hgrid
      htauB hc2 hsmallRet hFE1 hjmenu hsix hrcut hrhi hE1Near hSelect Rel hrefl hsym
  let Rel0 : Fin (NativeParentHorizontalQueryMenu.size d K) → (Fin n × Index) → (Fin n × Index) → Prop :=
    fun _ _ _ => True
  have Hhistory := NativeGenericFinalHistory.prescribed_final_stage_history h ref.original ref.R ref.E1 F P
    ref.a ref.level ref.schedule ref.dimension L L2 eta0 c tau seed htau c2 ell j Rel0
    (Hfinal Rel0 (by intro i x; trivial) (by intro i x y hxy; trivial))
  have hrange : extremalExponent+((ell.val+1:ℕ):ℝ) ≤ 4 :=
    NativeGenericHistoryDimensionRange.history_stage_dimension_range hJ he0 hc hc1 hcUnit hcGap htau htauB
      hseed.le hzeta hseedTau hzseed hc2 h heta hetaSeed L L2 ref Hphysical F hFE1 P hgrid
      ell j hjmenu hrcut Rel0 Hhistory hsmallRange
  have hne4 : ell.val+1≠4 := by
    intro hh
    rw [hh] at hrange
    norm_num at hrange
    linarith
  have hrank23 : ell.val+1=2 ∨ ell.val+1=3 := by omega
  let selected : Fin J := hEven.symm ▸ NativeGenericParentGraph.middleSelected Khalf hHalf
  have hmid : historyDepth J (ref.schedule j).val selected=middleDepth (ref.schedule j).val := by
    subst J
    exact NativeGenericParentGraph.middle_selected_depth Khalf hHalf (ref.schedule j).val hsix
  refine ⟨ell,j,hell,hrank23,hrange,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hstopK,hSelect,selected,hmid,?_⟩
  intro depths hdepths Rel hrefl hsym
  have hrf := NativeParentHorizontalQueryMenu.relations_refl h ref.R ref.a ref.level
    (historyDepth J (ref.schedule j).val selected) depths
    (NativeAnisotropicSliceLabels.slicePoint D ref.a (historyDepth J (ref.schedule j).val selected))
    (fun _p u => NativeAnisotropicSliceLabels.sliceClass (historyDepth J (ref.schedule j).val selected) (depths u)) Rel hrefl
  have hrs := NativeParentHorizontalQueryMenu.relations_symm h ref.R ref.a ref.level
    (historyDepth J (ref.schedule j).val selected) depths
    (NativeAnisotropicSliceLabels.slicePoint D ref.a (historyDepth J (ref.schedule j).val selected))
    (fun _p u => NativeAnisotropicSliceLabels.sliceClass (historyDepth J (ref.schedule j).val selected) (depths u)) Rel hsym
  have Hmenu := NativeGenericParentMenu.prescribed_stage_with_horizontal_menu h ref.original ref.R ref.E1 F P
    ref.a ref.level ref.schedule ref.dimension L L2 eta0 c tau seed htau c2 ell j selected depths
    (fun u => (hdepths u).2) Rel
    (Hfinal (NativeGenericParentMenu.callerRelations h ref.R ref.a ref.level ref.schedule j selected depths Rel) hrf hrs)
  have hstop := NativeSquaredGrainQueries.stopping_depth_cap htau g ref.level ref.schedule ref.schedule_eq j hjmenu
  have hsmall8 : D.thickness ≤ 1/8 := hsmallRange.trans
    (NativeHistoryDimensionRange.extraCutoff_spec c hc hc1 g).2.1
  have Hparent := NativeGenericSaturatedParent.saturated_stage_with_population_parent h ref.original ref.R ref.E1 F P
    ref.a ref.level ref.schedule ref.dimension L L2 eta0 c tau seed zeta htau c2 ell j selected depths Rel
    heta hJ hg ref.grid_depth hseedTau hgrid ref.backbone ref.schedule_eq ref.relations ref.core ref.cost
    ref.conditioned ref.pairs hFE1 hstop hdepths hsmall8 Hmenu
  exact NativeGenericParentGraph.saturated_stage_with_parent_graph h ref.original ref.R ref.E1 F P
    ref.a ref.level ref.schedule ref.dimension L L2 eta0 c tau seed zeta htau c2 ell j selected depths Khalf epsilon Rel
    hepsilon he0.le heps hc hc1 hceps hHalf hEven hgrain htauB hgrid hrcut hidentity (by omega)
    ref.backbone hmid (hmetric ell) Hparent

end NativeGenericGraphRank
