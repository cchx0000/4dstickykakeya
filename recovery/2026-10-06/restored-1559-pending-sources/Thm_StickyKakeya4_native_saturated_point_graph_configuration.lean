import Theorems.Thm_StickyKakeya4_native_saturated_parent_graph_configuration
import Theorems.Thm_StickyKakeya4_native_parent_original_point_menu
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 14000000
noncomputable section

namespace NativeSaturatedPointGraphConfiguration
open NativeSharpMixedGrainCore NativeSaturatedMixedGrainCore
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization NativeFixedCompactKakeyaExponent NativeJointUniformCoarseRelations
open NativeJointQuantitativeMenu NativeBalancedConfiguration NativeFixedSizeScaleMenu NativeLocalMenuInterpolation
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeConditionedPairMenu
open NativeMiddleTwoScaleConfiguration NativeMasterPointRelations NativeAllTwoScaleConfiguration
open NativeDirectionRankDichotomy NativeIncidentRankSelection NativeRankRadiusMenu NativeRankExponentHierarchy
open NativeLocalPairUniformCore NativeLocalPairFibers NativeRankRefinedReferenceCore NativeRefinedRowRelations
open NativeRetainedRankCutoffs NativeSecondRefinementCost NativeTwoStageTransverseTuples NativeTwoStagePlaneRank
open NativeRankRadiusRounding NativeActualMesoscopicRankConfiguration NativeActualRetainedRankConfiguration
open NativeRetainedQueryMenu NativeSquaredGrainQueries NativeActualQueryRankConfiguration
open NativeActualSquaredGrainSelection NativeCompatibleWeightedRetention SelfUniform
open scoped BigOperators ENNReal

open NativeActualCompatibleConfiguration NativeRetainedGrainHistory
open NativeActualAngularMenuCost NativeSourceSizeBounds NativeQueriedVertexWeights

open NativeActualHistoryConfiguration NativeHistoryGrainCleanup NativeActualGrainHistory
open NativeActualProjectedGrainCount NativeHistoryGrainCount NativeOriginalPacketReference
open NativeCompatibleNodeDirections RichDirectionalLayers WeightedRichDirectionalLayers
open NativeSpatialAngularGeometry NativeCompatibleAngularCandidates

open NativeActualFinalGrainConfiguration NativeGeneralRankScalarBudget
open NativeAnisotropicSliceLabels NativeCoarseShadingUniformity NativeCoarseDirectionThinning

open NativeActualParentMenuConfiguration NativeSaturatedPopulationParentProfiles
open NativePrescribedParentMenuConfiguration NativeSaturatedCompleteParentProfiles NativeOriginalAngularTupleMenu

open NativeSaturatedPopulationParentConfiguration NativeSaturatedParentGraphData
open NativeHeightMetricMenu NativeMiddleGrainParentBudget NativeHeightMetricPower

open NativeSaturatedParentGraphConfiguration

theorem exists_saturated_point_graph_configuration (d K Kmin : ℕ) (_hK : 0 < K)
    (hk : 0 < extremalExponent) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (Khalf : ℕ) (_hHalf : 0 < Khalf), Kmin ≤ Khalf ∧ 1/((2*Khalf:ℕ):ℝ) ≤ epsilon/2 ∧
    let J := 2*Khalf
    ∃ (eta0 : ℝ) (he0 : 0 < eta0), eta0 ≤ extremalExponent/2 ∧ eta0 ≤ epsilon ∧ eta0 ≤ 1/1000 ∧
    ∃ (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1), c ≤ 1/8 ∧ c ≤ 1/(eta0+1) ∧
      c ≤ positiveGap extremalExponent/(256*(eta0+1)) ∧ c ≤ epsilon/24 ∧ c ≤ 1/64 ∧
    ∃ (tau : ℝ) (htau : 0 < tau) (seed e zeta : ℝ) (L g L2 : ℕ) (c2 : ℝ),
      tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1)) ∧ tau ≤ commonBudget eta0 c / 1024 ∧ tau ≤ 1 / 2 ∧
      0 < seed ∧ seed ≤ tau / 16384 ∧ 0 < e ∧ 0 < zeta ∧
      zeta ≤ seed / 256 ∧ 0 < L ∧ 0 < g ∧
      1 / (g : ℝ) < rankWindow tau / 4 ∧
      0 < L2 ∧ c2=commonBudget eta0 c/4 ∧
      ∃ deltaRet : ℝ, 0 < deltaRet ∧ deltaRet ≤ 1 ∧
      deltaRet ≤ historyCutoff J (commonBudget eta0 c) (commonBudget_pos he0 hc) ∧
      deltaRet ≤ historyCutoff (J+1) (commonBudget eta0 c) (commonBudget_pos he0 hc) ∧
      deltaRet ≤ NativeHistoryDimensionRange.extraCutoff c hc hc1 g ∧ deltaRet ≤ 1/8 ∧
      (∀delta : ℝ,0 < delta → delta ≤ deltaRet → ∀i : Fin 4,
        delta^(cutoff c i*epsilon) ≤ 1/NativeHeightMetricPower.normalizationConstant) ∧
      ∀ etaBound deltaBound extraCutoff : ℝ,
        0 < etaBound → 0 < deltaBound → 0 < extraCutoff →
      ∃ (eta : ℝ) (n : ℕ) (D : FiniteScaleSource n)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0 < eta ∧ eta < etaBound ∧ eta < seed / 8 ∧ D.thickness < deltaBound ∧
        D.thickness < extraCutoff ∧ D.thickness ≤ deltaRet ∧
        (∀ i, D.line i ∈ fixedCompactClass) ∧
        volume (sourceUnion D) ≤ (ENNReal.ofReal D.thickness).rpow (extremalExponent - eta) ∧
        D.thickness ^ (-extremalExponent + eta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal ∧
        ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n))
          (original : Fin n → Finset Index) (E1 : Finset (Fin n × Index))
          (schedule : Fin (g + 1) → Fin (level + 1)),
          HasOriginalBackbone D original R a level zeta ∧ g ≤ level ∧
          schedule = fullSchedule tau htau g level ∧
          IsCore D original R a eta zeta (menuSize (pairMenuSize (1 + (g + 1)) (g + 1)) (g + 1))
            (g + 1) L (relationMenu h R a schedule (pairRelationMenu h R a schedule
              (masterRelations D a schedule))) (fun j => 2 ^ (schedule j).val) E1 ∧
          (125 * 175616 * 16384 : ℝ) *
            (factor (menuSize (pairMenuSize (1 + (g + 1)) (g + 1)) (g + 1)) (g + 1) L : ℝ) *
            (coreRadix original R L : ℝ) ^ 2 * D.thickness ^ (-eta) ≤ D.thickness ^ (-(seed / 8)) ∧
          HasUniformFibers E1 (coreRadix original R L) Prod.snd ∧
          (∀ j x y, x ∈ E1 → y ∈ E1 →
            degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2 ^ (schedule j).val)) E1 x ≤
              (coreRadix original R L) ^ 2 *
                degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2 ^ (schedule j).val)) E1 y) ∧
          (∀ i j, HasUniformFibers E1 (coreRadix original R L)
              (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
            HasUniformFibers E1 (coreRadix original R L)
              (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val)) ∧
          (∀ j, HasJointScale h R E1 a level (schedule j).val e zeta (seed / 8) (seed / 8) ∧
            HasBalancedScale h R E1 a level (schedule j).val seed) ∧
          (∀ m : ℕ, boundaryWindow tau * (level : ℝ) ≤ m →
            (m : ℝ) ≤ (1 - boundaryWindow tau) * (level : ℝ) →
            HasMiddleScale h R E1 a level m (tau / 16)) ∧
          (∀ m f : ℕ, m ≤ f → f ≤ level → HasConditionalTwoScale h R E1 a level m f tau) ∧
          D.thickness ^ (-extremalExponent + seed / 4) ≤
            NativeIncidenceMultiplicityTower.multiplicity E1 ∧
          ∃ (ell : Fin 4) (j : Fin (g + 1)), 1 ≤ ell.val ∧ (ell.val+1=2 ∨ ell.val+1=3) ∧
            extremalExponent+((ell.val+1:ℕ):ℝ) ≤ 4 ∧
            j ∈ NativeRankMesoscopicRadiusMenu.menu (rankWindow tau) (rankWindow_pos htau).le g level ∧
            let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
            r ≤ D.thickness ^ (cutoff c ell) ∧ D.thickness ≤ r ∧ r ≤ 1 / 4 ∧
            48 * ((2 ^ (schedule j).val : ℕ) : ℝ) * r = 1 ∧
            ((2 ^ (schedule j).val : ℕ) : ℝ) * D.thickness ≤ 1 ∧ 64 * D.thickness ≤ r ^ 2 ∧
            ∃ F ⊆ E1, F.Nonempty ∧
              (r ^ (rankLoss eta0 c ell) / (4 * ((g : ℝ) + 1))) * (E1.card : ℝ) ≤ (F.card : ℝ) ∧
              ∃ P : Index → Submodule ℝ E4,
                (∀ z ∈ F, Metric.infDist (slopeVector D z.1) (P z.2 : Set E4) ≤ r) ∧
                (∀ k ∈ F.image Prod.snd,
                  Module.finrank ℝ (P k) ≤ ell.val + 1 ∧
                  pointSet F k = pointNear D E1 k r (P k) ∧
                  r ^ (rankLoss eta0 c ell) * ((pointSet E1 k).card : ℝ) ≤ (pointSet F k).card ∧
                  ∀ ell' : Fin 4, ell' < ell →
                    ∀ j' ∈ NativeRankMesoscopicRadiusMenu.menu
                      (rankWindow tau) (rankWindow_pos htau).le g level,
                    radius (rankWindow tau) (rankWindow_pos htau).le g level j' ≤
                      D.thickness ^ (cutoff c ell') →
                    ∀ Q : Submodule ℝ E4, Module.finrank ℝ Q ≤ ell'.val + 1 →
                      ((pointNear D E1 k (radius (rankWindow tau) (rankWindow_pos htau).le g level j') Q).card : ℝ) <
                        (radius (rankWindow tau) (rankWindow_pos htau).le g level j') ^ (rankLoss eta0 c ell') *
                          ((pointSet E1 k).card : ℝ)) ∧
                (pairedCount J)+6 ≤ (schedule j).val ∧
                (∀ queries : Fin (pairedCount J) → ℕ × ℕ,
                  (∀i,(queries i).2 ≤ (queries i).1 ∧ (queries i).1 ≤ level) →
                ∀ Rel : Fin (NativeParentHorizontalQueryMenu.size (d+1) K) → (Fin n × Index) → (Fin n × Index) → Prop,
                  (∀i x,Rel i x x) → (∀i x y,Rel i x y → Rel i y x) →
                  HasQuerySecondStageCore h original R E1 F P a level queries schedule L L2
                    eta0 c tau htau c2 ell j Rel) ∧
                ∃ selected : Fin J,historyDepth J (schedule j).val selected=middleDepth (schedule j).val ∧
                ∀depths : Fin K → ℕ,
                  (∀u,historyDepth J (schedule j).val selected ≤ depths u ∧
                    depths u ≤ phaseDepth (historyDepth J (schedule j).val selected)) →
                  (∃u,depths u=historyDepth J (schedule j).val selected) →
                ∀ Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop,
                  (∀i x,Rel i x x) → (∀i x y,Rel i x y → Rel i y x) →
                  HasSaturatedCurveParentStage (J:=J) h original R E1 F P a level schedule L L2
                    eta0 c tau seed zeta htau c2 ell j selected depths Khalf epsilon
                    (NativeParentOriginalPointMenu.relations D a
                      (historyDepth J (schedule j).val selected) Rel) := by
  obtain ⟨Khalf,hHalf,hKmin,hgrain⟩ := NativeHeightMetricPower.exists_grain_count epsilon hepsilon Kmin
  refine ⟨Khalf,hHalf,hKmin,hgrain,?_⟩
  let J := 2*Khalf
  have hJ : 0 < J := by dsimp [J]; positivity
  obtain ⟨eta0,he0,heK,heeps,he1000,c,hc,hc1,hc8,hcUnit,hcGap,hceps,hc64,
    tau,htau,seed,e,zeta,L,g,L2,c2,htauB,htauT,htauHalf,hseed,hseedTau,
    he,hzeta,hzseed,hL,hg,hgrid,hL2,hc2,deltaRet,hdRet,hdRet1,hdRetHistory,hdRetCleanup,hdRetRange,hdRet8,hsource⟩ :=
    NativeSaturatedPopulationParentConfiguration.exists_saturated_population_parent_configuration
      (d+1) J K hJ _hK hk epsilon hepsilon
  obtain ⟨deltaMetric,hdMetric,_hdMetric8,hMetricCut⟩ := exists_uniform_metric_cutoff c epsilon hc hc1 hepsilon
  refine ⟨eta0,he0,heK,heeps,he1000,c,hc,hc1,hc8,hcUnit,hcGap,hceps,hc64,
    tau,htau,seed,e,zeta,L,g,L2,c2,htauB,htauT,htauHalf,hseed,hseedTau,
    he,hzeta,hzseed,hL,hg,hgrid,hL2,hc2,min deltaRet deltaMetric,
    lt_min hdRet hdMetric,(min_le_left _ _).trans hdRet1,
    (min_le_left _ _).trans hdRetHistory,(min_le_left _ _).trans hdRetCleanup,
    (min_le_left _ _).trans hdRetRange,(min_le_left _ _).trans hdRet8,?_,?_⟩
  · exact fun delta hd hsmall => hMetricCut delta hd (hsmall.trans (min_le_right _ _))
  intro etaBound deltaBound extraCutoff heB hdB hExtra
  obtain ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hExtraOld,hRet,hK,hvol,hnear,
    a,level,R,original,E1,schedule,hBackbone,hgl,hSchedule,hCore,hCost1,
    hPoint,hOld,hConditioned,hScales,hMiddle,hAllPairs,hE1Near,
    ell,j,hell,hrank23,hrange,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hstopK,hSelect,hParents⟩ :=
    hsource etaBound deltaBound (min extraCutoff deltaMetric) heB hdB (lt_min hExtra hdMetric)
  have hDMetric : D.thickness ≤ deltaMetric := hExtraOld.le.trans (min_le_right _ _)
  have hExtraSmall : D.thickness < extraCutoff := hExtraOld.trans_le (min_le_left _ _)
  let selected : Fin J := middleSelected Khalf hHalf
  have hs : 6 ≤ (schedule j).val := by omega
  have hmid : historyDepth J (schedule j).val selected=middleDepth (schedule j).val :=
    middle_selected_depth Khalf hHalf (schedule j).val hs
  refine ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hExtraSmall,le_min hRet hDMetric,hK,hvol,hnear,
    a,level,R,original,E1,schedule,hBackbone,hgl,hSchedule,hCore,hCost1,
    hPoint,hOld,hConditioned,hScales,hMiddle,hAllPairs,hE1Near,
    ell,j,hell,hrank23,hrange,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hstopK,hSelect,selected,hmid,?_⟩
  intro depths hdepths hcoarse Rel hrefl hsymm
  let RelPlus := NativeParentOriginalPointMenu.relations D a
    (historyDepth J (schedule j).val selected) Rel
  have hPlusRefl := NativeParentOriginalPointMenu.relations_refl D a
    (historyDepth J (schedule j).val selected) Rel hrefl
  have hPlusSymm := NativeParentOriginalPointMenu.relations_symm D a
    (historyDepth J (schedule j).val selected) Rel hsymm
  exact saturated_stage_with_parent_graph h original R E1 F P a level schedule L L2 eta0 c tau seed zeta htau c2 ell j
    selected depths Khalf epsilon RelPlus hepsilon he0.le heeps hc hc1 hceps hHalf rfl hgrain htauB hgrid
    hrcut hidentity (by omega) hBackbone hmid (hMetricCut D.thickness h.1.2.1 hDMetric ell)
    (hParents selected depths hdepths hcoarse RelPlus hPlusRefl hPlusSymm)

end NativeSaturatedPointGraphConfiguration
