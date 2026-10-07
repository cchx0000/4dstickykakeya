import Theorems.Thm_StickyKakeya4_native_actual_final_grain_configuration
import Theorems.Thm_StickyKakeya4_native_history_dimension_range

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 14000000
noncomputable section

namespace NativeActualDimensionRangeConfiguration
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

/-- Choose one finite positive-gap hierarchy before the master tolerance,
then derive the actual dimension range on an original near-extremal source.
Zero-gap branches remain admissible. Every final grain output is retained. -/
theorem exists_actual_dimension_range_configuration (d J : ℕ) (hJ : 0 < J) (hk : 0 < extremalExponent)
    (eta0 : ℝ) (he0 : 0 < eta0) (heK : eta0 ≤ extremalExponent / 2) :
    ∃ (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1), c ≤ 1/8 ∧ c ≤ 1/(eta0+1) ∧
      c ≤ positiveGap extremalExponent/(256*(eta0+1)) ∧
    ∃ (tau : ℝ) (htau : 0 < tau) (seed e zeta : ℝ) (L g L2 : ℕ) (c2 : ℝ),
      tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1)) ∧ tau ≤ commonBudget eta0 c / 1024 ∧ tau ≤ 1 / 2 ∧
      0 < seed ∧ seed ≤ tau / 16384 ∧ 0 < e ∧ 0 < zeta ∧
      zeta ≤ seed / 256 ∧ 0 < L ∧ 0 < g ∧
      1 / (g : ℝ) < rankWindow tau / 4 ∧
      0 < L2 ∧ c2=commonBudget eta0 c/4 ∧
      ∃ deltaRet : ℝ, 0 < deltaRet ∧ deltaRet ≤ 1 ∧
      deltaRet ≤ historyCutoff J (commonBudget eta0 c) (commonBudget_pos he0 hc) ∧
      deltaRet ≤ historyCutoff (J+1) (commonBudget eta0 c) (commonBudget_pos he0 hc) ∧
      deltaRet ≤ NativeHistoryDimensionRange.extraCutoff c hc hc1 g ∧
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
                ∀ Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop,
                  (∀i x,Rel i x x) → (∀i x y,Rel i x y → Rel i y x) →
                  HasQuerySecondStageCore h original R E1 F P a level queries schedule L L2
                    eta0 c tau htau c2 ell j Rel) ∧
                ∀ Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop,
                  (∀i x,Rel i x x) → (∀i x y,Rel i x y → Rel i y x) →
                  HasFinalGrainSquaredStage (J:=J) h original R E1 F P a level schedule L L2
                    eta0 c tau seed htau c2 ell j Rel := by
  obtain ⟨c,hc,hc8,hcUnit,hcGap⟩ := exists_uniform_hierarchy extremalExponent eta0 hk he0.le
  have hc1 : c ≤ 1 := hc8.trans (by norm_num : (1/8:ℝ)≤1)
  refine ⟨c,hc,hc1,hc8,hcUnit,hcGap,?_⟩
  obtain ⟨tau,htau,seed,e,zeta,L,g,L2,c2,htauB,htauT,htauHalf,hseed,hseedTau,
    he,hzeta,hzseed,hL,hg,hgrid,hL2,hc2,deltaRet,hdRet,hdRet1,hdRetHistory,hdRetCleanup,hsource⟩ :=
    NativeActualFinalGrainConfiguration.exists_actual_final_grain_configuration
      d J hJ hk eta0 c he0 heK hc (hc8.trans (by norm_num : (1/8:ℝ)≤1/2))
  let deltaRange := NativeHistoryDimensionRange.extraCutoff c hc hc1 g
  have hdRange : 0 < deltaRange := (NativeHistoryDimensionRange.extraCutoff_spec c hc hc1 g).1
  refine ⟨tau,htau,seed,e,zeta,L,g,L2,c2,htauB,htauT,htauHalf,hseed,hseedTau,
    he,hzeta,hzseed,hL,hg,hgrid,hL2,hc2,min deltaRet deltaRange,
    lt_min hdRet hdRange,(min_le_left _ _).trans hdRet1,
    (min_le_left _ _).trans hdRetHistory,(min_le_left _ _).trans hdRetCleanup,min_le_right _ _,?_⟩
  intro etaBound deltaBound extraCutoff heB hdB hExtra
  obtain ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hExtraOld,hRet,hK,hvol,hnear,
    a,level,R,original,E1,schedule,hBackbone,hgl,hSchedule,hCore,hCost1,
    hPoint,hOld,hConditioned,hScales,hMiddle,hAllPairs,hE1Near,
    ell,j,hell,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hstopK,hSelect,hFinal⟩ :=
    hsource etaBound deltaBound (min extraCutoff deltaRange) heB hdB (lt_min hExtra hdRange)
  have hRangeSmall : D.thickness ≤ deltaRange := hExtraOld.le.trans (min_le_right _ _)
  have hExtraSmall : D.thickness < extraCutoff := hExtraOld.trans_le (min_le_left _ _)
  let Rel0 : Fin d → (Fin n × Index) → (Fin n × Index) → Prop := fun _ _ _ => True
  have Hfinal := hFinal Rel0 (by intro i x; trivial) (by intro i x y hxy; trivial)
  have Hhistory := final_stage_history h original R E1 F P a level schedule L L2
    eta0 c tau seed htau c2 ell j Rel0 Hfinal
  have hrange : extremalExponent+((ell.val+1:ℕ):ℝ) ≤ 4 :=
    NativeHistoryDimensionRange.history_stage_dimension_range
      hJ he0 hc hc1 hcUnit hcGap htau htauB hseed.le hzeta.le hseedTau hzseed hc2
      h heta.le hetaSeed.le original R E1 F hFE1 P level L L2 schedule hSchedule hgrid
      hBackbone hCore hCost1 hMiddle ell j hjmenu hrcut (hScales j).2 Rel0 Hhistory hRangeSmall
  have hne4 : ell.val+1≠4 := by
    intro hh
    rw [hh] at hrange
    norm_num at hrange
    linarith
  have hrank23 : ell.val+1=2 ∨ ell.val+1=3 := by omega
  exact ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hExtraSmall,le_min hRet hRangeSmall,hK,hvol,hnear,
    a,level,R,original,E1,schedule,hBackbone,hgl,hSchedule,hCore,hCost1,
    hPoint,hOld,hConditioned,hScales,hMiddle,hAllPairs,hE1Near,
    ell,j,hell,hrank23,hrange,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hstopK,hSelect,hFinal⟩

/-- The actual finite source construction and its dimension range improve the
unconditional fixed-compact critical exponent upper bound to two. -/
theorem extremalExponent_le_two : extremalExponent ≤ 2 := by
  by_cases hk : 0 < extremalExponent
  · obtain ⟨c,hc,hc1,_hc8,_hcUnit,_hcGap,tau,htau,seed,e,zeta,L,g,L2,c2,
      _htauB,_htauT,_htauHalf,_hseed,_hseedTau,_he,_hzeta,_hzseed,_hL,_hg,_hgrid,_hL2,_hc2,
      deltaRet,_hdRet,_hdRet1,_hdRetHistory,_hdRetCleanup,_hdRetRange,hsource⟩ :=
      exists_actual_dimension_range_configuration 0 1 (by norm_num) hk
        (extremalExponent/2) (by positivity) le_rfl
    obtain ⟨eta,n,D,h,_heta,_hetaB,_hetaSeed,_hsmall,_hExtraOld,_hRet,_hK,_hvol,_hnear,
      a,level,R,original,E1,schedule,_hBackbone,_hgl,_hSchedule,_hCore,_hCost1,
      _hPoint,_hOld,_hConditioned,_hScales,_hMiddle,_hAllPairs,_hE1Near,
      ell,j,hell,_hrank23,hrange,_hrest⟩ :=
      hsource 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    have hdim : (2:ℝ) ≤ ((ell.val+1:ℕ):ℝ) := by exact_mod_cast (show 2 ≤ ell.val+1 by omega)
    linarith
  · linarith

end NativeActualDimensionRangeConfiguration
