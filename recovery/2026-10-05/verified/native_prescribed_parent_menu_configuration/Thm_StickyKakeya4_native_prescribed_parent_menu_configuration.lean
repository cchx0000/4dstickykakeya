import Theorems.Thm_StickyKakeya4_native_actual_parent_menu_configuration
import Theorems.Thm_StickyKakeya4_native_prescribed_final_configuration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 14000000
noncomputable section

namespace NativePrescribedParentMenuConfiguration
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
open NativePrescribedFinalConfiguration NativePrescribedHistoryConfiguration

def HasPrescribedHorizontalStage {n d J g K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index))
    (P : Index → Submodule ℝ E4) (a : ℝ) (level : ℕ)
    (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau seed : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (selected : Fin J) (depths : Fin K → ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) : Prop :=
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
  let lambda := r^(rankLoss eta0 c ell)/(4*((g:ℝ)+1))
  let F1 := factor (menuSize (pairMenuSize (1+(g+1)) (g+1)) (g+1)) (g+1) L
  let G := retentionCost ((NativeParentHorizontalQueryMenu.size d K+((J+1)+(J+1))+((J+1)+(J+1))+((J+1)+(J+1))+1)+(g+1)*(g+1)) 1 L2
  let F2 := factor ((NativeParentHorizontalQueryMenu.size d K+((J+1)+(J+1))+((J+1)+(J+1))+((J+1)+(J+1))+1)+(g+1)*(g+1)) 1 L2
  let Q2 := NativeSourceSizeBounds.radix F.card L2
  ∃ previous : Fin 4, previous.val+1=ell.val ∧
    ∃ test ∈ NativeRankMesoscopicRadiusMenu.allowed D.thickness (rankWindow tau)
        (rankWindow_pos htau).le g level (cutoff c previous),
      let q := radius (rankWindow tau) (rankWindow_pos htau).le g level test
      r ≤ q ∧ q ≤ r^(2*c) ∧ r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q ∧
      ∃ E2 ⊆ F, E2.Nonempty ∧ E2 ⊆ retained original R ∧ F.card ≤ G*E2.card ∧
        lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card ∧
        lambda/((F1:ℝ)*G)*NativeIncidenceMultiplicityTower.multiplicity (incidences original) ≤
          NativeIncidenceMultiplicityTower.multiplicity E2 ∧
        (∀i x y,x∈E2 → y∈E2 → degree (fun _ : Fin n × Index => 1) (Rel i) E2 x ≤
          Q2^2*degree (fun _ : Fin n × Index => 1) (Rel i) E2 y) ∧
        (∀i : Fin (J+1),
          let m := grainDepth J (schedule j).val i
          let b := phaseDepth m
          let Delta := (64:ℝ)/((2^m:ℕ):ℝ)
          let rep := NativeCoarseDirectionThinning.representative h R a (2^b)
          6 ≤ m ∧ m ≤ b ∧ b ≤ level ∧ 0 < Delta ∧ Delta ≤ 1 ∧
          (64:ℝ)/((2^b:ℕ):ℝ)=Delta^2 ∧ (1:ℝ)/((2^b:ℕ):ℝ) ≤ Delta^2 ∧
          D.thickness ≤ Delta^2 ∧
          Delta/((64:ℝ)/((2^b:ℕ):ℝ))=1/Delta ∧
          HasUniformFibers E2 Q2 (NativeCoarseShadingUniformity.fixedPair D a level b b rep) ∧
          HasUniformFibers E2 Q2 (NativeCoarseShadingUniformity.fixedPair D a level b m rep) ∧
          HasUniformFibers E2 Q2 (fun z => NativeSpatialAngularGeometry.spatialLabel D (2^b) z.2) ∧
          HasUniformFibers E2 Q2 (fun z => NativeSpatialAngularGeometry.spatialLabel D (2^m) z.2)) ∧
        HasUniformFibers E2 Q2 Prod.snd ∧
        (∀i j,HasUniformFibers E2 Q2 (rowPair h R a schedule i j)) ∧
        (∀e,e∈E2 → D.thickness^eta*(2^level:ℕ)/
          (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
          (pairFiber D a (2^level) E2 (localPair D a (2^level) e)).card) ∧
        (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤
          D.thickness^(-c2) ∧
        (∀k∈E2.image Prod.snd,Module.finrank ℝ (P k)=ell.val+1) ∧
        (∀k∈E2.image Prod.snd,
          let A := pointSet E2 k
          let v := fun z : Fin n × Index => slopeVector D z.1
          let C := NativeDirectionRankDichotomy.chains A v q (ell.val+1)
          C.Nonempty ∧ ((A.card:ℝ)/2)^(ell.val+1) ≤ (C.card:ℝ) ∧
            ∀xs∈C,xs.length=ell.val+1 ∧ (∀z∈xs,z∈E2 ∧ z.2=k) ∧
              NativeDirectionRankDichotomy.Separated v q xs ∧
              LinearIndependent ℝ (fun i : Fin xs.length => v (xs.get i)) ∧
              q^(2*(ell.val+1)) ≤ (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det) ∧
        (∀w : Index → ℕ, NativeCompatibleWeightedRetention.RetainedFamily D a (schedule j).val E2 q
          (ell.val+1) w J (r^(2*((ell.val+1:ℕ):ℝ)*rankLoss eta0 c ell))) ∧
        HasPrescribedFinalRetainedHistory h a (schedule j).val E2 q (ell.val+1) J Q2
          r (rankLoss eta0 c ell) lambda (seed/8) c2
 ∧
        (∀u : Fin K,HasUniformFibers E2 Q2
          (fixedPair D a level (depths u) (depths u) (representative h R a (2^(depths u)))) ∧
          HasUniformFibers E2 Q2 (fixedPair D a level (depths u)
            (historyDepth J (schedule j).val selected) (representative h R a (2^(depths u))))) ∧
        (∀p : Parent,
          HasUniformFibers (parentEdges D a (2^(historyDepth J (schedule j).val selected)) E2 p) Q2
            (fun z => slicePoint D a (historyDepth J (schedule j).val selected) p z.2) ∧
          ∀u : Fin K,HasUniformFibers
            (parentEdges D a (2^(historyDepth J (schedule j).val selected)) E2 p) Q2
            (fun z => NativeAnisotropicShortRowGeometry.columnLabel D a
              (2^(historyDepth J (schedule j).val selected)) p (64/((2^(depths u):ℕ):ℝ))
              (64/((2^(historyDepth J (schedule j).val selected):ℕ):ℝ)) z.2)) ∧
        ∀p : Parent,∀u : Fin K,
          let A := (parentEdges D a (2^(historyDepth J (schedule j).val selected)) E2 p).image
            (fun z => slicePoint D a (historyDepth J (schedule j).val selected) p z.2)
          ∀x∈A,∀y∈A,
            (A.filter (fun z => sliceClass (historyDepth J (schedule j).val selected) (depths u) z=
              sliceClass (historyDepth J (schedule j).val selected) (depths u) x)).card ≤
            Q2^4*(A.filter (fun z => sliceClass (historyDepth J (schedule j).val selected) (depths u) z=
              sliceClass (historyDepth J (schedule j).val selected) (depths u) y)).card

/-- Exact additional relations on the actual original source; the dimension
is fixed before the values of the source-dependent horizontal depths. -/
def callerRelations {n d J g K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (level : ℕ)
    (schedule : Fin (g+1) → Fin (level+1)) (j : Fin (g+1)) (selected : Fin J) (depths : Fin K → ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) :
    Fin (NativeParentHorizontalQueryMenu.size d K) → (Fin n × Index) → (Fin n × Index) → Prop :=
  let m := historyDepth J (schedule j).val selected
  NativeParentHorizontalQueryMenu.relations h R a level m depths (slicePoint D a m)
    (fun _p u => sliceClass m (depths u)) Rel

/-- Decode the additional actual maps without reselecting E2 or its history. -/
theorem prescribed_stage_with_horizontal_menu {n d J g K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index)) (P : Index → Submodule ℝ E4)
    (a : ℝ) (level : ℕ) (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau seed : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (selected : Fin J) (depths : Fin K → ℕ)
    (hdepths : ∀u,depths u ≤ phaseDepth (historyDepth J (schedule j).val selected))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : HasPrescribedFinalStage (J:=J) h original R E1 F P a level schedule L L2 eta0 c tau seed htau c2 ell j
      (callerRelations h R a level schedule j selected depths Rel)) :
    HasPrescribedHorizontalStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed htau c2 ell j selected depths Rel := by
  obtain ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,hFinal⟩ := H
  let m := historyDepth J (schedule j).val selected
  let Q := NativeSourceSizeBounds.radix F.card L2
  obtain ⟨hOld,hQueries,hParent,hCounts⟩ := NativeParentHorizontalQueryMenu.uniformities h R a level m depths
    (slicePoint D a m) (fun _p u => sliceClass m (depths u)) Rel E2 Q hCaller
  refine ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hOld,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,hFinal,hQueries,?_,hCounts⟩
  intro p
  refine ⟨(hParent p).1,?_⟩
  intro u
  apply NativeConditionedPairMenu.uniformity_congr _ _ _ Q
    (fun z _hz => sliceClass_point_eq_column D a m (depths u) (hdepths u) p z.2)
  exact (hParent p).2 u

/-- Fix the menu cardinal before tau/g, then install source-dependent actual
horizontal depths before ONE E2. The small-loss hierarchy, all original source
fields, the dimension range and the exact final grain history are preserved. -/
theorem exists_prescribed_parent_menu_configuration (d J K : ℕ) (hJ : 0 < J) (_hK : 0 < K)
    (hk : 0 < extremalExponent) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
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
                ∀ Rel : Fin (NativeParentHorizontalQueryMenu.size d K) → (Fin n × Index) → (Fin n × Index) → Prop,
                  (∀i x,Rel i x x) → (∀i x y,Rel i x y → Rel i y x) →
                  HasQuerySecondStageCore h original R E1 F P a level queries schedule L L2
                    eta0 c tau htau c2 ell j Rel) ∧
                ∀ selected : Fin J,∀depths : Fin K → ℕ,
                  (∀u,historyDepth J (schedule j).val selected ≤ depths u ∧
                    depths u ≤ phaseDepth (historyDepth J (schedule j).val selected)) →
                  (∃u,depths u=historyDepth J (schedule j).val selected) →
                ∀ Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop,
                  (∀i x,Rel i x x) → (∀i x y,Rel i x y → Rel i y x) →
                  HasPrescribedHorizontalStage (J:=J) h original R E1 F P a level schedule L L2
                    eta0 c tau seed htau c2 ell j selected depths Rel := by
  let eta0 := min (extremalExponent/2) (min epsilon (1/1000))
  have he0 : 0 < eta0 := lt_min (by positivity) (lt_min hepsilon (by norm_num))
  have heK : eta0 ≤ extremalExponent/2 := min_le_left _ _
  have heeps : eta0 ≤ epsilon := (min_le_right _ _).trans (min_le_left _ _)
  have he1000 : eta0 ≤ 1/1000 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨c0,hc0,hc08,hc0Unit,hc0Gap⟩ := exists_uniform_hierarchy extremalExponent eta0 hk he0.le
  let c := min c0 (min (epsilon/24) (1/64))
  have hc : 0 < c := lt_min hc0 (lt_min (by positivity) (by norm_num))
  have hcc0 : c ≤ c0 := min_le_left _ _
  have hc8 : c ≤ 1/8 := hcc0.trans hc08
  have hc1 : c ≤ 1 := hc8.trans (by norm_num : (1/8:ℝ)≤1)
  have hcUnit := hcc0.trans hc0Unit
  have hcGap := hcc0.trans hc0Gap
  have hceps : c ≤ epsilon/24 := (min_le_right _ _).trans (min_le_left _ _)
  have hc64 : c ≤ 1/64 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨eta0,he0,heK,heeps,he1000,c,hc,hc1,hc8,hcUnit,hcGap,hceps,hc64,?_⟩
  obtain ⟨tau,htau,seed,e,zeta,L,g,L2,c2,htauB,htauT,htauHalf,hseed,hseedTau,
    he,hzeta,hzseed,hL,hg,hgrid,hL2,hc2,deltaRet,hdRet,hdRet1,hdRetHistory,hdRetCleanup,hsource⟩ :=
    NativePrescribedFinalConfiguration.exists_prescribed_final_configuration
      (NativeParentHorizontalQueryMenu.size d K) J hJ hk eta0 c he0 heK hc
      (hc8.trans (by norm_num : (1/8:ℝ)≤1/2))
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
  let Rel0 : Fin (NativeParentHorizontalQueryMenu.size d K) → (Fin n × Index) → (Fin n × Index) → Prop :=
    fun _ _ _ => True
  have Hfinal := hFinal Rel0 (by intro i x; trivial) (by intro i x y hxy; trivial)
  have HhistoryNew := prescribed_final_stage_history h original R E1 F P a level schedule L L2
    eta0 c tau seed htau c2 ell j Rel0 Hfinal
  have Hhistory := prescribed_history_stage_forget h original R E1 F P a level schedule L L2
    eta0 c tau seed htau c2 ell j Rel0 HhistoryNew
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
  refine ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hExtraSmall,le_min hRet hRangeSmall,hK,hvol,hnear,
    a,level,R,original,E1,schedule,hBackbone,hgl,hSchedule,hCore,hCost1,
    hPoint,hOld,hConditioned,hScales,hMiddle,hAllPairs,hE1Near,
    ell,j,hell,hrank23,hrange,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hstopK,hSelect,?_⟩
  intro selected depths hdepths _hcoarse Rel hrefl hsymm
  have hrf := NativeParentHorizontalQueryMenu.relations_refl h R a level
    (historyDepth J (schedule j).val selected) depths
    (slicePoint D a (historyDepth J (schedule j).val selected))
    (fun _p u => sliceClass (historyDepth J (schedule j).val selected) (depths u)) Rel hrefl
  have hrs := NativeParentHorizontalQueryMenu.relations_symm h R a level
    (historyDepth J (schedule j).val selected) depths
    (slicePoint D a (historyDepth J (schedule j).val selected))
    (fun _p u => sliceClass (historyDepth J (schedule j).val selected) (depths u)) Rel hsymm
  exact prescribed_stage_with_horizontal_menu h original R E1 F P a level schedule L L2
    eta0 c tau seed htau c2 ell j selected depths (fun u => (hdepths u).2) Rel
    (hFinal (callerRelations h R a level schedule j selected depths Rel) hrf hrs)

/-- Keep every menu/parent query and the identical final history while
forgetting only the additional prescribed-word trace. -/
theorem prescribed_horizontal_stage_forget {n d J g K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index)) (P : Index → Submodule ℝ E4)
    (a : ℝ) (level : ℕ) (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau seed : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (selected : Fin J) (depths : Fin K → ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : HasPrescribedHorizontalStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed htau c2 ell j selected depths Rel) :
    NativeActualParentMenuConfiguration.HasHorizontalFinalStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed htau c2 ell j selected depths Rel := by
  obtain ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,hFinal,hQueries,hParent,hCounts⟩ := H
  exact ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,
    prescribed_final_retained_forget h hFinal,hQueries,hParent,hCounts⟩

end NativePrescribedParentMenuConfiguration
