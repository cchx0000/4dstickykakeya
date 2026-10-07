import Theorems.Thm_StickyKakeya4_native_generic_final_history
import Theorems.Thm_StickyKakeya4_native_actual_parent_menu_configuration
import Theorems.Thm_StickyKakeya4_native_prescribed_final_configuration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 14000000
noncomputable section

namespace NativeGenericParentMenu
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
    (schedule : Fin (g+1) → Fin (level+1)) (firstDimension L L2 : ℕ)
    (eta0 c tau seed : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (selected : Fin J) (depths : Fin K → ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) : Prop :=
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
  let lambda := r^(rankLoss eta0 c ell)/(4*((g:ℝ)+1))
  let F1 := factor firstDimension (g+1) L
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
    (a : ℝ) (level : ℕ) (schedule : Fin (g+1) → Fin (level+1)) (firstDimension L L2 : ℕ)
    (eta0 c tau seed : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (selected : Fin J) (depths : Fin K → ℕ)
    (hdepths : ∀u,depths u ≤ phaseDepth (historyDepth J (schedule j).val selected))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : NativeGenericFinalHistory.HasPrescribedFinalStage (J:=J) h original R E1 F P a level schedule firstDimension L L2 eta0 c tau seed htau c2 ell j
      (callerRelations h R a level schedule j selected depths Rel)) :
    HasPrescribedHorizontalStage (J:=J) h original R E1 F P a level schedule firstDimension L L2
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


end NativeGenericParentMenu
