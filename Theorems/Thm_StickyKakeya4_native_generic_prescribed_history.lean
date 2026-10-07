import Theorems.Thm_StickyKakeya4_native_generic_compatible_stage
import Theorems.Thm_StickyKakeya4_native_actual_history_configuration
import Theorems.Thm_StickyKakeya4_native_prescribed_retained_history

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 14000000
noncomputable section

namespace NativeGenericPrescribedHistory
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
open NativePrescribedRetainedHistory

/-- The complete same-E2 stage, with all old fields plus the actual retained grain history. -/
def HasPrescribedHistoryStage {n d J g : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index))
    (P : Index → Submodule ℝ E4) (a : ℝ) (level : ℕ)
    (schedule : Fin (g+1) → Fin (level+1)) (firstDimension L L2 : ℕ)
    (eta0 c tau seed : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) : Prop :=
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
  let lambda := r^(rankLoss eta0 c ell)/(4*((g:ℝ)+1))
  let F1 := factor firstDimension (g+1) L
  let G := retentionCost ((d+((J+1)+(J+1))+((J+1)+(J+1))+((J+1)+(J+1))+1)+(g+1)*(g+1)) 1 L2
  let F2 := factor ((d+((J+1)+(J+1))+((J+1)+(J+1))+((J+1)+(J+1))+1)+(g+1)*(g+1)) 1 L2
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
        NativePrescribedRetainedHistory.HasPrescribedRetainedHistory h a (schedule j).val E2 q (ell.val+1) J Q2
          r (rankLoss eta0 c ell) lambda (seed/8) c2


/-- Deterministic upgrade of the chosen second-stage witness. Its E2 is
unpacked once and is used by the actual retained-history constructor. -/
theorem prescribed_history_stage_of_compatible {n d J g : ℕ} {D : FiniteScaleSource n} {eta zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index)) (P : Index → Submodule ℝ E4)
    (a : ℝ) (level : ℕ) (schedule : Fin (g+1) → Fin (level+1)) (firstDimension L L2 : ℕ)
    (eta0 c tau seed : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (he0 : 0 < eta0) (hc : 0 < c) (heta : 0 ≤ eta)
    (hBackbone : HasOriginalBackbone D original R a level zeta)
    (hrcut : radius (rankWindow tau) (rankWindow_pos htau).le g level j ≤ D.thickness^(cutoff c ell))
    (hsmall : D.thickness ≤ historyCutoff J (commonBudget eta0 c) (commonBudget_pos he0 hc))
    (hCost1 : (125*175616*16384:ℝ)*
      (factor firstDimension (g+1) L:ℝ)*
      (coreRadix original R L:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (H : NativeGenericCompatibleStage.HasCompatibleSquaredStage (J:=J) h original R E1 F P a level schedule firstDimension L L2
      eta0 c tau htau c2 ell j Rel) :
    HasPrescribedHistoryStage (J:=J) h original R E1 F P a level schedule firstDimension L L2
      eta0 c tau seed htau c2 ell j Rel := by
  obtain ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily⟩ := H
  refine ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,?_⟩
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
  let q := radius (rankWindow tau) (rankWindow_pos htau).le g level test
  let lambda := r^(rankLoss eta0 c ell)/(4*((g:ℝ)+1))
  let F1 := factor firstDimension (g+1) L
  let d2 := (d+pairedCount J+pairedCount J+pairedCount J+1)+(g+1)*(g+1)
  let G := retentionCost d2 1 L2
  let F2 := factor d2 1 L2
  let Q1 := coreRadix original R L
  let Q2 := NativeSourceSizeBounds.radix F.card L2
  have hr : 0 < r := radius_pos _ _ _ _ _
  have hq : 0 < q := radius_pos _ _ _ _ _
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  have hE : E2⊆incidences original := fun z hz => (mem_filter.mp (hE2old hz)).1
  have hER : ∀z∈E2,z.1∈R := fun z hz => (mem_filter.mp (hE2old hz)).2
  have hF1 : 0 < F1 := original_factor_pos _ _ _
  have hG : 0 < G := by dsimp [G,retentionCost]; positivity
  have hQ1 : 1 ≤ Q1 := (show 1 ≤ 4 by norm_num).trans (radix_four_le _ _)
  have hQ2 : 0 < Q2 := (show 0 < 4 by norm_num).trans_le (radix_four_le _ _)
  have hGF : G ≤ F2 := NativeSecondRefinementCost.retained_cost_le_factor d2 1 L2 (by omega)
  have Hquery (i : Fin J) :
      let m := historyDepth J (schedule j).val i
      let b := phaseDepth m
      let rep := NativeCoarseDirectionThinning.representative h R a (2^b)
      6 ≤ m ∧ b ≤ level ∧ D.thickness ≤ (64/((2^m:ℕ):ℝ))^2 ∧
        HasUniformFibers E2 Q2 (NativeCoarseShadingUniformity.fixedPair D a level b b rep) ∧
        HasUniformFibers E2 Q2 (NativeCoarseShadingUniformity.fixedPair D a level b m rep) ∧
        HasUniformFibers E2 Q2 (fun z => NativeSpatialAngularGeometry.spatialLabel D (2^b) z.2) := by
    obtain ⟨h6,_hmb,hbl,_hp,_hle,_hid,_hinv,hd,_hrat,hf,hc,hv,_hvc⟩ := hGrains i.succ
    exact ⟨h6,hbl,hd,hf,hc,hv⟩
  exact construct_prescribed_retained_history J (commonBudget eta0 c) (commonBudget_pos he0 hc)
    h hsmall original hBackbone.1 hBackbone.2.2.1 R E2 hE hE2ne hER
    F1 F2 G Q1 Q2 hF1 hG hQ2 hQ1 hGF heta hBackbone.2.1 hlambda hRich hCost1 hCost2
    (schedule j).val (fun i => (Hquery i).1) (fun i => (Hquery i).2.1)
    (fun i => (Hquery i).2.2.1) (fun i => (Hquery i).2.2.2.1)
    (fun i => (Hquery i).2.2.2.2.1) (fun i => (Hquery i).2.2.2.2.2)
    q hq (ell.val+1) (by omega) (cutoff c ell) (rankLoss eta0 c ell) r
    (rankLoss_pos he0 hc ell).le (cutoff_mul_rankLoss eta0 c ell) hr hrcut
    (hFamily (pointWeight E2))


end NativeGenericPrescribedHistory
