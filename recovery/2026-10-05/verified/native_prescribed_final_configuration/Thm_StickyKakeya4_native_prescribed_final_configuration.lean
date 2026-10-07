import Theorems.Thm_StickyKakeya4_native_actual_final_grain_configuration
import Theorems.Thm_StickyKakeya4_native_prescribed_history_configuration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 14000000
noncomputable section

namespace NativePrescribedFinalConfiguration
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

open NativeActualFinalGrainConfiguration NativePrescribedHistoryConfiguration NativePrescribedRetainedHistory
open NativeOriginalAngularTupleMenu

def HasPrescribedFinalRetainedHistory {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (stop : ℕ)
    (E : Finset (Fin n × Index)) (q : ℝ) (ell J Q2 : ℕ)
    (r etaRank lambda c1 c2 : ℝ) : Prop :=
  let w := pointWeight E
  ∃P⊆terminalFamily D a stop E q ell, ∃S⊆E.image Prod.snd,
    S=P.image Prod.fst ∧
    (∀x y,x∈P → y∈P → x.1=y.1 → x=y) ∧
    SelfUniform.mass (fun p => w p.1) P=SelfUniform.mass w S ∧
    r^(2*(ell:ℝ)*etaRank)*(SelfUniform.mass w (E.image Prod.snd):ℝ) ≤ (SelfUniform.mass w S:ℝ) ∧
    (∀j,j<J+1 → ∀x y,x∈P → y∈P →
      spatialLabel D (2^(depth J stop j)) x.1=spatialLabel D (2^(depth J stop j)) y.1 →
      projectWord stop (depth J stop j) x.2=projectWord stop (depth J stop j) y.2) ∧
    (∀p∈P,LocalWitness D a stop E q ell p) ∧
    (∀j,j<J → ∀v∈P.image (node D J stop (j+1)),
      ancestorNode (depth J stop (j+1)) (depth J stop j) v∈P.image (node D J stop j) ∧
      (candidate D J stop (j+1) P v ∩ candidate D J stop j P
        (ancestorNode (depth J stop (j+1)) (depth J stop j) v)).Nonempty) ∧
    ∃ (point : Fin J → Index → Index)
      (tuple : Fin J → Index → Fin ell → (Fin n × Index))
      (anchor : Fin J → Index → Fin ell → Fin n),
      (∀i,IsNodeDirectionSystem D a (historyDepth J stop i) E S q ell
        (point i) (tuple i) (anchor i)) ∧
      (∀i : Fin J,∀p∈P,angularTuple D a (historyDepth J stop i)
        (List.ofFn (tuple i (spatialLabel D (2^(historyDepth J stop i)) p.1)))=
          projectWord stop (historyDepth J stop i) p.2) ∧
      (∀i : Fin J,∀x y,x∈P → y∈P →
        projectWord stop (historyDepth J stop i) x.2=projectWord stop (historyDepth J stop i) y.2 →
        tuple i (spatialLabel D (2^(historyDepth J stop i)) x.1)=
          tuple i (spatialLabel D (2^(historyDepth J stop i)) y.1) ∧
        point i (spatialLabel D (2^(historyDepth J stop i)) x.1)=
          point i (spatialLabel D (2^(historyDepth J stop i)) y.1)) ∧
      HasGrainHistory D E (historyDepth J stop) ell (fun i => natStageDirectionIndex h (tuple i))
        S Q2 lambda c1 c2 ∧
      r^((2*(ell:ℝ)+1)*etaRank)*(E.card:ℝ) ≤
        (mass (history D E (historyDepth J stop) ell
          (fun i => natStageDirectionIndex h (tuple i)) S J) w:ℝ) ∧
      FinalCleanupData h a E (historyDepth J stop) q ell Q2 S r etaRank point tuple anchor


/-- Full original second-stage fields together with the actual final grain core. -/
def HasPrescribedFinalStage {n d J g : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index))
    (P : Index → Submodule ℝ E4) (a : ℝ) (level : ℕ)
    (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau seed : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) : Prop :=
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
  let lambda := r^(rankLoss eta0 c ell)/(4*((g:ℝ)+1))
  let F1 := factor (menuSize (pairMenuSize (1+(g+1)) (g+1)) (g+1)) (g+1) L
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
        HasPrescribedFinalRetainedHistory h a (schedule j).val E2 q (ell.val+1) J Q2
          r (rankLoss eta0 c ell) lambda (seed/8) c2


theorem prescribed_final_retained_of_history {n J ell stop Q : ℕ} {D : FiniteScaleSource n}
    {eta a q r etaRank lambda c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (E : Finset (Fin n × Index)) (hE : E.Nonempty)
    (hJ : 0 < J) (hm : ∀i : Fin J,6 ≤ historyDepth J stop i) (hell : ell ≤ 4)
    (HU : ∀i : Fin J,HasUniformFibers E Q
      (fun z => spatialLabel D (2^(phaseDepth (historyDepth J stop i))) z.2))
    (hq : 0 < q) (hq1 : q ≤ 1) (t : ℝ) (ht : 0 < t)
    (hsmall : D.thickness ≤ historyCutoff (J+1) t ht) (aRank : ℝ)
    (hetaRank : 0 ≤ etaRank) (hid : aRank*etaRank=t) (hr : 0 < r) (hrscale : r ≤ D.thickness^aRank)
    (H : HasPrescribedRetainedHistory h a stop E q ell J Q r etaRank lambda c1 c2) :
    HasPrescribedFinalRetainedHistory h a stop E q ell J Q r etaRank lambda c1 c2 := by
  obtain ⟨P,hP,S,hSE,hS,hinj,hmass,hret,hcompat,hwitness,htrace,
    point,tuple,anchor,Hsys,Hword,Hsame,Hhistory,hHistoryRet⟩ := H
  refine ⟨P,hP,S,hSE,hS,hinj,hmass,hret,hcompat,hwitness,htrace,
    point,tuple,anchor,Hsys,Hword,Hsame,Hhistory,hHistoryRet,?_⟩
  have hbase : r^(2*(ell:ℝ)*etaRank)*(E.card:ℝ) ≤ (mass S (pointWeight E):ℝ) := by
    have hh := hret
    change r^(2*(ell:ℝ)*etaRank)*(mass (E.image Prod.snd) (pointWeight E):ℝ) ≤
      (mass S (pointWeight E):ℝ) at hh
    rwa [NativeQueriedVertexWeights.reference_mass] at hh
  exact final_cleanup_of_history h E hE hJ (historyDepth J stop) hm ell hell S hSE Q HU hq hq1
    point tuple anchor Hsys Hhistory t ht hsmall aRank etaRank r hetaRank hid hr hrscale hbase

/-- Read back the original retained history from the exact final-core witness. -/
theorem prescribed_final_retained_history {n J ell stop Q : ℕ} {D : FiniteScaleSource n}
    {eta a q r etaRank lambda c1 c2 : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    {E : Finset (Fin n × Index)}
    (H : HasPrescribedFinalRetainedHistory h a stop E q ell J Q r etaRank lambda c1 c2) :
    HasPrescribedRetainedHistory h a stop E q ell J Q r etaRank lambda c1 c2 := by
  obtain ⟨P,hP,S,hSE,hS,hinj,hmass,hret,hcompat,hwitness,htrace,
    point,tuple,anchor,Hsys,Hword,Hsame,Hhistory,hHistoryRet,_hFinal⟩ := H
  exact ⟨P,hP,S,hSE,hS,hinj,hmass,hret,hcompat,hwitness,htrace,
    point,tuple,anchor,Hsys,Hword,Hsame,Hhistory,hHistoryRet⟩

theorem prescribed_final_stage_of_history {n d J g : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index)) (P : Index → Submodule ℝ E4)
    (a : ℝ) (level : ℕ) (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau seed : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (he0 : 0 < eta0) (hc : 0 < c) (hJ : 0 < J)
    (hrcut : radius (rankWindow tau) (rankWindow_pos htau).le g level j ≤ D.thickness^(cutoff c ell))
    (hrhi : radius (rankWindow tau) (rankWindow_pos htau).le g level j ≤ 1/4)
    (hsmall : D.thickness ≤ historyCutoff (J+1) (commonBudget eta0 c) (commonBudget_pos he0 hc))
    (H : HasPrescribedHistoryStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed htau c2 ell j Rel) :
    HasPrescribedFinalStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed htau c2 ell j Rel := by
  obtain ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,hHistory⟩ := H
  refine ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,?_⟩
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
  let q := radius (rankWindow tau) (rankWindow_pos htau).le g level test
  let Q := NativeSourceSizeBounds.radix F.card L2
  have hr : 0 < r := radius_pos _ _ _ _ _
  have hq : 0 < q := radius_pos _ _ _ _ _
  have hq1 : q ≤ 1 := hqr.trans (Real.rpow_le_one hr.le
    (hrhi.trans (by norm_num : (1/4:ℝ)≤1)) (by positivity))
  have Hquery (i : Fin J) :
      6 ≤ historyDepth J (schedule j).val i ∧
      HasUniformFibers E2 Q (fun z => spatialLabel D
        (2^(phaseDepth (historyDepth J (schedule j).val i))) z.2) := by
    obtain ⟨h6,_hmb,_hbl,_hp,_hle,_hid,_hinv,_hd,_hrat,_hf,_hc,hv,_hvc⟩ := hGrains i.succ
    exact ⟨h6,hv⟩
  exact prescribed_final_retained_of_history h E2 hE2ne hJ (fun i => (Hquery i).1)
    (by omega) (fun i => (Hquery i).2) hq hq1 (commonBudget eta0 c) (commonBudget_pos he0 hc)
    hsmall (cutoff c ell) (rankLoss_pos he0 hc ell).le (cutoff_mul_rankLoss eta0 c ell)
    hr hrcut hHistory

/-- The final source stage retains the same history required by the rank-four
consumer; reading it back performs no new source or tuple selection. -/
theorem prescribed_final_stage_history {n d J g : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index)) (P : Index → Submodule ℝ E4)
    (a : ℝ) (level : ℕ) (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau seed : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : HasPrescribedFinalStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed htau c2 ell j Rel) :
    HasPrescribedHistoryStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed htau c2 ell j Rel := by
  obtain ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,hFinal⟩ := H
  exact ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,
    prescribed_final_retained_history h hFinal⟩

/-- An actual original near-extremal source, its same second-stage incidence core,
its complete retained history, and one final simultaneously dense grain core.
The complete fixed loss 2^(J+1) is absorbed once before choosing the source. -/
theorem exists_prescribed_final_configuration (d J : ℕ) (hJ : 0 < J) (hk : 0 < extremalExponent)
    (eta0 c : ℝ) (he0 : 0 < eta0) (heK : eta0 ≤ extremalExponent / 2)
    (hc : 0 < c) (hcsmall : c ≤ 1 / 2) :
    ∃ (tau : ℝ) (htau : 0 < tau) (seed e zeta : ℝ) (L g L2 : ℕ) (c2 : ℝ),
      tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1)) ∧ tau ≤ commonBudget eta0 c / 1024 ∧ tau ≤ 1 / 2 ∧
      0 < seed ∧ seed ≤ tau / 16384 ∧ 0 < e ∧ 0 < zeta ∧
      zeta ≤ seed / 256 ∧ 0 < L ∧ 0 < g ∧
      1 / (g : ℝ) < rankWindow tau / 4 ∧
      0 < L2 ∧ c2=commonBudget eta0 c/4 ∧
      ∃ deltaRet : ℝ, 0 < deltaRet ∧ deltaRet ≤ 1 ∧
      deltaRet ≤ historyCutoff J (commonBudget eta0 c) (commonBudget_pos he0 hc) ∧
      deltaRet ≤ historyCutoff (J+1) (commonBudget eta0 c) (commonBudget_pos he0 hc) ∧
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
          ∃ (ell : Fin 4) (j : Fin (g + 1)), 1 ≤ ell.val ∧
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
                  HasPrescribedFinalStage (J:=J) h original R E1 F P a level schedule L L2
                    eta0 c tau seed htau c2 ell j Rel := by
  let t := commonBudget eta0 c
  have ht : 0 < t := commonBudget_pos he0 hc
  let deltaCleanup := historyCutoff (J+1) t ht
  have hdCleanup : 0 < deltaCleanup := (historyCutoff_spec (J+1) t ht).1
  obtain ⟨tau,htau,seed,e,zeta,L,g,L2,c2,htauB,htauT,htauHalf,hseed,hseedTau,
    he,hzeta,hzseed,hL,hg,hgrid,hL2,hc2,deltaRet,hdRet,hdRet1,hdRetHistory,hsource⟩ :=
    NativePrescribedHistoryConfiguration.exists_prescribed_history_configuration
      d J hJ hk eta0 c he0 heK hc hcsmall
  refine ⟨tau,htau,seed,e,zeta,L,g,L2,c2,htauB,htauT,htauHalf,hseed,hseedTau,
    he,hzeta,hzseed,hL,hg,hgrid,hL2,hc2,min deltaRet deltaCleanup,
    lt_min hdRet hdCleanup,(min_le_left _ _).trans hdRet1,
    (min_le_left _ _).trans hdRetHistory,min_le_right _ _,?_⟩
  intro etaBound deltaBound extraCutoff heB hdB hExtra
  obtain ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hExtraOld,hRet,hK,hvol,hnear,
    a,level,R,original,E1,schedule,hBackbone,hgl,hSchedule,hCore,hCost1,
    hPoint,hOld,hConditioned,hScales,hMiddle,hAllPairs,hE1Near,
    ell,j,hell,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hstopK,hSelect,hHistory⟩ :=
    hsource etaBound deltaBound (min extraCutoff deltaCleanup) heB hdB (lt_min hExtra hdCleanup)
  have hCleanupSmall : D.thickness ≤ deltaCleanup := hExtraOld.le.trans (min_le_right _ _)
  have hExtraSmall : D.thickness < extraCutoff := hExtraOld.trans_le (min_le_left _ _)
  refine ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hExtraSmall,le_min hRet hCleanupSmall,hK,hvol,hnear,
    a,level,R,original,E1,schedule,hBackbone,hgl,hSchedule,hCore,hCost1,
    hPoint,hOld,hConditioned,hScales,hMiddle,hAllPairs,hE1Near,
    ell,j,hell,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hstopK,hSelect,?_⟩
  intro Rel hrefl hsym
  exact prescribed_final_stage_of_history h original R E1 F P a level schedule L L2
    eta0 c tau seed htau c2 ell j Rel he0 hc hJ hrcut hrhi
    hCleanupSmall (hHistory Rel hrefl hsym)

/-- Exact forgetful projection: retain the original final K and every
history layer, dropping only the prescribed-word fields. -/
theorem prescribed_final_retained_forget {n J ell stop Q : ℕ} {D : FiniteScaleSource n}
    {eta a q r etaRank lambda c1 c2 : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    {E : Finset (Fin n × Index)}
    (H : HasPrescribedFinalRetainedHistory h a stop E q ell J Q r etaRank lambda c1 c2) :
    NativeActualFinalGrainConfiguration.HasFinalRetainedHistory h a stop E q ell J Q r etaRank lambda c1 c2 := by
  obtain ⟨P,hP,S,hSE,hS,hinj,hmass,hret,hcompat,hwitness,htrace,
    point,tuple,anchor,Hsys,_Hword,_Hsame,Hhistory,hHistoryRet,Hfinal⟩ := H
  exact ⟨P,hP,S,hSE,hS,hinj,hmass,hret,hcompat,hwitness,htrace,
    point,tuple,anchor,Hsys,Hhistory,hHistoryRet,Hfinal⟩

theorem prescribed_final_stage_forget {n d J g : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index)) (P : Index → Submodule ℝ E4)
    (a : ℝ) (level : ℕ) (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau seed : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : HasPrescribedFinalStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed htau c2 ell j Rel) :
    NativeActualFinalGrainConfiguration.HasFinalGrainSquaredStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed htau c2 ell j Rel := by
  obtain ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,hFinal⟩ := H
  exact ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,
    prescribed_final_retained_forget h hFinal⟩

end NativePrescribedFinalConfiguration
