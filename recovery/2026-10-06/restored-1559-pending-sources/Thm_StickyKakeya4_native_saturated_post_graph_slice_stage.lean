import Theorems.Thm_StickyKakeya4_native_saturated_actual_post_graph_slice
import Theorems.Thm_StickyKakeya4_native_saturated_parent_graph_configuration
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 14000000
noncomputable section

namespace NativeSaturatedPostGraphSliceStage
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

open NativeSaturatedPostGraphSliceData NativeSaturatedActualPostGraphSlice NativeSaturatedParentGraphConfiguration

def SaturatedPostGraphCleanupData {n J : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (E : Finset (Fin n × Index))
    (m : Fin J → ℕ) (q : ℝ) (ell Q : ℕ) (S0 : Finset Index) (r etaRank : ℝ)
    (point : Fin J → Index → Index)
    (tuple : Fin J → Index → Fin ell → (Fin n × Index))
    (anchor : Fin J → Index → Fin ell → Fin n)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (E1 : Finset (Fin n × Index))
    (level F1 G stop : ℕ) (lambda zeta tau seed c2 : ℝ) (selected : Fin J) (Jhorizontal d3 L3 : ℕ) (Khalf : ℕ) (epsilon : ℝ) : Prop :=
  let S := history D E m ell (fun j => natStageDirectionIndex h (tuple j)) S0
  let F := S J
  let plane := fun j node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple j node))
  let f := fun j => taggedLabel D (m j) (plane j) ell
  let L := fun j => predecessorProduct D (m j) E Q
    (scaleThreshold D E (m j) (S j.val) ell (natStageDirectionIndex h (tuple j))) ell
  let M := fun j => vertexCap E (spatialLabel D (2^(phaseDepth (m j)))) Q
  ∃K⊆F,K.Nonempty ∧ mass F (pointWeight E) ≤ 2*mass K (pointWeight E) ∧
    mass S0 (pointWeight E) ≤ 2^(J+1)*mass K (pointWeight E) ∧
    r^((2*(ell:ℝ)+1)*etaRank)*(E.card:ℝ) ≤ (mass K (pointWeight E):ℝ) ∧
    (∀j : Fin J,0 < L j ∧ (M j:ℝ)*L j*(F.image (f j)).card ≤
      625*transverseCost q ell*(Q:ℝ)^2*E.card) ∧
    (∀j : Fin J,∀x∈K,
      NativeAutomaticWeightedGrainCore.threshold (mass F (pointWeight E)) J (F.image (f j)).card ≤
        mass (classFiber K (f j) (f j x)) (pointWeight E) ∧
      ((mass F (pointWeight E):ℝ)/(E.card:ℝ))*(M j:ℝ)*(L j:ℝ)/
        (1250*(J:ℝ)*transverseCost q ell*(Q:ℝ)^2) <
          (mass (classFiber K (f j) (f j x)) (pointWeight E):ℝ) ∧
      ∀y∈classFiber K (f j) (f j x),
        spatialLabel D (2^(m j)) y=spatialLabel D (2^(m j)) x ∧
        Metric.infDist (rawVertex D (phaseDepth (m j)) y-rawVertex D (phaseDepth (m j)) x)
          (plane j (spatialLabel D (2^(m j)) x):Set E4) ≤ 2*grainWidth (m j) ell) ∧
    (∀j,IsNodeDirectionSystem D a (m j) E K q ell (point j) (tuple j) (anchor j)) ∧
    (∀j : Fin J,∀k∈K,(spatialLabel D (2^(m j)) k,k)∈
      scaleLayers D E (m j) (S j.val) ell (natStageDirectionIndex h (tuple j)) ell) ∧
    HasSaturatedPostGraphParentProfiles h original R E1 E a level (m selected) (plane selected) K q ell Q
      F1 G (L selected) lambda zeta tau seed c2 Jhorizontal d3 L3 stop Khalf (tuple selected) r epsilon


def HasSaturatedPostGraphRetainedHistory {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (stop : ℕ)
    (E : Finset (Fin n × Index)) (q : ℝ) (ell J Q2 : ℕ)
    (r etaRank lambda c1 c2 : ℝ)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (E1 : Finset (Fin n × Index))
    (level F1 G : ℕ) (zeta tau seed : ℝ) (selected : Fin J) (Jhorizontal d3 L3 : ℕ) (Khalf : ℕ) (epsilon : ℝ) : Prop :=
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
      SaturatedPostGraphCleanupData h a E (historyDepth J stop) q ell Q2 S r etaRank point tuple anchor
        original R E1 level F1 G stop lambda zeta tau seed c2 selected Jhorizontal d3 L3 Khalf epsilon

def HasSaturatedPostGraphStage {n d J g : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index))
    (P : Index → Submodule ℝ E4) (a : ℝ) (level : ℕ)
    (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau seed zeta : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (selected : Fin J) (Jhorizontal d3 L3 : ℕ) (Khalf : ℕ) (epsilon : ℝ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) : Prop :=
  let K := Jhorizontal+1
  let depths := NativeFixedHorizontalMenu.depths Jhorizontal (historyDepth J (schedule j).val selected)
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
        HasSaturatedPostGraphRetainedHistory h a (schedule j).val E2 q (ell.val+1) J Q2
          r (rankLoss eta0 c ell) lambda (seed/8) c2 original R E1 level F1 G zeta tau seed selected Jhorizontal d3 L3 Khalf epsilon
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


theorem stage_with_saturated_post_graph_slice {n d J g : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index)) (P : Index → Submodule ℝ E4)
    (a : ℝ) (level : ℕ) (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau seed zeta : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (selected : Fin J) (Jhorizontal d3 L3 : ℕ) (Khalf : ℕ) (epsilon : ℝ)
    (hHorizontal : 0 < Jhorizontal) (hL3 : 0 < L3)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (heta : 0 ≤ eta) (_hJ : 0 < J) (hg : 0 < g) (hgl : g ≤ level)
    (hseed : seed ≤ tau/16384) (hgrid : 1/(g:ℝ) < rankWindow tau/4)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (hschedule : schedule=fullSchedule tau htau g level)
    (Hcore : IsCore D original R a eta zeta
      (menuSize (pairMenuSize (1+(g+1)) (g+1)) (g+1)) (g+1) L
      (relationMenu h R a schedule (pairRelationMenu h R a schedule (masterRelations D a schedule)))
      (fun j => 2^(schedule j).val) E1)
    (hcost : (125*175616*16384:ℝ)*
      (factor (menuSize (pairMenuSize (1+(g+1)) (g+1)) (g+1)) (g+1) L:ℝ)*
      (coreRadix original R L:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (hconditioned : ∀i j,HasUniformFibers E1 (coreRadix original R L)
      (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
      HasUniformFibers E1 (coreRadix original R L)
      (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val))
    (hreference : ∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E1 a level m f tau)
    (hFE1 : F⊆E1)
    (hnearP : ∀z∈F,Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤
      radius (rankWindow tau) (rankWindow_pos htau).le g level j)
    (hidentity : 48*((2^(schedule j).val:ℕ):ℝ)*radius (rankWindow tau) (rankWindow_pos htau).le g level j=1)
    (hsmall : D.thickness ≤ 1/8)
    (H : HasSaturatedCurveParentStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed zeta htau c2 ell j selected
      (NativeFixedHorizontalMenu.depths Jhorizontal (historyDepth J (schedule j).val selected)) Khalf epsilon Rel) :
    HasSaturatedPostGraphStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed zeta htau c2 ell j selected Jhorizontal d3 L3 Khalf epsilon Rel := by
  obtain ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,hFinal,hQueries,hParent,hCounts⟩ := H
  refine ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,?_,hQueries,hParent,hCounts⟩
  obtain ⟨C,hC,S0,hS0,hS,hinj,hmass,hretain,hcompat,hwitness,htrace,
    point,tuple,anchor,Hsys,Hword,Hsame,Hhistory,hHistRet,Hcleanup⟩ := hFinal
  refine ⟨C,hC,S0,hS0,hS,hinj,hmass,hretain,hcompat,hwitness,htrace,
    point,tuple,anchor,Hsys,Hword,Hsame,Hhistory,hHistRet,?_⟩
  obtain ⟨Kpoints,hKF,hKn,hhalf,htotal,hfinal,hgrainCounts,hdense,HsysK,hTrace,Hcurve⟩ := Hcleanup
  refine ⟨Kpoints,hKF,hKn,hhalf,htotal,hfinal,hgrainCounts,hdense,HsysK,hTrace,?_⟩
  let m := historyDepth J (schedule j).val selected
  let stop := (schedule j).val
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
  let q := radius (rankWindow tau) (rankWindow_pos htau).le g level test
  let Q2 := NativeSourceSizeBounds.radix F.card L2
  let d2 := (NativeParentHorizontalQueryMenu.size d (Jhorizontal+1)+pairedCount J+pairedCount J+pairedCount J+1)+(g+1)*(g+1)
  let G := retentionCost d2 1 L2
  let lambda := r^(rankLoss eta0 c ell)/(4*((g:ℝ)+1))
  have hr : 0 < r := radius_pos _ _ _ _ _
  have hq : 0 < q := radius_pos _ _ _ _ _
  have hq1 : q ≤ 1 := (radius_le_one_div_48 _ _ _ _ _).trans (by norm_num)
  have hG : 0 < G := by dsimp [G,retentionCost]; positivity
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  have hm6 : 6 ≤ m := (hGrains selected.succ).1
  have hf : phaseDepth m ≤ level := (hGrains selected.succ).2.2.1
  have hms : m ≤ stop := historyDepth_le_stop J stop selected
  have hrD : r ≤ 64/((2^m:ℕ):ℝ) := by
    have hp : ((2^m:ℕ):ℝ) ≤ ((2^stop:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hms
    have hh := mul_le_mul_of_nonneg_left hp hr.le
    apply (le_div_iff₀ (by positivity : (0:ℝ)<((2^m:ℕ):ℝ))).mpr
    change 48*((2^stop:ℕ):ℝ)*r=1 at hidentity
    nlinarith only [hh,hidentity]
  have HP : HasUniformFibers E2 Q2 (physicalPair h R a level (phaseDepth m)) :=
    (hGrains selected.succ).2.2.2.2.2.2.2.2.2.1
  have HV : HasUniformFibers E2 Q2 (fun z => spatialLabel D (2^(phaseDepth m)) z.2) :=
    (hGrains selected.succ).2.2.2.2.2.2.2.2.2.2.2.1
  have hKS0 : Kpoints⊆S0 := hKF.trans (Hhistory.2.2.1 J le_rfl).2.1
  exact attach_saturated_post_graph_slice h original R E1 E2 (hE2F.trans hFE1) hE2ne L schedule
    (relationMenu h R a schedule (pairRelationMenu h R a schedule (masterRelations D a schedule)))
    htau heta hseed hg hgl hgrid Hbackbone hschedule Hcore hcost hconditioned hreference
    G hG lambda hlambda hret m (ell.val+1) Q2 hm6 hf hsmall HP HV
    hHorizontal L3 hL3 stop Khalf S0 (point selected) (tuple selected) (anchor selected) (Hsys selected)
    P (fun k hk => hPlane k (hS0 hk)) (fun z hz => hnearP z (hE2F hz)) hq hq1 hr hrD
    Kpoints hKS0 _ hParent Hcurve

end NativeSaturatedPostGraphSliceStage
