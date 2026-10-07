import Theorems.Thm_StickyKakeya4_native_prescribed_population_parent_configuration
import Theorems.Thm_StickyKakeya4_native_prescribed_parent_graph_data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 14000000
noncomputable section

namespace NativePrescribedParentGraphConfiguration
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

open NativeActualParentMenuConfiguration NativePopulationParentProfiles
open NativePrescribedParentMenuConfiguration NativeCompleteParentProfiles NativeOriginalAngularTupleMenu

open NativePrescribedPopulationParentConfiguration NativePrescribedParentGraphData
open NativeHeightMetricMenu NativeMiddleGrainParentBudget NativeHeightMetricPower

def CurveParentFinalCleanupData {n J Kmenu : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (E : Finset (Fin n × Index))
    (m : Fin J → ℕ) (q : ℝ) (ell Q : ℕ) (S0 : Finset Index) (r etaRank : ℝ)
    (point : Fin J → Index → Index)
    (tuple : Fin J → Index → Fin ell → (Fin n × Index))
    (anchor : Fin J → Index → Fin ell → Fin n)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (E1 : Finset (Fin n × Index))
    (level F1 G stop : ℕ) (lambda zeta tau seed c2 : ℝ) (selected : Fin J) (depths : Fin Kmenu → ℕ) (Khalf : ℕ) (epsilon : ℝ) : Prop :=
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
    HasCurveParentProfiles h original R E1 E a level (m selected) (plane selected) K q ell Q
      F1 G (L selected) lambda zeta tau seed c2 depths stop Khalf (tuple selected) r epsilon


def HasCurveParentRetainedHistory {n Kmenu : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (stop : ℕ)
    (E : Finset (Fin n × Index)) (q : ℝ) (ell J Q2 : ℕ)
    (r etaRank lambda c1 c2 : ℝ)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (E1 : Finset (Fin n × Index))
    (level F1 G : ℕ) (zeta tau seed : ℝ) (selected : Fin J) (depths : Fin Kmenu → ℕ) (Khalf : ℕ) (epsilon : ℝ) : Prop :=
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
      CurveParentFinalCleanupData h a E (historyDepth J stop) q ell Q2 S r etaRank point tuple anchor
        original R E1 level F1 G stop lambda zeta tau seed c2 selected depths Khalf epsilon

def HasCurveParentStage {n d J g K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index))
    (P : Index → Submodule ℝ E4) (a : ℝ) (level : ℕ)
    (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau seed zeta : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (selected : Fin J) (depths : Fin K → ℕ) (Khalf : ℕ) (epsilon : ℝ)
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
        HasCurveParentRetainedHistory h a (schedule j).val E2 q (ell.val+1) J Q2
          r (rankLoss eta0 c ell) lambda (seed/8) c2 original R E1 level F1 G zeta tau seed selected depths Khalf epsilon
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

/-- The middle entry among the stored positive grain levels. -/
def middleSelected (Khalf : ℕ) (hHalf : 0 < Khalf) : Fin (2*Khalf) := ⟨Khalf-1,by omega⟩

lemma middle_selected_depth (Khalf : ℕ) (hHalf : 0 < Khalf) (stop : ℕ) (hs : 6 ≤ stop) :
    historyDepth (2*Khalf) stop (middleSelected Khalf hHalf)=middleDepth stop := by
  have he : (middleSelected Khalf hHalf).succ=middleIndex Khalf := by
    apply Fin.ext
    simp only [middleSelected,middleIndex,Fin.val_succ]
    omega
  change grainDepth (2*Khalf) stop (middleSelected Khalf hHalf).succ=middleDepth stop
  rw [he]
  exact grainDepth_middle Khalf stop hHalf hs

lemma half_depth_eq_depth (Khalf stop : ℕ) (i : Fin (Khalf+1)) :
    halfDepth Khalf stop i=NativeCompatibleAngularCandidates.depth (2*Khalf) stop i.val := by
  have hi : i.val ≤ 2*Khalf := by omega
  simp only [halfDepth,NativeCompatibleAngularCandidates.depth,min_eq_left hi]


/-- Construct the graph core on the stored parent using its prescribed-word
history. The normalized metric coefficient is derived from the source cutoff. -/
theorem stage_with_parent_graph {n d J g K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index)) (P : Index → Submodule ℝ E4)
    (a : ℝ) (level : ℕ) (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau seed zeta : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (selected : Fin J) (depths : Fin K → ℕ) (Khalf : ℕ) (epsilon : ℝ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hepsilon : 0 < epsilon) (he0 : 0 ≤ eta0) (heps : eta0 ≤ epsilon)
    (hc : 0 < c) (hc1 : c ≤ 1) (hceps : c ≤ epsilon/24)
    (hHalf : 0 < Khalf) (hEven : J=2*Khalf) (hgrain : 1/((2*Khalf:ℕ):ℝ) ≤ epsilon/2)
    (hTau : tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1)))
    (hgrid : 1/(g:ℝ) < rankWindow tau/4)
    (hrcut : radius (rankWindow tau) (rankWindow_pos htau).le g level j ≤ D.thickness^(cutoff c ell))
    (hidentity : 48*((2^(schedule j).val:ℕ):ℝ)*radius (rankWindow tau) (rankWindow_pos htau).le g level j=1)
    (hell3 : ell.val+1 ≤ 3)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (hmid : historyDepth J (schedule j).val selected=middleDepth (schedule j).val)
    (hsmall : D.thickness^(cutoff c ell*epsilon) ≤ 1/NativeHeightMetricPower.normalizationConstant)
    (H : HasPrescribedPopulationParentStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed zeta htau c2 ell j selected depths Rel) :
    HasCurveParentStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed zeta htau c2 ell j selected depths Khalf epsilon Rel := by
  subst J
  obtain ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,hFinal,hQueries,hParent,hCounts⟩ := H
  refine ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,?_,hQueries,hParent,hCounts⟩
  obtain ⟨C,hC,S0,hS0,hS,hinj,hmass,hretain,hcompat,hwitness,htrace,
    point,tuple,anchor,Hsys,Hword,Hsame,Hhistory,hHistRet,Hcleanup⟩ := hFinal
  refine ⟨C,hC,S0,hS0,hS,hinj,hmass,hretain,hcompat,hwitness,htrace,
    point,tuple,anchor,Hsys,Hword,Hsame,Hhistory,hHistRet,?_⟩
  obtain ⟨Kpoints,hKF,hKn,hhalf,htotal,hfinal,hgrainCounts,hdense,HsysK,hTrace,Hcomplete⟩ := Hcleanup
  refine ⟨Kpoints,hKF,hKn,hhalf,htotal,hfinal,hgrainCounts,hdense,HsysK,hTrace,?_⟩
  let stop := (schedule j).val
  let m := historyDepth (2*Khalf) stop selected
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
  let q := radius (rankWindow tau) (rankWindow_pos htau).le g level test
  have hr : 0 < r := radius_pos _ _ _ _ _
  have hr1 : r ≤ 1 := (radius_le_one_div_48 _ _ _ _ _).trans (by norm_num)
  have hq : 0 < q := radius_pos _ _ _ _ _
  have hq1 : q ≤ 1 := (radius_le_one_div_48 _ _ _ _ _).trans (by norm_num)
  have hm6 : 6 ≤ m := (hGrains selected.succ).1
  have hms : m ≤ stop := historyDepth_le_stop (2*Khalf) stop selected
  have hs : 6 ≤ stop := hm6.trans hms
  have hmL : m ≤ level := (hGrains selected.succ).2.1.trans (hGrains selected.succ).2.2.1
  have Hnode : IsNodeDirectionSystem D a m E2 (C.image Prod.fst) q (ell.val+1)
      (point selected) (tuple selected) (anchor selected) := by
    simpa only [hS] using Hsys selected
  have HC : ∀u : Fin (Khalf+1),∀x y,x∈C → y∈C →
      spatialLabel D (2^(halfDepth Khalf stop u)) x.1=spatialLabel D (2^(halfDepth Khalf stop u)) y.1 →
      projectWord stop (halfDepth Khalf stop u) x.2=projectWord stop (halfDepth Khalf stop u) y.2 := by
    intro u
    rw [half_depth_eq_depth]
    exact hcompat u.val (by omega)
  have hKC : Kpoints⊆C.image Prod.fst := by
    rw [←hS]
    exact hKF.trans (Hhistory.2.2.1 (2*Khalf) le_rfl).2.1
  have hmetric : 512*metricConstant ((stop-6)/(2*Khalf)+1)
      (NativeSeparatedSpanControl.coefficientCost 2 q (ell.val+1)) ≤ r^(-2*epsilon) :=
    actual_metric_constant_paid h.1.2.1 hr hr1 hepsilon he0 heps hc hc1 hceps ell hrcut htau.le
      g Khalf stop (ell.val+1) hHalf hell3 hgrain hTau hgrid hq hq1 hqlo hidentity hsmall
  exact attach_prescribed_parent_graph h original Hbackbone.1 Hbackbone.2.2.1 R E1 E2 hE2old
    level m stop Khalf Hbackbone.2.1 hmL hs hHalf hmid C hC
    (point selected) (tuple selected) (anchor selected) Hnode (by omega) (by omega) hq
    (Hword selected) HC Kpoints hKC _ _ _ _ _ zeta tau seed c2 r epsilon depths hmetric Hcomplete

/-- Choose the grain cardinal before tau/source, the middle scale before E2,
and the metric cutoff before D. The graph is built on the stored parent and
prescribed tuple history; no curve or metric certificate is an input. -/
theorem exists_prescribed_parent_graph_configuration (d K Kmin : ℕ) (_hK : 0 < K)
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
                ∀ Rel : Fin (NativeParentHorizontalQueryMenu.size d K) → (Fin n × Index) → (Fin n × Index) → Prop,
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
                  HasCurveParentStage (J:=J) h original R E1 F P a level schedule L L2
                    eta0 c tau seed zeta htau c2 ell j selected depths Khalf epsilon Rel := by
  obtain ⟨Khalf,hHalf,hKmin,hgrain⟩ := NativeHeightMetricPower.exists_grain_count epsilon hepsilon Kmin
  refine ⟨Khalf,hHalf,hKmin,hgrain,?_⟩
  let J := 2*Khalf
  have hJ : 0 < J := by dsimp [J]; positivity
  obtain ⟨eta0,he0,heK,heeps,he1000,c,hc,hc1,hc8,hcUnit,hcGap,hceps,hc64,
    tau,htau,seed,e,zeta,L,g,L2,c2,htauB,htauT,htauHalf,hseed,hseedTau,
    he,hzeta,hzseed,hL,hg,hgrid,hL2,hc2,deltaRet,hdRet,hdRet1,hdRetHistory,hdRetCleanup,hdRetRange,hdRet8,hsource⟩ :=
    NativePrescribedPopulationParentConfiguration.exists_prescribed_population_parent_configuration
      d J K hJ _hK hk epsilon hepsilon
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
  exact stage_with_parent_graph h original R E1 F P a level schedule L L2 eta0 c tau seed zeta htau c2 ell j
    selected depths Khalf epsilon Rel hepsilon he0.le heeps hc hc1 hceps hHalf rfl hgrain htauB hgrid
    hrcut hidentity (by omega) hBackbone hmid (hMetricCut D.thickness h.1.2.1 hDMetric ell)
    (hParents selected depths hdepths hcoarse Rel hrefl hsymm)

end NativePrescribedParentGraphConfiguration
