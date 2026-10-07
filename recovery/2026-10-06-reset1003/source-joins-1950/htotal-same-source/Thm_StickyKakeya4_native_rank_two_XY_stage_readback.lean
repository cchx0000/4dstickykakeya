/- UNVERIFIED actual stage readback. No strict Lean check has run. -/
import Theorems.Thm_StickyKakeya4_native_generic_XY_rank
import Theorems.Thm_StickyKakeya4_native_parent_original_point_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 9000000
noncomputable section
namespace NativeRankTwoXYStageReadback
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeGenericReferenceData NativeGenericXYRank NativePostGraphXYHookStage NativePostGraphXYHookData
open NativeRankExponentHierarchy NativeActualMesoscopicRankConfiguration NativeRankRadiusMenu
open NativeMiddleGrainParentBudget NativeSquaredGrainQueries NativeParentHorizontalQueryMenu
open NativeJointUniformCoarseRelations NativeLocalPairUniformCore NativeRetainedRankCutoffs
open NativeSecondRefinementCost NativeCompatibleWeightedRetention NativeActualGrainHistory
open NativeRetainedGrainHistory NativeCompatibleNodeDirections NativeOriginalPacketReference
open NativeQueriedVertexWeights NativeDirectionRankDichotomy NativeSpatialAngularGeometry
open NativeParentOriginalPointMenu SelfUniform WeightedRichDirectionalLayers
open scoped BigOperators ENNReal

/-- This is the exact second-stage dimension, including the newly installed
original-point slot and all existing paired/history and row relations. -/
def secondDimension (g dOld Jhorizontal Khalf : ℕ) : ℕ :=
  ((size (dOld+1) (Jhorizontal+1)+((2*Khalf+1)+(2*Khalf+1))+
    ((2*Khalf+1)+(2*Khalf+1))+((2*Khalf+1)+(2*Khalf+1))+1)+(g+1)*(g+1))

/-- Unpack the actual E2/history/profile branch on its stored middle index.
The caller passes the genuine HasXYStage returned by the original producer,
specialized to its installed parent-original-point relation. No point
uniformity, population, history mass, or third-core continuation is assumed
separately. Every returned object comes from this one stage witness. -/
theorem extract {n g L L2 L3 dOld dExtra Jhorizontal Khalf : ℕ}
    {D : FiniteScaleSource n} {eta tau seed e zeta eta0 c c2 epsilonGraph : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau)
    (ref : Reference h tau htau seed e zeta L g)
    (F : Finset (Fin n × Index)) (hFref : F⊆ref.E1)
    (oldPlane : Index → Submodule ℝ E4) (j : Fin (g+1))
    (hNearF : ∀z∈F,Metric.infDist (slopeVector D z.1) (oldPlane z.2:Set E4) ≤
      radius (rankWindow tau) (rankWindow_pos htau).le g ref.level j)
    (selected : Fin (2*Khalf)) (_hKhalf : 0 < Khalf)
    (hmid : historyDepth (2*Khalf) (ref.schedule j).val selected=middleDepth (ref.schedule j).val)
    (RelOld : Fin dOld → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hstage : HasXYStage (J:=2*Khalf) h ref.original ref.R ref.E1 F oldPlane ref.a ref.level
      ref.schedule ref.dimension L L2 eta0 c tau seed zeta htau c2 (1:Fin 4) j selected
      Jhorizontal (dExtra+3) L3 Khalf epsilonGraph
      (NativeParentOriginalPointMenu.relations D ref.a (middleDepth (ref.schedule j).val) RelOld)) :
    let m := middleDepth (ref.schedule j).val
    let r := radius (rankWindow tau) (rankWindow_pos htau).le g ref.level j
    let lambda := r^(rankLoss eta0 c (1:Fin 4))/(4*((g:ℝ)+1))
    let F1 := factor ref.dimension (g+1) L
    let G := retentionCost (secondDimension g dOld Jhorizontal Khalf) 1 L2
    let F2 := factor (secondDimension g dOld Jhorizontal Khalf) 1 L2
    let Q2 := NativeSourceSizeBounds.radix F.card L2
    ∃q : ℝ,0 < q ∧ q ≤ 1 ∧ r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q ∧
    ∃E2 : Finset (Fin n × Index),E2⊆F ∧ E2⊆ref.E1 ∧ E2.Nonempty ∧
      0 < G ∧ G ≤ F2 ∧ 0 < Q2 ∧
      (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2) ∧
      (∀i x y,x∈E2 → y∈E2 →
        degree (fun _ : Fin n × Index => 1) (NativeParentOriginalPointMenu.relations D ref.a m RelOld i) E2 x ≤
        Q2^2*degree (fun _ : Fin n × Index => 1) (NativeParentOriginalPointMenu.relations D ref.a m RelOld i) E2 y) ∧
      (∀p : Parent,HasUniformFibers (parentEdges D ref.a (2^m) E2 p) Q2 Prod.snd) ∧
    ∃points S0 : Finset Index,points⊆S0 ∧ S0⊆E2.image Prod.snd ∧
      r^(5*rankLoss eta0 c (1:Fin 4))*(E2.card:ℝ) ≤
        (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ) ∧
    ∃(point : Index → Index) (tuple : Index → Fin 2 → (Fin n × Index))
      (anchor : Index → Fin 2 → Fin n),
      IsNodeDirectionSystem D ref.a m E2 S0 q 2 point tuple anchor ∧
      (∀k∈S0,Module.finrank ℝ (oldPlane k)=2) ∧
      (∀z∈E2,Metric.infDist (slopeVector D z.1) (oldPlane z.2:Set E4) ≤ r) ∧
    ∃Lgrain : ℕ,
      HasXYParentProfiles h ref.original ref.R ref.E1 E2 ref.a ref.level m
        (nodePlane D tuple) points q 2 Q2 F1 G Lgrain lambda zeta tau seed c2
        Jhorizontal (dExtra+3) L3 (ref.schedule j).val Khalf tuple r epsilonGraph := by
  intro m r lambda F1 G F2 Q2
  obtain ⟨previous,_hPrevious,test,_hTest,_hrq,_hqr,hqRaw,E2,hE2F,hE2n,_hE2old,
    _hRetF,_hRetE1,_hNearE2,Hcaller2,_hGrains,_hPoint,_hRows,_hRich,H2,hPlane,_hTuples,
    _hFamily,Hhistory,_hQueries,_hColumns,_hCounts⟩ := Hstage
  let q := radius (rankWindow tau) (rankWindow_pos htau).le g ref.level test
  have hq : 0 < q := radius_pos _ _ _ _ _
  have hq1 : q ≤ 1 := (radius_le_one_div_48 _ _ _ _ _).trans (by norm_num)
  have h21 : E2⊆ref.E1 := hE2F.trans hFref
  have hG : 0 < G := by dsimp [G,retentionCost]; positivity
  have hGF : G ≤ F2 := retained_cost_le_factor (secondDimension g dOld Jhorizontal Khalf) 1 L2 (by omega)
  have hQ2 : 0 < Q2 := lt_of_lt_of_le (by norm_num : 0 < (4:ℕ))
    (NativeSourceSizeBounds.radix_four_le F.card L2)
  have Hpoint := (parent_original_point_uniformities D ref.a m RelOld E2 Q2 Hcaller2).2
  obtain ⟨C,_hC,S0,hS0,_hS,_hInjective,_hPointMass,_hRetained,_hCompat,_hWitness,_hTrace,
    point,tuple,anchor,Hsys,_hWord,_hSame,_hHistory,_hHistoryRet,Hcleanup⟩ := Hhistory
  obtain ⟨points,hPointsFinal,_hPointsN,_hHalf,_hTotal,hMass,_hGrainCounts,_hDense,
    _hSysFinal,_hFinalTrace,Hprofiles⟩ := Hcleanup
  have hPoints : points⊆S0 := hPointsFinal.trans
    (history_antitone D E2 (historyDepth (2*Khalf) (ref.schedule j).val) 2
      (fun i => natStageDirectionIndex h (tuple i)) S0 (Nat.zero_le (2*Khalf)))
  have HsysMiddle : IsNodeDirectionSystem D ref.a m E2 S0 q 2
      (point selected) (tuple selected) (anchor selected) := by
    simpa only [hmid] using Hsys selected
  have hMass' : r^(5*rankLoss eta0 c (1:Fin 4))*(E2.card:ℝ) ≤
      (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ) := by
    convert hMass using 1 <;> norm_num <;> ring
  refine ⟨q,hq,hq1,hqRaw,E2,hE2F,h21,hE2n,hG,hGF,hQ2,H2,Hcaller2,Hpoint,
    points,S0,hPoints,hS0,hMass',point selected,tuple selected,anchor selected,HsysMiddle,?_,?_,?_⟩
  · intro k hk
    exact hPlane k (hS0 hk)
  · intro z hz
    exact hNearF z (hE2F hz)
  · refine ⟨_,?_⟩
    simpa only [hmid] using Hprofiles

end NativeRankTwoXYStageReadback

