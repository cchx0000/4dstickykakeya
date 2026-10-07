import Theorems.Thm_StickyKakeya4_native_actual_physical_third_prerequisites
/- Actual reference-to-one-T composition. Originally drafted without verification; consult current receipts. -/
import Theorems.Thm_StickyKakeya4_native_generic_XY_rank
import Theorems.Thm_StickyKakeya4_native_parent_original_point_menu
import Theorems.Thm_StickyKakeya4_native_configured_third_relation
import Theorems.Thm_StickyKakeya4_native_paid_third_budget

open NativeGrainHeightProjectionSource NativeGrainQuotientFibers NativeSharpXPowerAlgebra
open NativeRetainedGrainHistory NativeLocalPairUniformCore NativeParentHeightAlignment NativeCubicalIncidenceCounts

/- Original source: Thm_StickyKakeya4_native_rank_two_XY_stage_readback.lean; SHA256 b1500d282338ba2653fc70143d9874d678d23462f83b7c9b701edfd44c5e6915. -/
/- UNVERIFIED actual stage readback. No strict Lean check has run. -/

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
    simpa [m,q,hmid] using Hsys selected
  have hMass' : r^(5*rankLoss eta0 c (1:Fin 4))*(E2.card:ℝ) ≤
      (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ) := by
    simpa [r,show (2:ℝ)*2+1=5 by norm_num] using hMass
  refine ⟨q,hq,hq1,hqRaw,E2,hE2F,h21,hE2n,hG,hGF,hQ2,H2,Hcaller2,Hpoint,
    points,S0,hPoints,hS0,hMass',point selected,tuple selected,anchor selected,HsysMiddle,?_,?_,?_⟩
  · intro k hk
    exact hPlane k (hS0 hk)
  · intro z hz
    exact hNearF z (hE2F hz)
  · refine ⟨_,?_⟩
    simpa [m,q,r,lambda,F1,G,Q2,secondDimension,nodePlane,hmid] using Hprofiles

end NativeRankTwoXYStageReadback
end -- original anonymous section NativeRankTwoXYStageReadback

/- Original source: Thm_StickyKakeya4_native_actual_coherent_height_core_full.lean; SHA256 fcb25b2b8ce9da2e12d1637363d6c51007d9d23e6e8cf1065bb1061b8bccf0f0. -/
/- UNVERIFIED same-E2/one-third-core composition. No strict Lean check has run. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeActualCoherentHeightCoreFull
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeGenericReferenceData NativeExtraQueriedRankConfiguration
open NativeConditionalReferenceMenu NativeSourcePhysicalCoherence NativePhysicalCoherentThirdJoin
open NativeActualHeightThirdJoin NativePostGraphXYHookData NativePostGraphSliceData
open NativeJointUniformCoarseRelations NativeRankExponentHierarchy NativeActualMesoscopicRankConfiguration
open NativeMiddleGrainParentBudget NativeSquaredGrainQueries NativeSpatialAngularGeometry
open NativeCompatibleNodeDirections NativeDirectionRankDichotomy NativeOriginalPointSaturation
open NativeSaturatedMixedGrainCore NativeParentGrainIncidenceCleanup NativeParentHeightGraphCore
open NativeHeightMetricMenu NativeProjectorCellChart NativeActualHeightSlopeVariation
open NativeHeightSlopeCoordinates NativeHorizontalGraphCoordinates NativeOriginalCellChartGeometry
open NativeReferenceXYGridPoints NativeReferenceXYGridField NativeHorizontalGrainSlice
open NativeWeightedGrainQuotientGeometry NativeTranslatedGrainHeightSelection
open NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric NativeTranslatedHeightFreeze
open NativeThirdXYSourceData NativeRetainedSliceCore NativeRetainedSliceBudgetAlgebra
open NativeReferenceSliceBudgetAlgebra NativeReferenceSliceBudgetReadback
open NativeAnisotropicSliceLabels NativeReferenceColumnExponents NativeActivePhasePopulation
open NativeOriginalPacketReference NativeQueriedVertexWeights
open NativeConfiguredThirdRelation
open NativePaidThirdBudget
open NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu NativeIncidentAffineAnchorSource
open NativePaidMeshAngularUpper NativeFixedCompactKakeyaExponent CanonicalConfiguredE4Bridge
open scoped BigOperators Matrix.Norms.Elementwise

/-- Integral support widths of the actually chosen dyadic base. -/
lemma integral_width (m u s : ℕ) (R0 : ℕ)
    (hbase : mu m*(R0:ℝ)=(2:ℝ)⁻¹^u) (hs : s ≤ u+6) :
    64/((2^s:ℕ):ℝ)=(mu m*(R0:ℝ))*((2^(u+6-s):ℕ):ℝ) := by
  have he : (2:ℝ)^(u+6-s)*(2:ℝ)^s=(2:ℝ)^u*64 := by
    rw [←pow_add,Nat.sub_add_cancel hs,pow_add]
    norm_num
  rw [hbase,inv_pow]
  push_cast
  field_simp
  nlinarith only [he]

/-- The source profile is unpacked here. Its actual graph is passed first
to physical coherence and then, through the returned paid-subset continuation,
to the literal height/support/residue selector and the unique third core.
Hnext is constructed inside this proof. The original-point relation is read
from the very E2 caller table that selected this E2. -/
theorem from_parent_profiles {n g L dOld dExtra Jhorizontal L3 : ℕ}
    {D : FiniteScaleSource n} {eta zeta seed tau e a eta0 c c2 r q epsilonGraph : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau)
    (ref : Reference h tau htau seed e zeta L g) (ha : a=ref.a)
    (Kcoh Ksupport Kupper Khalf : ℕ) (loss seedCap deltaUpper : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (Hupper : HasUpperEngine Kupper (c^3/8) loss seedCap deltaUpper)
    (Hcaller1 : HasCallerUniformities ref (factory g Kupper))
    (heta : 0 ≤ eta) (hzeta : 0 ≤ zeta) (hetaSeed : eta ≤ seed/8)
    (hzseed : zeta ≤ seed/256) (hseedCap : seed ≤ seedCap) (hUpperSmall : D.thickness ≤ deltaUpper)
    (he0 : 0 < eta0) (hcUnit : c ≤ 1/(eta0+1))
    (hr : 0 < r) (hr1 : r ≤ 1) (hrdelta : r ≤ D.thickness^(cutoff c (1:Fin 4)))
    (htauHalf : tau ≤ 1/2) (hTau : tau ≤ commonBudget eta0 c/1024)
    (hTauHistory : tau ≤ commonBudget eta0 c/(1000*(((2*Khalf:ℕ):ℝ)+1)))
    (hseed : seed ≤ tau/16384) (hc2 : c2=commonBudget eta0 c/4)
    (hg : 0 < g) (hgrid : 1/(g:ℝ) < rankWindow tau/4)
    (j : Fin (g+1)) (hstop18 : 18 ≤ (ref.schedule j).val)
    (hstopCap : (ref.schedule j).val ≤ ref.level/4)
    (hidentity : 48*((2^(ref.schedule j).val:ℕ):ℝ)*r=1)
    (hdelta : 64*D.thickness ≤ r^2)
    (hExtraSmall : D.thickness ≤ NativeHistoryDimensionRange.extraCutoff c hc hc1 g)
    (heGraph : 0 < epsilonGraph) (heGraphHalf : epsilonGraph ≤ 1/2)
    (heSmall : eta0 ≤ epsilonGraph) (hcSmall : c ≤ epsilonGraph/24)
    (hKhalf : 0 < Khalf) (hq : 0 < q) (hq1 : q ≤ 1)
    (hqraw : r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q)
    (hError : D.thickness^(cutoff c (1:Fin 4)*epsilonGraph/2) ≤ 1/errorConstant)
    (E2 : Finset (Fin n × Index)) (h21 : E2⊆ref.E1) (hE2n : E2.Nonempty)
    (F2 G Q2 Lgrain : ℕ) (hG : 0 < G) (hGF : G ≤ F2)
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2))
    (epsilonPaid deltaBudget : ℝ)
    (Hbudget : HasBudget epsilonPaid eta0 c g Khalf (dExtra+3) Jhorizontal L3 deltaBudget)
    (hBudgetSmall : D.thickness ≤ deltaBudget)
    (points S0 : Finset Index) (hPoints : points⊆S0)
    (hMass : r^(5*rankLoss eta0 c (1:Fin 4))*(E2.card:ℝ) ≤
      (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ))
    (point : Index → Index) (tuple : Index → Fin 2 → (Fin n × Index))
    (anchor : Index → Fin 2 → Fin n)
    (oldPlane : Index → Submodule ℝ E4)
    (hOld : ∀k∈S0,Module.finrank ℝ (oldPlane k)=2)
    (hNear : ∀z∈E2,Metric.infDist (slopeVector D z.1) (oldPlane z.2:Set E4) ≤ r) :
    let m := middleDepth (ref.schedule j).val
    let F1 := factor ref.dimension (g+1) L
    let lambda := r^(rankLoss eta0 c (1:Fin 4))/(4*((g:ℝ)+1))
    let W : ℝ := (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)
    let population := (lambda*W/(2*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ)))*D.thickness^eta
    let retain := population/rowConstant
    let PL := profileLower D.thickness population
      (columnEpsilon D.thickness lambda (seed/8) c2)
      tau (seed/8) (min (NativeAllTwoScaleConfiguration.boundaryWindow tau) ((tau/16)/1000))
    let PU := profileUpper D.thickness (columnEpsilon D.thickness lambda (seed/8) c2) tau
    let plane := nodePlane D tuple
    let threshold := (((cutEdges E2 points).card:ℝ)/
      (2*((((cutEdges E2 points).image (mixedLabel D a m plane 2)).card):ℝ)))
    IsNodeDirectionSystem D a m E2 S0 q 2 point tuple anchor →
    ∀RelOld : Fin dOld → (Fin n × Index) → (Fin n × Index) → Prop,
    (∀i x y,x∈E2 → y∈E2 →
      SelfUniform.degree (fun _ : Fin n × Index => 1)
        (NativeParentOriginalPointMenu.relations D a m RelOld i) E2 x ≤
      Q2^2*SelfUniform.degree (fun _ : Fin n × Index => 1)
        (NativeParentOriginalPointMenu.relations D a m RelOld i) E2 y) →
    HasXYParentProfiles h ref.original ref.R ref.E1 E2 a ref.level m plane points q 2 Q2 F1 G Lgrain
      lambda zeta tau seed c2 Jhorizontal (dExtra+3) L3 (ref.schedule j).val Khalf tuple r epsilonGraph →
    ∀u R0 : ℕ,0 < R0 → rho m ≤ mu m*(R0:ℝ) → mu m*(R0:ℝ)=(2:ℝ)⁻¹^u →
    ∀depths : Fin Kcoh → ℕ,
      (∀k,6 ≤ depths k ∧ depths k ≤ m+6) →
      (∀k,(5/4:ℝ)*(rho m)^(1-2*epsilonGraph) ≤ 64/((2^(depths k):ℕ):ℝ)) →
    ∀supportDepths : Fin Ksupport → ℕ,(∀k,supportDepths k ≤ u+6) →
    ∀extras : Parent → Finset (Fin n × Index) → (P : Submodule ℝ E4) → (hP : P≤heightKernel) → (hd : Module.finrank ℝ P=1) →
      (ℤ → Matrix (Fin 2) (Fin 1) ℝ) → (ℤ → Matrix (Fin 2) (Fin 1) ℝ) →
      Finset (Fin n × Index) → Fin dExtra → (Fin n × Index) → (Fin n × Index) → Prop,
    (∀p Hgraph P hP hd f Fcfg U k x,extras p Hgraph P hP hd f Fcfg U k x x) →
    (∀p Hgraph P hP hd f Fcfg U k x y,extras p Hgraph P hP hd f Fcfg U k x y → extras p Hgraph P hP hd f Fcfg U k y x) →
    ∃p : Parent,∃Hp Hgraph : Finset (Fin n × Index),
      population*(NativeLocalParentSource.parentLabels D ref.R a (2^m) p).card ≤ D.thickness*Hp.card ∧
      Hp.card ≤ selectionCost Khalf*Hgraph.card ∧
    ∃(P0 : Submodule ℝ E4) (hP0 : P0≤heightKernel) (hd : Module.finrank ℝ P0=1)
      (f : ℤ → Matrix (Fin 2) (Fin 1) ℝ),
      (∀height,‖f height‖≤(1/4:ℝ)) ∧
      let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P0 hP0
        (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
      let F := fixedField D a m 2 plane Sq f
      let Gcoh := NativeActualNewCutBudget.coherenceCharge Kcoh 2 g meshAngularConstant rowConstant
        r loss (rankLoss eta0 c (1:Fin 4)) (r^(-2*epsilonGraph)) extremalExponent
        (fun k => 64/((2^(depths k):ℕ):ℝ))
      let Ctotal := (quotientCost q*(Gcoh:ℝ))*
        ((((8*R0)*53^(4*Ksupport))*8^4:ℕ):ℝ)
      ∃xi : Index → EuclideanSpace ℝ (Fin 2),
      ∃Spre U T : Finset (Fin n × Index),∃Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ,
      Spre.Nonempty ∧ U.Nonempty ∧ T.Nonempty ∧ T⊆U ∧ U⊆Spre ∧ Spre⊆Hgraph ∧ Hgraph⊆ref.E1 ∧
      (Hgraph.card:ℝ) ≤ Ctotal*U.card ∧ 0 < Ctotal ∧
      Ctotal=quotientCost q*(NativeActualNewCutBudget.newCutCharge Kcoh Ksupport 2 g R0
        meshAngularConstant rowConstant r loss (rankLoss eta0 c (1:Fin 4))
        (r^(-2*epsilonGraph)) extremalExponent (fun k => 64/((2^(depths k):ℕ):ℝ)):ℝ) ∧
      (∀height,‖Fcfg height‖≤(1/4:ℝ)) ∧
      let Q3 := NativeSourceSizeBounds.radix U.card L3
      let F3 := refinementCost ((dExtra+3)+2) (Jhorizontal+1) L3
      let CX := (Ctotal/quotientCost q)*fiberCoefficient D.thickness eta zeta tau (seed/8) c2
        lambda (W/(E2.card:ℝ)) F1 G Q2 F3 Q3 q 2
      1 ≤ F3 ∧ 1 ≤ Q3 ∧
      (F3:ℝ)*(Q3:ℝ)^4 ≤ D.thickness^(-(commonBudget eta0 c/4)) ∧
      HasThirdXYSourceData (J:=Jhorizontal) (ell:=2) D zeta a m plane E2 Hgraph U T P0 hP0
        (by norm_num) (by norm_num) hd f p population PL PU Q2 retain (selectionCost Khalf)
        Ctotal threshold L3
        (completeRelations D a m p .oneTwo P0 hP0 hd F Fcfg R0 u (extras p Hgraph P0 hP0 hd f Fcfg U)) CX ∧
      (∀z∈U,parentLabel D a (2^m) z.1=p) ∧
      (∀z∈T,parentLabel D a (2^m) z.1=p) ∧
      (∀z∈T,Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))=F (translatedHeight D a m z.2)) ∧
      (∀z∈T,∀w∈T,translatedHeight D a m z.2/((8*R0:ℕ):ℤ)=
        translatedHeight D a m w.2/((8*R0:ℕ):ℤ) → translatedHeight D a m z.2=translatedHeight D a m w.2) ∧
      (∀x∈T.image (fun z => NativeActualConfiguredPoint.point D a m p .oneTwo P0 hP0 hd F Fcfg R0 z.2),
       ∀y∈T.image (fun z => NativeActualConfiguredPoint.point D a m p .oneTwo P0 hP0 hd F Fcfg R0 z.2),
       x≠y → (mu m*(R0:ℝ))/64≤dist x y) ∧
      ∀k z w,z∈T → w∈T →
        physicalCell D a (2^m) (2^(depths k)) p z.2=physicalCell D a (2^m) (2^(depths k)) p w.2 →
        ‖f (rawHeight D m z.2)-f (rawHeight D m w.2)‖<64/((2^(depths k):ℕ):ℝ) ∧
        ‖xi z.2-xi w.2‖≤(129/4:ℝ)*(64/((2^(depths k):ℕ):ℝ)) := by
  intro m F1 lambda W population retain PL PU plane threshold Hsys RelOld Hcaller2
    Hprofiles u R0 hR0 hbase hbaseEq depths hdepths hErrorWindow
    supportDepths hSupport extras hExtraRefl hExtraSymm
  subst a
  have Hpoint := (NativeParentOriginalPointMenu.parent_original_point_uniformities
    D ref.a m RelOld E2 Q2 Hcaller2).2
  obtain ⟨_hTheta,_hPopulation,_hRetain,H,hHpoints,_hHn,_hHalf,p,_hp,_hHpn,hPop,
    hReference,_hGrains,_hThreshold,hsat,_hProfiles,_hCleaned,_hHeightL,_hHeightU,_hPhases,
    _hPlane,hMetricPaid,_hell,_hell4,HgraphData⟩ := Hprofiles
  obtain ⟨Nodes,_hNodes,u0,_hu0,hP0,hd,f,B,hBN,_hBn,Hgraph,hGraphEq,hGraphHp,hGraphN,hGraphNodes,
    hGraphRet,hGraphParent,_hAlign,_hResid,_hZero,hF,hCell,hRead,_hGraph,hMetricGraph,_hFib,HfinishAll⟩ := HgraphData
  let Hp := parentEdges D ref.a (2^m) H p
  let P0 := horizontalPlane D tuple u0
  have hHE2 : H⊆E2 := hHpoints.trans (cutEdges_subset E2 points)
  have hHpE2p : Hp⊆parentEdges D ref.a (2^m) E2 p := filter_subset_filter _ hHE2
  have hGraphE2 : Hgraph⊆E2 := hGraphHp.trans ((filter_subset _ _).trans hHE2)
  have hGraphRef : Hgraph⊆ref.E1 := hGraphE2.trans h21
  have Hsat : Saturated (parentEdges D ref.a (2^m) E2 p) Hgraph Prod.snd := by
    rw [hGraphEq]
    exact nodeCut_saturation D m _ _ ⟨hHpE2p,hsat⟩ B
  have hGraphPoints : ∀z∈Hgraph,z.2∈S0 := by
    intro z hz
    exact hPoints (mem_filter.mp (hHpoints (mem_filter.mp (hGraphHp hz)).1)).2
  have hNode (z : Fin n × Index) (hz : z∈Hgraph) : spatialLabel D (2^m) z.2∈B := by
    rw [←hGraphNodes]
    exact mem_image_of_mem (fineNode D m) hz
  have hGraphNode : ∀k∈Hgraph.image Prod.snd,spatialLabel D (2^m) k∈Nodes := by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
    exact hBN (hNode z hz)
  have hCell' : ∀k∈Hgraph.image Prod.snd,cell P0=cell (horizontalPlane D tuple (spatialLabel D (2^m) k)) :=
    fun k hk => hCell _ (hGraphNode k hk)
  have hRead' : ∀k∈Hgraph.image Prod.snd,f (rawHeight D m k)=
      nodeSlope P0 hP0 2 (by norm_num) (by norm_num) hd
        (horizontalPlane D tuple (spatialLabel D (2^m) k)) (horizontalPlane_le D tuple _) :=
    fun k hk => hRead _ (hGraphNode k hk)
  have hMetric : ∀z∈Hgraph,∀w∈Hgraph,‖f (rawHeight D m z.2)-f (rawHeight D m w.2)‖ ≤
      r^(-2*epsilonGraph)*|chartHeightCoordinate m 0 (rawHeight D m z.2)-
        chartHeightCoordinate m 0 (rawHeight D m w.2)| := by
    intro z hz w hw
    have hh := (hMetricGraph _ (hNode z hz) _ (hNode w hw)).2 0
    exact hh.trans (mul_le_mul_of_nonneg_right hMetricPaid (abs_nonneg _))
  have hRefRet :
      (population/rowConstant)*(parentEdges D ref.a (2^m) ref.E1 p).card ≤
        (parentEdges D ref.a (2^m) E2 p).card :=
    (hReference ref.E1 ref.core.1).trans (by exact_mod_cast card_le_card hHpE2p)
  have Hcoh := NativePhysicalCoherentThirdJoin.from_actual_source Kcoh Kupper c loss seedCap deltaUpper
    hc hc1 Hupper
  obtain ⟨_choice,xi,_hChoice,_hResidual,Pcoh,_hPcoh,hSpreN,hSpreFull,_hSpreSat,
    _hCoherenceCost,hCpre,hPreRet,_hFiber,hCoherent,_hHeightCoherent,HnextRaw⟩ :=
    Hcoh n D eta zeta seed tau e eta0 c2 r q epsilonGraph (r^(-2*epsilonGraph))
      h htau L g Khalf heta hzeta hetaSeed hzseed hseedCap hUpperSmall ref Hcaller1
      E2 Hgraph points h21 hE2n hGraphN (1:Fin 4) (by norm_num) (by norm_num)
      he0 hcUnit hr hr1 hrdelta (by convert hMass using 1 <;> norm_num <;> ring) htauHalf hTau hTauHistory hseed hc2 hg hgrid
      F2 G Q2 hG hGF H2 j hstop18 hstopCap hidentity hdelta hExtraSmall p Hsat (Hpoint p) hRefRet
      heGraph heGraphHalf heSmall hcSmall hKhalf hq hq1 hqraw hError (by positivity)
      S0 point tuple anchor hGraphPoints Hsys oldPlane hOld hNear P0 hP0 hd hCell'
      f hF hRead' hMetric Jhorizontal (dExtra+3) L3 population PL PU retain
      (selectionCost Khalf) threshold HfinishAll depths hdepths hErrorWindow
  let Sq := NativeWeightedGrainQuotientGeometry.retained D ref.a m 2 plane Hgraph P0 hP0
    (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
  let Sfull := second D ref.a m 2 plane Sq
  let F := fixedField D ref.a m 2 plane Sq f
  let Spre := NativeFinitePointCoherence.lift Sfull Prod.snd Pcoh
  let Gcoh := NativeActualNewCutBudget.coherenceCharge Kcoh 2 g meshAngularConstant rowConstant
    r loss (rankLoss eta0 c (1:Fin 4)) (r^(-2*epsilonGraph)) extremalExponent
    (fun k => 64/((2^(depths k):ℕ):ℝ))
  let Cpre := quotientCost q*(Gcoh:ℝ)
  have hCpreNorm : 0 < Cpre := by
    simpa [Cpre,Gcoh,NativeActualNewCutBudget.coherenceCharge,
      NativeActualNewCutBudget.offsetCharge,mul_assoc] using hCpre
  have hPreRetNorm : (Hgraph.card:ℝ) ≤ Cpre*Spre.card := by
    simpa [Cpre,Gcoh,NativeActualNewCutBudget.coherenceCharge,
      NativeActualNewCutBudget.offsetCharge,mul_assoc,Spre,Sfull,Sq,plane,m] using hPreRet
  have hFullGraph : Sfull⊆Hgraph :=
    (second_subset D ref.a m 2 plane Sq).trans (NativeWeightedGrainQuotientSelection.selected_subset _ _ _ _)
  have hSpreGraph : Spre⊆Hgraph := hSpreFull.trans hFullGraph
  have Hnext : ∀U⊆Spre,∀Cextra : ℝ,0 < Cextra → (Spre.card:ℝ)≤Cextra*U.card →
      ∀Rel3 : Fin (dExtra+3) → (Fin n × Index) → (Fin n × Index) → Prop,
      (∀k z,Rel3 k z z) → (∀k z w,Rel3 k z w → Rel3 k w z) →
      let Ctotal := Cpre*Cextra
      let Q3 := NativeSourceSizeBounds.radix U.card L3
      let F3 := refinementCost ((dExtra+3)+2) (Jhorizontal+1) L3
      let CX := (Ctotal/quotientCost q)*fiberCoefficient D.thickness eta zeta tau (seed/8) c2
        lambda (W/(E2.card:ℝ)) F1 G Q2 F3 Q3 q 2
      ∃T,HasThirdXYSourceData (J:=Jhorizontal) (ell:=2) D zeta ref.a m plane E2 Hgraph U T P0 hP0
        (by norm_num) (by norm_num) hd f p population PL PU Q2 retain (selectionCost Khalf)
        Ctotal threshold L3 Rel3 CX := by
    intro U hU Cextra hExtra hRet Rel3 hRefl hSymm
    obtain ⟨T,HT,_hCoh,_hHeight,_hMetric⟩ := HnextRaw U hU Cextra hExtra hRet Rel3 hRefl hSymm
    exact ⟨T,HT⟩
  let M : Fin Ksupport → ℕ := fun k => 2^(supportDepths k)
  let Jsupport : Fin Ksupport → ℕ := fun k => 2^(u+6-supportDepths k)
  have hmu := mu_pos m
  have hIntegral : ∀k,64/(M k:ℝ)=(mu m*(R0:ℝ))*(Jsupport k:ℝ) :=
    fun k => integral_width m u _ R0 hbaseEq (hSupport k)
  have hMenu : ∀k,mu m*(R0:ℝ) ≤ 64/(M k:ℝ) := by
    intro k
    rw [hIntegral k]
    have hJ : (1:ℝ) ≤ Jsupport k := by
      dsimp [Jsupport]
      exact_mod_cast (show 1 ≤ (2:ℕ)^(u+6-supportDepths k) by
        have hp : 0 < (2:ℕ)^(u+6-supportDepths k) := by positivity
        omega)
    exact le_mul_of_one_le_right (by positivity) hJ
  let Rels := fun (U : Finset (Fin n × Index)) (Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
      (_Gcfg : ℤ → ℝ) =>
    completeRelations D ref.a m p .oneTwo P0 hP0 hd F Fcfg R0 u (extras p Hgraph P0 hP0 hd f Fcfg U)
  obtain ⟨Bh,_hBh,hCfg,B0,_hB0,_color,BhFinal,_hBFinal,hUN,hUS,hHeightCost,_hOldFib,
    hFrozen,_hFine,_hTime,_hColor,hSep,_hTimeSep,_hWide,_hSingle,_hRaw,T,HT,hTU,_hFinalRaw,hSingleT⟩ :=
    NativeActualHeightThirdJoin.attach_rank_two h ref.a zeta m
      (middle_depth_bounds (ref.schedule j).val (by omega)).1 p plane E2 Hgraph Spre hSpreN
      (fun z hz => hGraphParent z (hSpreGraph hz)) P0 hP0 hd hSpreFull f hF
      q tau (seed/8) c2 lambda (W/(E2.card:ℝ)) population PL PU retain
      (selectionCost Khalf) Cpre threshold F1 G Q2 L3 Hnext
      (fun _ : ℤ => (0:ℝ)) R0 hR0 hbase M Jsupport (fun _ => by dsimp [M]; positivity)
      hMenu hIntegral Rels
      (fun U Fcfg _Gcfg => completeRelations_refl D ref.a m p .oneTwo P0 hP0 hd F Fcfg R0 u _
        (hExtraRefl p Hgraph P0 hP0 hd f Fcfg U))
      (fun U Fcfg _Gcfg => completeRelations_symm D ref.a m p .oneTwo P0 hP0 hd F Fcfg R0 u _
        (hExtraSymm p Hgraph P0 hP0 hd f Fcfg U))
  let Sh := NativeMatrixHeightWholePoint.edgeLift Spre Prod.snd Bh
  let Fcfg := frozen D ref.a m R0 Sh F
  let U0 := NativeMatrixHeightWholePoint.edgeLift Sh Prod.snd B0
  let U := NativeMatrixHeightWholePoint.edgeLift U0 Prod.snd BhFinal
  let Cextra : ℝ := ((((8*R0)*53^(4*Ksupport))*8^4:ℕ):ℝ)
  let Ctotal := Cpre*Cextra
  have hTotal : (Hgraph.card:ℝ) ≤ Ctotal*U.card := by
    have hh : (Spre.card:ℝ) ≤ Cextra*U.card := by
      dsimp only [Cextra,U,U0,Sh]
      exact_mod_cast hHeightCost
    exact hPreRetNorm.trans (by simpa only [Ctotal,mul_assoc] using
      mul_le_mul_of_nonneg_left hh hCpreNorm.le)
  have hTotalPos : 0 < Ctotal := mul_pos hCpreNorm (by dsimp [Cextra]; positivity)
  have hCostRead : Ctotal=quotientCost q*(NativeActualNewCutBudget.newCutCharge Kcoh Ksupport 2 g R0
      meshAngularConstant rowConstant r loss (rankLoss eta0 c (1:Fin 4))
      (r^(-2*epsilonGraph)) extremalExponent (fun k => 64/((2^(depths k):ℕ):ℝ)):ℝ) :=
    source_total_charge q Kcoh Ksupport 2 g R0 meshAngularConstant rowConstant
      r loss (rankLoss eta0 c (1:Fin 4)) (r^(-2*epsilonGraph)) extremalExponent _
  have hUold : U⊆incidences ref.original :=
    hUS.trans (hSpreGraph.trans (hGraphRef.trans (ref.core.1.trans (filter_subset _ _))))
  have hetaRaw : eta ≤ commonBudget eta0 c/32 := by
    have ht := commonBudget_pos he0 hc
    linarith only [hetaSeed,hseed,hTau,ht]
  have H3 := Hbudget.1 n D eta h hBudgetSmall heta hetaRaw
    ref.original ref.backbone.1 U hUold hUN
  have hF3 : 1 ≤ refinementCost ((dExtra+3)+2) (Jhorizontal+1) L3 := by
    have hh := refinementCost_pos ((dExtra+3)+2) (Jhorizontal+1) L3
    omega
  have hQ3 : 1 ≤ NativeSourceSizeBounds.radix U.card L3 :=
    (by norm_num : 1 ≤ (4:ℕ)).trans (NativeSourceSizeBounds.radix_four_le _ _)
  refine ⟨p,Hp,Hgraph,hPop,hGraphRet,P0,hP0,hd,f,hF,xi,Spre,U,T,Fcfg,
    hSpreN,hUN,HT.1.2.1,hTU,hUS,hSpreGraph,hGraphRef,hTotal,hTotalPos,hCostRead,hCfg,
    hF3,hQ3,H3,HT,?_,?_,?_,hSingleT,?_,?_⟩
  · intro z hz
    exact hGraphParent z (hSpreGraph (hUS hz))
  · intro z hz
    exact hGraphParent z (hSpreGraph (hUS (hTU hz)))
  · intro z hz
    exact (hFrozen z (hTU hz)).1
  · intro x hx y hy hxy
    exact hSep x (image_subset_image hTU hx) y (image_subset_image hTU hy) hxy
  · intro k z w hz hw hcell
    exact hCoherent k z w (hUS (hTU hz)) (hUS (hTU hw)) hcell

end NativeActualCoherentHeightCoreFull
end -- original anonymous section NativeActualCoherentHeightCoreFull

/- Original source: Thm_StickyKakeya4_native_actual_XY_stage_height_join_full.lean; SHA256 9aa2e1e69d9ce531a12726e6045890cf43dea2e14bb20e527bd4ab24291374df. -/
/- UNVERIFIED actual stage-to-one-T composition. No strict Lean check has run. -/
/- UNVERIFIED same-E2/one-third-core composition. No strict Lean check has run. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeActualXYStageHeightJoinFull
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeGenericReferenceData NativeExtraQueriedRankConfiguration
open NativeConditionalReferenceMenu NativeSourcePhysicalCoherence NativePhysicalCoherentThirdJoin
open NativeActualHeightThirdJoin NativePostGraphXYHookData NativePostGraphSliceData
open NativeJointUniformCoarseRelations NativeRankExponentHierarchy NativeActualMesoscopicRankConfiguration
open NativeMiddleGrainParentBudget NativeSquaredGrainQueries NativeSpatialAngularGeometry
open NativeCompatibleNodeDirections NativeDirectionRankDichotomy NativeOriginalPointSaturation
open NativeSaturatedMixedGrainCore NativeParentGrainIncidenceCleanup NativeParentHeightGraphCore
open NativeHeightMetricMenu NativeProjectorCellChart NativeActualHeightSlopeVariation
open NativeHeightSlopeCoordinates NativeHorizontalGraphCoordinates NativeOriginalCellChartGeometry
open NativeReferenceXYGridPoints NativeReferenceXYGridField NativeHorizontalGrainSlice
open NativeWeightedGrainQuotientGeometry NativeTranslatedGrainHeightSelection
open NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric NativeTranslatedHeightFreeze
open NativeThirdXYSourceData NativeRetainedSliceCore NativeRetainedSliceBudgetAlgebra
open NativeReferenceSliceBudgetAlgebra NativeReferenceSliceBudgetReadback
open NativeAnisotropicSliceLabels NativeReferenceColumnExponents NativeActivePhasePopulation
open NativeOriginalPacketReference NativeQueriedVertexWeights
open NativeConfiguredThirdRelation
open NativePaidThirdBudget
open NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu NativeIncidentAffineAnchorSource
open NativePaidMeshAngularUpper NativeFixedCompactKakeyaExponent CanonicalConfiguredE4Bridge
open scoped BigOperators Matrix.Norms.Elementwise

open NativePostGraphXYHookStage NativeRankTwoXYStageReadback NativeRankRadiusMenu SelfUniform
theorem from_xy_stage {n g L L2 dOld dExtra Jhorizontal L3 : ℕ}
    {D : FiniteScaleSource n} {eta zeta seed tau e eta0 c c2 r epsilonGraph : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau)
    (ref : Reference h tau htau seed e zeta L g)
    (Kcoh Ksupport Kupper Khalf : ℕ) (loss seedCap deltaUpper : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (Hupper : HasUpperEngine Kupper (c^3/8) loss seedCap deltaUpper)
    (Hcaller1 : HasCallerUniformities ref (factory g Kupper))
    (heta : 0 ≤ eta) (hzeta : 0 ≤ zeta) (hetaSeed : eta ≤ seed/8)
    (hzseed : zeta ≤ seed/256) (hseedCap : seed ≤ seedCap) (hUpperSmall : D.thickness ≤ deltaUpper)
    (he0 : 0 < eta0) (hcUnit : c ≤ 1/(eta0+1))
    (hr : 0 < r) (hr1 : r ≤ 1) (hrdelta : r ≤ D.thickness^(cutoff c (1:Fin 4)))
    (htauHalf : tau ≤ 1/2) (hTau : tau ≤ commonBudget eta0 c/1024)
    (hTauHistory : tau ≤ commonBudget eta0 c/(1000*(((2*Khalf:ℕ):ℝ)+1)))
    (hseed : seed ≤ tau/16384) (hc2 : c2=commonBudget eta0 c/4)
    (hg : 0 < g) (hgrid : 1/(g:ℝ) < rankWindow tau/4)
    (j : Fin (g+1)) (hstop18 : 18 ≤ (ref.schedule j).val)
    (hstopCap : (ref.schedule j).val ≤ ref.level/4)
    (hidentity : 48*((2^(ref.schedule j).val:ℕ):ℝ)*r=1)
    (hdelta : 64*D.thickness ≤ r^2)
    (hExtraSmall : D.thickness ≤ NativeHistoryDimensionRange.extraCutoff c hc hc1 g)
    (heGraph : 0 < epsilonGraph) (heGraphHalf : epsilonGraph ≤ 1/2)
    (heSmall : eta0 ≤ epsilonGraph) (hcSmall : c ≤ epsilonGraph/24)
    (hKhalf : 0 < Khalf)
    (hError : D.thickness^(cutoff c (1:Fin 4)*epsilonGraph/2) ≤ 1/errorConstant)
    (epsilonPaid deltaBudget : ℝ)
    (Hbudget : HasBudget epsilonPaid eta0 c g Khalf (dExtra+3) Jhorizontal L3 deltaBudget)
    (hBudgetSmall : D.thickness ≤ deltaBudget)
    (hradius : r=radius (rankWindow tau) (rankWindow_pos htau).le g ref.level j)
    (F : Finset (Fin n × Index)) (hFref : F⊆ref.E1)
    (oldPlane : Index → Submodule ℝ E4)
    (hNearF : ∀z∈F,Metric.infDist (slopeVector D z.1) (oldPlane z.2:Set E4) ≤ r)
    (selected : Fin (2*Khalf))
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
        Jhorizontal (dExtra+3) L3 (ref.schedule j).val Khalf tuple r epsilonGraph ∧
    let W : ℝ := (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)
    let population := (lambda*W/(2*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ)))*D.thickness^eta
    let retain := population/rowConstant
    let PL := profileLower D.thickness population
      (columnEpsilon D.thickness lambda (seed/8) c2)
      tau (seed/8) (min (NativeAllTwoScaleConfiguration.boundaryWindow tau) ((tau/16)/1000))
    let PU := profileUpper D.thickness (columnEpsilon D.thickness lambda (seed/8) c2) tau
    let plane := nodePlane D tuple
    let threshold := (((cutEdges E2 points).card:ℝ)/
      (2*((((cutEdges E2 points).image (mixedLabel D ref.a m plane 2)).card):ℝ)))
    ∀u R0 : ℕ,0 < R0 → rho m ≤ mu m*(R0:ℝ) → mu m*(R0:ℝ)=(2:ℝ)⁻¹^u →
    ∀depths : Fin Kcoh → ℕ,
      (∀k,6 ≤ depths k ∧ depths k ≤ m+6) →
      (∀k,(5/4:ℝ)*(rho m)^(1-2*epsilonGraph) ≤ 64/((2^(depths k):ℕ):ℝ)) →
    ∀supportDepths : Fin Ksupport → ℕ,(∀k,supportDepths k ≤ u+6) →
    ∀extras : Parent → Finset (Fin n × Index) → (P : Submodule ℝ E4) → (hP : P≤heightKernel) → (hd : Module.finrank ℝ P=1) →
      (ℤ → Matrix (Fin 2) (Fin 1) ℝ) → (ℤ → Matrix (Fin 2) (Fin 1) ℝ) →
      Finset (Fin n × Index) → Fin dExtra → (Fin n × Index) → (Fin n × Index) → Prop,
    (∀p Hgraph P hP hd f Fcfg U k x,extras p Hgraph P hP hd f Fcfg U k x x) →
    (∀p Hgraph P hP hd f Fcfg U k x y,extras p Hgraph P hP hd f Fcfg U k x y → extras p Hgraph P hP hd f Fcfg U k y x) →
    ∃p : Parent,∃Hp Hgraph : Finset (Fin n × Index),
      population*(NativeLocalParentSource.parentLabels D ref.R ref.a (2^m) p).card ≤ D.thickness*Hp.card ∧
      Hp.card ≤ selectionCost Khalf*Hgraph.card ∧
    ∃(P0 : Submodule ℝ E4) (hP0 : P0≤heightKernel) (hd : Module.finrank ℝ P0=1)
      (f : ℤ → Matrix (Fin 2) (Fin 1) ℝ),
      (∀height,‖f height‖≤(1/4:ℝ)) ∧
      let Sq := NativeWeightedGrainQuotientGeometry.retained D ref.a m 2 plane Hgraph P0 hP0
        (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
      let F := fixedField D ref.a m 2 plane Sq f
      let Gcoh := NativeActualNewCutBudget.coherenceCharge Kcoh 2 g meshAngularConstant rowConstant
        r loss (rankLoss eta0 c (1:Fin 4)) (r^(-2*epsilonGraph)) extremalExponent
        (fun k => 64/((2^(depths k):ℕ):ℝ))
      let Ctotal := (quotientCost q*(Gcoh:ℝ))*
        ((((8*R0)*53^(4*Ksupport))*8^4:ℕ):ℝ)
      ∃xi : Index → EuclideanSpace ℝ (Fin 2),
      ∃Spre U T : Finset (Fin n × Index),∃Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ,
      Spre.Nonempty ∧ U.Nonempty ∧ T.Nonempty ∧ T⊆U ∧ U⊆Spre ∧ Spre⊆Hgraph ∧ Hgraph⊆ref.E1 ∧
      (Hgraph.card:ℝ) ≤ Ctotal*U.card ∧ 0 < Ctotal ∧
      Ctotal=quotientCost q*(NativeActualNewCutBudget.newCutCharge Kcoh Ksupport 2 g R0
        meshAngularConstant rowConstant r loss (rankLoss eta0 c (1:Fin 4))
        (r^(-2*epsilonGraph)) extremalExponent (fun k => 64/((2^(depths k):ℕ):ℝ)):ℝ) ∧
      (∀height,‖Fcfg height‖≤(1/4:ℝ)) ∧
      let Q3 := NativeSourceSizeBounds.radix U.card L3
      let F3 := refinementCost ((dExtra+3)+2) (Jhorizontal+1) L3
      let CX := (Ctotal/quotientCost q)*fiberCoefficient D.thickness eta zeta tau (seed/8) c2
        lambda (W/(E2.card:ℝ)) F1 G Q2 F3 Q3 q 2
      1 ≤ F3 ∧ 1 ≤ Q3 ∧
      (F3:ℝ)*(Q3:ℝ)^4 ≤ D.thickness^(-(commonBudget eta0 c/4)) ∧
      HasThirdXYSourceData (J:=Jhorizontal) (ell:=2) D zeta ref.a m plane E2 Hgraph U T P0 hP0
        (by norm_num) (by norm_num) hd f p population PL PU Q2 retain (selectionCost Khalf)
        Ctotal threshold L3
        (completeRelations D ref.a m p .oneTwo P0 hP0 hd F Fcfg R0 u (extras p Hgraph P0 hP0 hd f Fcfg U)) CX ∧
      (∀z∈U,parentLabel D ref.a (2^m) z.1=p) ∧
      (∀z∈T,parentLabel D ref.a (2^m) z.1=p) ∧
      (∀z∈T,Fcfg (translatedHeight D ref.a m z.2/((8*R0:ℕ):ℤ))=F (translatedHeight D ref.a m z.2)) ∧
      (∀z∈T,∀w∈T,translatedHeight D ref.a m z.2/((8*R0:ℕ):ℤ)=
        translatedHeight D ref.a m w.2/((8*R0:ℕ):ℤ) → translatedHeight D ref.a m z.2=translatedHeight D ref.a m w.2) ∧
      (∀x∈T.image (fun z => NativeActualConfiguredPoint.point D ref.a m p .oneTwo P0 hP0 hd F Fcfg R0 z.2),
       ∀y∈T.image (fun z => NativeActualConfiguredPoint.point D ref.a m p .oneTwo P0 hP0 hd F Fcfg R0 z.2),
       x≠y → (mu m*(R0:ℝ))/64≤dist x y) ∧
      ∀k z w,z∈T → w∈T →
        physicalCell D ref.a (2^m) (2^(depths k)) p z.2=physicalCell D ref.a (2^m) (2^(depths k)) p w.2 →
        ‖f (rawHeight D m z.2)-f (rawHeight D m w.2)‖<64/((2^(depths k):ℕ):ℝ) ∧
        ‖xi z.2-xi w.2‖≤(129/4:ℝ)*(64/((2^(depths k):ℕ):ℝ)) := by
  subst r
  intro m r lambda F1 G F2 Q2
  obtain ⟨q,hq,hq1,hqRaw,E2,hE2F,h21,hE2n,hG,hGF,hQ2,H2,Hcaller2,Hpoint,
    points,S0,hPoints,hS0,hMass,point,tuple,anchor,Hsys,hOld,hNear,Lgrain,Hprofiles⟩ :=
    NativeRankTwoXYStageReadback.extract h htau ref F hFref oldPlane j hNearF
      selected hKhalf hmid RelOld Hstage
  refine ⟨q,hq,hq1,hqRaw,E2,hE2F,h21,hE2n,hG,hGF,hQ2,H2,Hcaller2,Hpoint,
    points,S0,hPoints,hS0,hMass,point,tuple,anchor,Hsys,hOld,hNear,Lgrain,Hprofiles,?_⟩
  intro W population retain PL PU plane threshold u R0 hR0 hbase hbaseEq
    depths hdepths hErrorWindow supportDepths hSupport extras hExtraRefl hExtraSymm
  exact NativeActualCoherentHeightCoreFull.from_parent_profiles h htau ref rfl
    Kcoh Ksupport Kupper Khalf loss seedCap deltaUpper hc hc1 Hupper Hcaller1
    heta hzeta hetaSeed hzseed hseedCap hUpperSmall he0 hcUnit hr hr1 hrdelta
    htauHalf hTau hTauHistory hseed hc2 hg hgrid j hstop18 hstopCap hidentity hdelta
    hExtraSmall heGraph heGraphHalf heSmall hcSmall hKhalf hq hq1 hqRaw hError
    E2 h21 hE2n F2 G Q2 Lgrain hG hGF H2 epsilonPaid deltaBudget Hbudget hBudgetSmall
    points S0 hPoints hMass point tuple anchor oldPlane hOld hNear
    Hsys RelOld Hcaller2 Hprofiles u R0 hR0 hbase hbaseEq depths hdepths hErrorWindow
    supportDepths hSupport extras hExtraRefl hExtraSymm

end NativeActualXYStageHeightJoinFull
end -- original anonymous section NativeActualXYStageHeightJoinFull
