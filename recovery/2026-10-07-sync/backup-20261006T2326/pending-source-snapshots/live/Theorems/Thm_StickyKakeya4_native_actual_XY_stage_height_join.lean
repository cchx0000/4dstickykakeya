/- UNVERIFIED actual stage-to-one-T composition. No strict Lean check has run. -/
import Theorems.Thm_StickyKakeya4_native_actual_coherent_height_core
import Theorems.Thm_StickyKakeya4_native_rank_two_XY_stage_readback
/- UNVERIFIED same-E2/one-third-core composition. No strict Lean check has run. -/
import Theorems.Thm_StickyKakeya4_native_physical_coherent_third_join
import Theorems.Thm_StickyKakeya4_native_actual_height_third_join
import Theorems.Thm_StickyKakeya4_native_parent_original_point_menu
import Theorems.Thm_StickyKakeya4_native_configured_third_relation
import Theorems.Thm_StickyKakeya4_native_paid_third_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeActualXYStageHeightJoin
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
      HasThirdXYSourceData (J:=Jhorizontal) D zeta ref.a m plane E2 Hgraph U T P0 hP0
        (by norm_num) (by norm_num) hd f p population PL PU Q2 retain (selectionCost Khalf)
        Ctotal threshold L3
        (completeRelations D ref.a m p .oneTwo P0 hP0 hd F Fcfg R0 u (extras p Hgraph P0 hP0 hd f Fcfg U)) CX ∧
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
  exact NativeActualCoherentHeightCore.from_parent_profiles h htau ref rfl
    Kcoh Ksupport Kupper Khalf loss seedCap deltaUpper hc hc1 Hupper Hcaller1
    heta hzeta hetaSeed hzseed hseedCap hUpperSmall he0 hcUnit hr hr1 hrdelta
    htauHalf hTau hTauHistory hseed hc2 hg hgrid j hstop18 hstopCap hidentity hdelta
    hExtraSmall heGraph heGraphHalf heSmall hcSmall hKhalf hq hq1 hqRaw hError
    E2 h21 hE2n F2 G Q2 Lgrain hG hGF H2 epsilonPaid deltaBudget Hbudget hBudgetSmall
    points S0 hPoints hMass point tuple anchor oldPlane hOld hNear
    Hsys RelOld Hcaller2 Hprofiles u R0 hR0 hbase hbaseEq depths hdepths hErrorWindow
    supportDepths hSupport extras hExtraRefl hExtraSymm

end NativeActualXYStageHeightJoin
