import Theorems.Thm_StickyKakeya4_native_actual_reference_one_T
import Theorems.Thm_StickyKakeya4_native_actual_reference_frontend
import Theorems.Thm_StickyKakeya4_native_actual_paid_planar_alignment

/- The same constructed third core supplies the paid planar witnesses.
Originally drafted without verification; consult current receipts. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeActualRankTwoPlanarStage
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
open NativeActualPaidPlanarAlignment
open NativeFinalSourceScopeReadback NativeActualThirdHistoryReadback
open NativeRetainedGrainHistory NativeLocalPairUniformCore NativeGrainHeightProjectionSource
open NativeGrainQuotientFibers NativeSharpXPowerAlgebra NativeParentHeightAlignment NativeCubicalIncidenceCounts

/-- The analytic exponent and gap precede every source choice. On a genuine
rank-two stage this constructs the unique final third core and then invokes
Lemma 5.3 on its actual quotient slices; no baseline graph mass is assumed. -/
theorem exists_stage_supplier (zeta53 : ℝ) (hzeta53 : 0 < zeta53) :
    ∃eta53Threshold chi : ℝ,0 < eta53Threshold ∧ 0 < chi ∧
    ∀eta53 : ℝ,0 < eta53 → eta53 ≤ eta53Threshold →
    ∀Kcoh Ksupport g Khalf : ℕ,
    ∃epsCut : ℝ,0 < epsCut ∧ epsCut ≤ 1 ∧
    ∀ {n L L2 dOld dExtra Jhorizontal L3 : ℕ}
    {D : FiniteScaleSource n} {eta zeta seed tau e eta0 c c2 r epsilonGraph : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau)
    (ref : Reference h tau htau seed e zeta L g)
    (Kupper : ℕ) (loss seedCap deltaUpper : ℝ)
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
    (heGraphQuarter : epsilonGraph ≤ 1/4) (hLoss : 0 ≤ loss)
    (hk : extremalExponent ≤ 2)
    (heSmall : eta0 ≤ epsilonGraph) (hcSmall : c ≤ epsilonGraph/24)
    (hKhalf : 0 < Khalf)
    (hError : D.thickness^(cutoff c (1:Fin 4)*epsilonGraph/2) ≤ 1/errorConstant)
    (epsilonPaid deltaBudget : ℝ) (hePaid : 0 < epsilonPaid)
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
      (NativeParentOriginalPointMenu.relations D ref.a (middleDepth (ref.schedule j).val) RelOld))
    (hNu : NativeActualNewCutBudget.newExponent Kcoh epsilonGraph loss (rankLoss eta0 c (1:Fin 4)) ≤ 1/2)
    (hMargin : 16*NativeActualNewCutBudget.newExponent Kcoh epsilonGraph loss (rankLoss eta0 c (1:Fin 4))+
      4*epsilonPaid ≤ eta53/2),
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
    6 ≤ u → u+6 ≤ m →
    ((8*R0:ℕ):ℝ) ≤ 1280*(mu m)^(-2*epsilonGraph) →
    64/((2^(u+12):ℕ):ℝ) ≤ epsCut →
    64*(64/((2^(u+12):ℕ):ℝ)) ≤
      2*max ((5/4:ℝ)*(rho m)^(1-2*epsilonGraph)) (rho m) →
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
      (∀k z w,z∈T → w∈T →
        physicalCell D ref.a (2^m) (2^(depths k)) p z.2=physicalCell D ref.a (2^m) (2^(depths k)) p w.2 →
        ‖f (rawHeight D m z.2)-f (rawHeight D m w.2)‖<64/((2^(depths k):ℕ):ℝ) ∧
        ‖xi z.2-xi w.2‖≤(129/4:ℝ)*(64/((2^(depths k):ℕ):ℝ))) ∧
      Nonempty (∀height : {height : ℤ // height∈
        ((T.image (fun z => coarseYKey D ref.a m p .oneTwo P0 hP0 hd F Fcfg R0 z.2)).image Prod.fst)},
        NativeLiteralYHeightAlignment.HeightAlignment
          (T.image (fun z => coarseYKey D ref.a m p .oneTwo P0 hP0 hd F Fcfg R0 z.2))
          u (2-extremalExponent) zeta53 chi height.val) := by
  trace "planar-stage: analytic supplier"
  obtain ⟨etaThreshold,chi,hThreshold,hchi,Hplanar⟩ := exists_paid_alignment zeta53 hzeta53
  refine ⟨etaThreshold,chi,hThreshold,hchi,?_⟩
  intro eta53 he53 he53Top Kcoh Ksupport g Khalf
  have hMesh : (0:ℝ) ≤ meshAngularConstant := by unfold meshAngularConstant NativeSameSourceConditionalAngularUpper.conditionalConstant; positivity
  have hRow : (0:ℝ) ≤ rowConstant := by unfold rowConstant NativeOriginalPrunedMass.volumeConstant; positivity
  obtain ⟨epsCut,hCut,hCut1,Hpaid⟩ := Hplanar eta53 he53 he53Top Kcoh Ksupport g
    meshAngularConstant rowConstant hMesh hRow
  refine ⟨epsCut,hCut,hCut1,?_⟩
  intro n L L2 dOld dExtra Jhorizontal L3 D eta zeta seed tau e eta0 c c2 r epsilonGraph
    h htau ref Kupper loss seedCap deltaUpper hc hc1 Hupper Hcaller1
    heta hzeta hetaSeed hzseed hseedCap hUpperSmall he0 hcUnit hr hr1 hrdelta
    htauHalf hTau hTauHistory hseed hc2 hg hgrid j hstop18 hstopCap hidentity hdelta
    hExtraSmall heGraph heGraphHalf heGraphQuarter hLoss hk heSmall hcSmall hKhalf hError
    epsilonPaid deltaBudget hePaid Hbudget hBudgetSmall hradius F hFref oldPlane hNearF
    selected hmid RelOld Hstage hNu hMargin
  trace "planar-stage: source arguments introduced"
  subst r
  trace "planar-stage: radius normalized"
  intro m r lambda F1 G F2 Q2
  obtain ⟨q,hq,hq1,hqRaw,E2,hE2F,h21,hE2n,hG,hGF,hQ2,H2,Hcaller2,Hpoint,
    points,S0,hPoints,hS0,hMass,point,tuple,anchor,Hsys,hOld,hNear,Lgrain,Hprofiles,Hrun⟩ :=
    NativeActualXYStageHeightJoinFull.from_xy_stage h htau ref Kcoh Ksupport Kupper Khalf
      loss seedCap deltaUpper hc hc1 Hupper Hcaller1 heta hzeta hetaSeed hzseed
      hseedCap hUpperSmall he0 hcUnit hr hr1 hrdelta htauHalf hTau hTauHistory hseed hc2
      hg hgrid j hstop18 hstopCap hidentity hdelta hExtraSmall heGraph heGraphHalf
      heSmall hcSmall hKhalf hError epsilonPaid deltaBudget Hbudget hBudgetSmall rfl
      F hFref oldPlane hNearF selected hmid RelOld Hstage
  trace "planar-stage: one-T stage unpacked"
  refine ⟨q,hq,hq1,hqRaw,E2,hE2F,h21,hE2n,hG,hGF,hQ2,H2,Hcaller2,Hpoint,
    points,S0,hPoints,hS0,hMass,point,tuple,anchor,Hsys,hOld,hNear,Lgrain,Hprofiles,?_⟩
  intro W population retain PL PU plane threshold u R0 hR0 hbase hbaseEq hu6 hum
    hHeight hSmall hShape depths hdepths hErrorWindow supportDepths hSupport
    extras hExtraRefl hExtraSymm
  trace "planar-stage: base and menu arguments introduced"
  obtain ⟨p,Hp,Hgraph,hPopulation,hGraphRet,P0,hP0,hd,f,hfNorm,xi,Spre,U,T,Fcfg,
    hSpre,hUn,hTn,hTU,hUS,hSH,hHRef,hRet,hCtotal,hCost,hCfg,
    hF3,hQ3,H3,HT,hUp,hTp,hFreeze,Hsingle,hSeparator,Hcoherence⟩ :=
    Hrun u R0 hR0 hbase hbaseEq depths hdepths hErrorWindow supportDepths hSupport
      extras hExtraRefl hExtraSymm
  trace "planar-stage: actual T unpacked"
  refine ⟨p,Hp,Hgraph,hPopulation,hGraphRet,P0,hP0,hd,f,hfNorm,xi,Spre,U,T,Fcfg,
    hSpre,hUn,hTn,hTU,hUS,hSH,hHRef,hRet,hCtotal,hCost,hCfg,
    hF3,hQ3,H3,HT,hUp,hTp,hFreeze,Hsingle,hSeparator,Hcoherence,?_⟩
  let Sq := NativeWeightedGrainQuotientGeometry.retained D ref.a m 2 plane Hgraph P0 hP0
    (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
  let field := fixedField D ref.a m 2 plane Sq f
  let Ctotal := (quotientCost q*(NativeActualNewCutBudget.coherenceCharge Kcoh 2 g
    meshAngularConstant rowConstant r loss (rankLoss eta0 c (1:Fin 4))
    (r^(-2*epsilonGraph)) extremalExponent (fun k => 64/((2^(depths k):ℕ):ℝ)):ℝ))*
      ((((8*R0)*53^(4*Ksupport))*8^4:ℕ):ℝ)
  have hUOld : U⊆incidences ref.original :=
    hUS.trans (hSH.trans (hHRef.trans (original_scope ref).1))
  have hFirst : 0 < F1 := NativeGenericReferenceData.factor_pos ref
  have hQ1 : 1 ≤ coreRadix ref.original ref.R L :=
    (by norm_num : 1 ≤ (4:ℕ)).trans (NativeSourceSizeBounds.radix_four_le _ _)
  have hMassRatio := fraction_lower E2 hE2n r (rankLoss eta0 c (1:Fin 4)) W hMass
  trace "planar-stage: normalize actual source record"
  have HTbudget := source_record D eta zeta ref.a m plane E2 Hgraph U T P0 hP0 hd f p
    lambda W tau seed c2 q Ctotal threshold F1 G Q2 Khalf L3
    (completeRelations D ref.a m p .oneTwo P0 hP0 hd field Fcfg R0 u
      (extras p Hgraph P0 hP0 hd f Fcfg U)) HT
  have hGuards := middle_guards (ref.schedule j).val ref.level D.thickness r
    (by omega) hstopCap h.1.2.1 hr hr1 hdelta hidentity
  have hRank : 0 ≤ rankLoss eta0 c (1:Fin 4) := (rankLoss_pos he0 hc _).le
  have hm12 : 12 ≤ m := by omega
  have hMassRatio' : r^((2*((2:ℕ):ℝ)+1)*rankLoss eta0 c (1:Fin 4)) ≤ W/(E2.card:ℝ) := by
    simpa only [Nat.cast_ofNat,show (2:ℝ)*2+1=5 by norm_num] using hMassRatio
  trace "planar-stage: invoke paid planar supplier"
  exact Hpaid Hbudget hePaid h hBudgetSmall heta ref.original ref.backbone.1 U hUOld hUn
    F1 F2 G (coreRadix ref.original ref.R L) Q2 m hFirst hG hQ1 hQ2 hGF hm12
    zeta lambda (W/(E2.card:ℝ)) tau seed c2 r q hetaSeed htau.le hTau hseed hzseed hc2
    ref.cost H2 hr hr1 hrdelta rfl hMassRatio' hq hq1 hgrid hqRaw hGuards.2.2.2
    Ctotal hCtotal ref.a plane E2 Hgraph T P0 hP0 hd f p threshold _ HTbudget
    ref.backbone.2.2.1 ref.level u R0 ref.backbone.2.1 hGuards.1 hUp hR0 hbaseEq hk
    loss (r^(-2*epsilonGraph)) epsilonGraph depths hLoss hRank (Real.rpow_nonneg hr.le _)
    heGraph.le heGraphQuarter le_rfl hGuards.2.2.1 hHeight hCost hSmall hShape hNu hMargin
    Fcfg (fun z hz => (hFreeze z hz).symm) Hsingle

end NativeActualRankTwoPlanarStage
