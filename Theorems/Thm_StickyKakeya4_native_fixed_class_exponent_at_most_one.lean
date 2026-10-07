import Theorems.Thm_StickyKakeya4_native_saturated_reference_graph_configuration
import Theorems.Thm_StickyKakeya4_native_saturated_source_angular_rank_lower
import Theorems.Thm_StickyKakeya4_native_scheduled_angular_ancestor
import Theorems.Thm_StickyKakeya4_native_angular_test_source_window
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_source_angular_cap
import Theorems.Thm_StickyKakeya4_native_angular_rank_contradiction

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 24576
set_option maxHeartbeats 18000000
noncomputable section
namespace NativeFixedClassExponentAtMostOne
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeFixedCompactKakeyaExponent NativeJointUniformCoarseRelations NativeJointQuantitativeMenu
open NativeBalancedConfiguration NativeFixedSizeScaleMenu NativeLocalMenuInterpolation
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeConditionedPairMenu
open NativeAllTwoScaleConfiguration NativeDirectionRankDichotomy NativeIncidentRankSelection
open NativeRankRadiusMenu NativeRankExponentHierarchy NativeLocalPairUniformCore NativeLocalPairFibers
open NativeSecondRefinementCost NativeActualMesoscopicRankConfiguration NativeRetainedQueryMenu
open NativeSquaredGrainQueries NativeActualQueryRankConfiguration NativeCompatibleWeightedRetention
open NativeActualAngularMenuCost NativeSourceSizeBounds NativeQueriedVertexWeights
open NativeActualGrainHistory NativeOriginalPacketReference NativeCompatibleNodeDirections
open NativeRetainedGrainHistory NativeActualHistoryConfiguration
open RichDirectionalLayers WeightedRichDirectionalLayers NativeSpatialAngularGeometry
open NativeCompatibleAngularCandidates NativeGeneralRankScalarBudget NativeOriginalAngularTupleMenu
open NativeSaturatedParentGraphConfiguration NativeSaturatedParentGraphData
open NativeSaturatedReferenceGraphConfiguration NativeSaturatedSourceAngularRankLower
open NativeScheduledAngularAncestor NativeAngularTestSourceWindow NativeAngularRankContradiction
open NativeMiddleGrainParentBudget NativeSmallLossParentBudget NativeOriginalPointSaturation
open NativeParentHeightAlignment NativeHorizontalGrainSlice NativeProjectorCellChart
open NativeParentGrainIncidenceCleanup
open NativeActualHeightSlopeVariation NativeHorizontalGraphCoordinates NativeHeightSlopeCoordinates
open NativeReferenceXYGridSourceAngularCap NativeOriginalPointAngularLower NativeActivePhasePopulation
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

/-- The actual fixed compact native critical exponent is at most one.
The source, whole-point graph, angular lower, affine cap and scale cutoffs
are all constructed internally on the same original incidence backbone. -/
theorem extremalExponent_le_one : extremalExponent≤ 1 := by
  by_contra hnot
  have hk : 1< extremalExponent := lt_of_not_ge hnot
  have hk0 : 0< extremalExponent := lt_trans zero_lt_one hk
  let epsilon : ℝ := min ((extremalExponent-1)/1000) (1/9)
  have he : 0< epsilon := lt_min (by positivity) (by norm_num)
  have he9 : epsilon≤ 1/9 := min_le_right _ _
  have heHalf : epsilon≤ 1/2 := he9.trans (by norm_num)
  have heGap : epsilon≤ (extremalExponent-1)/108 := by
    have hh : epsilon≤ (extremalExponent-1)/1000 := min_le_left _ _
    linarith only [hh,hk]
  obtain ⟨Khalf,hHalf,_hKmin,_hgrain,eta0,he0,_heK,heeps,_he1000,
    c,hc,hc1,_hc8,hcUnit,_hcGap,hceps,_hc64,
    tau,htau,seed,e,zeta,L,g,L2,c2,htauB,htauT,htauHalf,hseed,hseedTau,
    _heAux,_hzeta,_hzseed,_hL,hg,hgrid,_hL2,hc2,
    deltaRet,_hdRet,_hdRet1,_hdRetH,_hdRetH1,_hdRange,_hdRet8,_hMetric,Hsource⟩ :=
    exists_saturated_reference_graph_configuration 0 1 0 1 (by omega) hk0 epsilon he
  let J := 2*Khalf
  obtain ⟨dScale,hdScale,_hdScale8,HScale⟩ := exists_original_test_cutoff c epsilon hc hc1 he he9
  obtain ⟨dError,hdError,_hdError8,HError⟩ := exists_uniform_small_loss_cutoff c epsilon hc hc1 he
  let A : ℝ := 2744*rowConstant*((g:ℝ)+1)
  have hRow := rowConstant_pos
  have hA : 0≤ A := by dsimp [A]; positivity
  have hB : 0≤ angularCapConstant := by norm_num [angularCapConstant]
  obtain ⟨dContra,hdContra,_hdContra1,HContra⟩ := exists_original_scale_cutoff hk
    (show (0:ℝ)< c^3/8 by positivity) (show 0≤ 160*A*angularCapConstant by positivity)
  obtain ⟨eta,n,D,h,heta,_hetaBound,hetaSeed,_hSmall,hExtra,_hRet,_hCompact,_hVolume,_hNear,
    a,level,R,original,E1,schedule,Hbackbone,hgl,hSchedule,hCore,H1,
    _hPoint1,hOld,_hConditioned,_hScales,HMiddle,_hAllPairs,_hE1Near,
    rank,j,hrank,_hrank23,hrange,hjmenu,hrcut,_hrlo,hrhi,hidentity,_hscale,_hrsquare,
    F,hFE1,_hFn,_hRankMass,P,hnearP,_hOldNear,hstopK,_hSelect,selected,hmid,Hparents⟩ :=
    Hsource 1 (1/8) (min dScale (min dError dContra)) (by norm_num) (by norm_num)
      (lt_min hdScale (lt_min hdError hdContra))
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
  let stop := (schedule j).val
  let m := historyDepth J stop selected
  have hmMid : m=middleDepth stop := hmid
  have hd := h.1.2.1
  have hr : 0< r := radius_pos _ _ _ _ _
  have hr1 : r≤ 1 := hrhi.trans (by norm_num)
  have hstop6 : 6≤ stop := by omega
  have hstopCap : stop≤ level/4 := stopping_depth_cap htau g level schedule hSchedule j hjmenu
  have hrank2 : rank.val+1=2 := by
    rcases _hrank23 with h2 | h3
    · exact h2
    · rw [h3] at hrange
      norm_num only [Nat.cast_ofNat] at hrange
      linarith only [hk,hrange]
  have hrank3 : rank.val+1≤ 3 := by omega
  have hk2 : extremalExponent≤ 2 := by
    rw [hrank2] at hrange
    norm_num only [Nat.cast_ofNat] at hrange
    linarith only [hrange]
  have hm6 : 6≤ m := by rw [hmMid]; exact (middle_depth_bounds stop hstop6).1
  let depths : Fin 1 → ℕ := fun _ => m
  let scales : Fin 0 → ℕ := Fin.elim0
  let Rel : Fin 0 → (Fin n × Index) → (Fin n × Index) → Prop := fun i => Fin.elim0 i
  have Hstage := Hparents depths (fun _ => ⟨le_rfl,by change m≤phaseDepth m; dsimp only [phaseDepth]; omega⟩)
    ⟨0,rfl⟩ scales Rel (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  let F1 := factor (menuSize (pairMenuSize (1+(g+1)) (g+1)) (g+1)) (g+1) L
  let Q1 := coreRadix original R L
  let d2 := ((NativeParentHorizontalQueryMenu.size ((0+1)+(0+0)) 1+
    ((J+1)+(J+1))+((J+1)+(J+1))+((J+1)+(J+1))+1)+(g+1)*(g+1))
  let G := retentionCost d2 1 L2
  let F2 := factor d2 1 L2
  let Q2 := NativeSourceSizeBounds.radix F.card L2
  obtain ⟨previous,_hprevious,test,_htest,_hrq,_hqr,hqlo,E2,hE2F,hE2ne,_hE2old,
    _hret2,_hret,_hnear2,hCaller,_hGrains,_hPoint2,_hRows,_hRich,H2,hPlane,_hTuples,
    _hFamily,Hfinal,_hQueries,_hParent,_hCounts⟩ := Hstage
  let q := radius (rankWindow tau) (rankWindow_pos htau).le g level test
  have hq : 0< q := radius_pos _ _ _ _ _
  have hq1 : q≤ 1 := (radius_le_one_div_48 _ _ _ _ _).trans (by norm_num)
  have h21 : E2⊆ E1 := hE2F.trans hFE1
  have hF1 : 0< F1 := original_factor_pos _ _ _
  have hG : 0< G := by dsimp [G,retentionCost]; positivity
  have hQ1 : 1≤ Q1 := (show 1≤ 4 by omega).trans (radix_four_le _ _)
  have hGF : G≤ F2 := retained_cost_le_factor d2 1 L2 (by omega)
  have hLocalPoint := (NativeParentReferenceRelationMenu.uniformities h R a m scales Rel E2 Q2 hCaller).2.1
  obtain ⟨C,_hC,S0,hS0,_hS,_hinj,_hmass,_hretain,_hcompat,_hwitness,_htrace,
    point,tuple,anchor,Hsys,_Hword,_Hsame,_Hhistory,_hHistRet,Hcleanup⟩ := Hfinal
  obtain ⟨Kpoints,hKF,_hKn,_hhalf,_htotal,hfinal,_hgrainCounts,_hdense,_HsysK,_hTrace,Hprofile⟩ := Hcleanup
  obtain ⟨_ht,_hmu,_hkeep,H,hHK,_hHn,_hhalfH,p,_hp,_hHpn,_hpop,href,_hgrain,_hmin,
    hsat,_hprofiles,_hcleaned,_hheightL,_hheightU,_hdescendant,_hplane,_hpaid,hell1,hell4,Hgraph⟩ := Hprofile
  obtain ⟨Nodes,_hNodes,u0,_hu0,hP0,hDim,f,B,hBN,_hBn,S,hSeq,hSH,hSn,hSB,_hcut,
    hSparent,_hAlign,_hResid,_hZero,_hNorm,hCell,hSlope,_hGraph,_hMetricGraph,_hFib⟩ := Hgraph
  have hHE2 : H⊆ E2 := hHK.trans (cutEdges_subset E2 Kpoints)
  have hHpE2p : parentEdges D a (2^m) H p⊆ parentEdges D a (2^m) E2 p := filter_subset_filter _ hHE2
  have hSE2 : S⊆ E2 := hSH.trans ((filter_subset _ _).trans hHE2)
  have HS : Saturated (parentEdges D a (2^m) E2 p) S Prod.snd := by
    rw [hSeq]
    exact nodeCut_saturation D m _ _ ⟨hHpE2p,hsat⟩ B
  have hK0 : Kpoints⊆ S0 := hKF.trans
    (history_antitone D E2 (historyDepth J stop) (rank.val+1)
      (fun i => natStageDirectionIndex h (tuple i)) S0 (Nat.zero_le J))
  have hSpoints : ∀z∈S,z.2∈S0 := by
    intro z hz
    exact hK0 (mem_filter.mp (hHK (mem_filter.mp (hSH hz)).1)).2
  have hSNodes : ∀k∈S.image Prod.snd,spatialLabel D (2^m) k∈Nodes := by
    intro k hkS
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hkS
    apply hBN
    rw [←hSB]
    exact mem_image_of_mem (fineNode D m) hz
  let P0 := NativeActualHeightSlopeVariation.horizontalPlane D (tuple selected) u0
  have hCell' : ∀k∈S.image Prod.snd,cell P0=cell
      (NativeActualHeightSlopeVariation.horizontalPlane D (tuple selected) (spatialLabel D (2^m) k)) :=
    fun k hkS => hCell _ (hSNodes k hkS)
  have hSlope' : ∀k∈S.image Prod.snd,f (spatialLabel D (2^m) k (3:Fin 4))=
      nodeSlope P0 hP0 (rank.val+1) (by omega) (by omega) hDim
        (NativeActualHeightSlopeVariation.horizontalPlane D (tuple selected) (spatialLabel D (2^m) k))
        (horizontalPlane_le D (tuple selected) (spatialLabel D (2^m) k)) :=
    fun k hkS => hSlope _ (hSNodes k hkS)
  have hTauCut := tau_le_cutoff he0.le hc hc1 hcUnit rank hrank htau.le J htauB
  have hdScale' : D.thickness≤ dScale := hExtra.le.trans (min_le_left _ _)
  have hdError' : D.thickness≤ dError := hExtra.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdContra' : D.thickness≤ dContra := hExtra.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨s,hs6,hsm,hfine,hlo,hhi,hErrorScale,hRho⟩ := HScale D.thickness r tau hd hdScale' hr hr1
    rank hrcut htau htauHalf hTauCut level stop Hbackbone.2.1 hstop6 hstopCap hidentity
  rw [←hmMid] at hsm hfine hlo hhi hErrorScale
  have hs3 : 3≤ s := by omega
  have hmLevel : m≤ level := by omega
  obtain ⟨hgap0,hgapTau,jA,hAncestor,hGap,HAncestor⟩ := exists_actual_angular_ancestor D E1 a tau htau
    g level (m+s-3) Q1 hg hgl hgrid schedule hSchedule hOld hlo hhi
  obtain ⟨z,hz⟩ := hSn
  have hkS : z.2∈S.image Prod.snd := mem_image_of_mem _ hz
  have hReferenceRet :
      let lambda := r^(rankLoss eta0 c rank)/(4*((g:ℝ)+1))
      let W : ℝ := (WeightedRichDirectionalLayers.mass Kpoints (pointWeight E2):ℝ)
      let mu := (lambda*W/(2*(F1:ℝ)*G*(E2.card:ℝ)))*D.thickness^eta
      (mu/rowConstant)*(parentEdges D a (2^m) E1 p).card≤ (parentEdges D a (2^m) E2 p).card :=
    (href E1 hCore.1).trans (by exact_mod_cast card_le_card hHpE2p)
  have hLower := actual_saturated_angular_rank_lower h original R level Hbackbone E1 E2 S Kpoints
    hCore.1 h21 hE2ne rank (rank.val+1) hrank3 heta.le he0 hc hr hr1 hrcut hfinal
    htau htauT hseedTau hc2 hgap0 hgapTau g F1 F2 G Q1 Q2 hg hgl hF1 hG hQ1 hGF hgrid H1 H2 HMiddle
    m s (schedule jA).val hmLevel hs3 hfine hAncestor hGap p HS HAncestor (hLocalPoint p) hReferenceRet z.2 hkS
  have hmGrain : m=grainDepth (2*Khalf) stop (middleIndex Khalf) :=
    hmMid.trans (grainDepth_middle Khalf stop hHalf hstop6).symm
  have hUpper := actual_point_angular_cap h hr hr1 he heHalf he0.le heeps hc hc1 hceps rank hrank3
    hrcut htau.le g Khalf stop m hHalf hstop6 hmGrain htauB hgrid hq hq1 hqlo hidentity
    (HError D.thickness hd hdError' rank) E2 S hSE2 S0 hSpoints (point selected) (tuple selected) (anchor selected)
    (Hsys selected) P (fun k hkP => hPlane k (hS0 hkP)) (fun y hy => hnearP y (hE2F hy))
    p hSparent P0 hP0 hDim hCell' f hSlope' s hs3 hErrorScale z.2 hkS
  have hLoss : rankLoss eta0 c rank≤ (extremalExponent-1)/108 :=
    (rankLoss_le_initial he0.le hc.le hc1 rank).trans (heeps.trans heGap)
  have hContraSmall := HContra D.thickness r (cutoff c rank) hd hdContra' hr
    (cutoff_bounds hc hc1 rank).2.2 hrcut
  have hrho : (0:ℝ)< 64/((2^s:ℕ):ℝ) := by positivity
  have hRankVal : rank.val=1 := by omega
  rw [hRankVal] at hUpper
  norm_num only [Nat.cast_one] at hUpper
  apply incompatible_rank_two_counts hk hk2 hrho hr hr1 hA hB hLoss hRho ?_ hUpper hContraSmall
  simpa only [A,neg_mul] using hLower

end NativeFixedClassExponentAtMostOne
