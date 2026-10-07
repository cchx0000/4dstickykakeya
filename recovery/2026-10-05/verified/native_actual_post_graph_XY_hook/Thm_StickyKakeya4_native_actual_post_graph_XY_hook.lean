import Theorems.Thm_StickyKakeya4_native_post_graph_XY_hook_data
import Theorems.Thm_StickyKakeya4_native_post_graph_slice_data
import Theorems.Thm_StickyKakeya4_native_weighted_grain_quotient_cap
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeActualPostGraphXYHook
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeSquaredGrainQueries
open NativeAnisotropicSliceLabels NativeAnisotropicShortRowGeometry NativeReferenceSliceClassBounds
open NativeReferenceColumnExponents NativeRetainedSliceCore NativeSliceADConstant
open NativeParentGrainIncidenceCleanup NativeSpatialAngularGeometry NativeHorizontalGrainSlice
open NativeDirectionRankDichotomy NativeCompatibleNodeDirections NativeProjectorCellChart
open NativeWeightedGrainQuotientSource NativeWeightedGrainQuotientGeometry
open NativeTranslatedGrainHeightSelection NativeTranslatedGrainHeightOverlap
open NativeTranslatedGrainHeightMetric NativeTranslatedGrainHeightFibers NativeTranslatedGrainHeightChart
open NativeGrainQuotientFibers NativeParentLocalSliceGrainAD NativeHeightMetricMenu
open NativeFixedCompactKakeyaExponent FiniteVoronoiRealADCoarsening SelfUniform
open NativeMiddleWindowBalance NativeGrainHeightProjectionSource NativeReferenceSliceAllRadii
open scoped Matrix.Norms.Elementwise

open NativeHeightSlopeCoordinates NativeHorizontalGraphCoordinates NativeOriginalCellChartGeometry
open NativeSharpParentGraphData NativeReferenceSliceBudgetAlgebra NativeReferenceSliceBudgetReadback
open NativeParentHeightAlignment NativeParentHeightGraphCore NativeSharpMixedGrainCore
open NativeOriginalPacketReference NativeQueriedVertexWeights NativeParentVertexMassCap
open NativeActualProjectedGrainCount RichDirectionalLayers WeightedRichDirectionalLayers
open NativeSourceParentGrainCleanup NativeActivePhasePopulation NativePhaseHeightPopulation
open NativeCombinedParentProfiles NativeFullCoarseShadow NativeAllTwoScaleConfiguration

open NativePostGraphSliceData NativeTranslatedSliceGrainJoin NativeSharpParentGraphData
open NativeConditionedPairMenu NativeTwoScaleConfiguration NativeRetainedFinePairDensity

open NativePostGraphXYHookData NativeSourceThirdXYBundle NativeThirdXYSourceData NativeThirdXYData
open NativeSaturatedParentGraphData NativeReferenceXYGridField NativeRetainedSliceBudgetAlgebra
open NativeActualGrainHistory NativeHistoryGrainCount
theorem attach_actual_post_graph_XY {n d g level J Jhorizontal d3 : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed tau q r c2 epsilon : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1) (hE2 : E2.Nonempty) (L : ℕ)
    (schedule : Fin (g+1) → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (htau : 0 < tau) (heta : 0 ≤ eta) (hseed : seed ≤ tau/16384)
    (hg : 0 < g) (hgl : g ≤ level)
    (hgrid : 1/(g:ℝ) < min (boundaryWindow tau) ((tau/16)/1000)/4)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (hschedule : schedule=fullSchedule tau htau g level)
    (Hcore : IsCore D original R a eta zeta d (g+1) L Rel
      (fun j => 2^(schedule j).val) E1)
    (hcost : (125*175616*16384:ℝ)*(factor d (g+1) L:ℝ)*(coreRadix original R L:ℝ)^2*
      D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (hconditioned : ∀i j,HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
      HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val))
    (hreference : ∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E1 a level m f tau)
    (G : ℕ) (hG : 0 < G) (lambda : ℝ) (hlambda : 0 < lambda)
    (hret : lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card)
    (_hJ : 0 < J) (m : Fin J → ℕ) (hm6 : ∀i,6 ≤ m i) (ell : ℕ) (_hell : ell ≤ 4)
    (S0 : Finset Index) (hS0 : S0⊆E2.image Prod.snd) (Q2 : ℕ)
    (HU : ∀i,HasUniformFibers E2 Q2 (fun z => spatialLabel D (2^(phaseDepth (m i))) z.2))
    (hq : 0 < q) (hq1 : q ≤ 1)
    (point : Fin J → Index → Index)
    (tuple : Fin J → Index → Fin ell → (Fin n × Index))
    (anchor : Fin J → Index → Fin ell → Fin n)
    (Hsys : ∀i,IsNodeDirectionSystem D a (m i) E2 S0 q ell (point i) (tuple i) (anchor i))
    (Hhistory : HasGrainHistory D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 Q2 lambda (seed/8) c2)
    (i : Fin J) (hf : phaseDepth (m i) ≤ level) (hsmall : D.thickness ≤ 1/8)
    (HP : HasUniformFibers E2 Q2 (physicalPair h R a level (phaseDepth (m i))))
    (K : Finset Index)
    (hK : K⊆history D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 J)
    (hKn : K.Nonempty)

    (A : Index → Submodule ℝ E4) (hA : ∀k∈S0,Module.finrank ℝ (A k)=ell)
    (hnear : ∀z∈E2,Metric.infDist (slopeVector D z.1) (A z.2:Set E4) ≤ r)
    (hr : 0 < r) (hrD : r ≤ 64/((2^(m i):ℕ):ℝ))
    (hm12 : 12 ≤ m i) (hdimension : extremalExponent+(ell:ℝ) ≤ 4)
    (hJhorizontal : 0 < Jhorizontal) (L3 : ℕ) (hL3 : 0 < L3) (stop Khalf Lgrain : ℕ)
    (HParent : ∀p : Parent,
      HasUniformFibers (parentEdges D a (2^(m i)) E2 p) Q2 (fun z => slicePoint D a (m i) p z.2) ∧
      ∀j,HasUniformFibers (parentEdges D a (2^(m i)) E2 p) Q2
        (fun z => columnLabel D a (2^(m i)) p
          (64/((2^(NativeFixedHorizontalMenu.depths Jhorizontal (m i) j):ℕ):ℝ))
          (64/((2^(m i):ℕ):ℝ)) z.2))
    (H : HasSaturatedCurveParentProfiles h original R E1 E2 a level (m i) (nodePlane D (tuple i))
      K q ell Q2 (factor d (g+1) L) G Lgrain lambda zeta tau seed c2
      (NativeFixedHorizontalMenu.depths Jhorizontal (m i)) stop Khalf (tuple i) r epsilon) :
    HasXYParentProfiles h original R E1 E2 a level (m i) (nodePlane D (tuple i))
      K q ell Q2 (factor d (g+1) L) G Lgrain lambda zeta tau seed c2
      Jhorizontal d3 L3 stop Khalf (tuple i) r epsilon := by
  obtain ⟨ht,hmu,hretain,H,hHK,hHn,hhalf,p,hp,hHpn,hpop,href,hgrain,hmin,hsat,hprofiles,hcleaned,
    hheightL,hheightU,hdescendant,hplane,hpaid,hell,hell4,Hgraph⟩ := H
  obtain ⟨Nodes,hNodes,u0,hu0,hP0,hd,f,B,hBN,hBn,S,hSeq,hSH,hSn,hSB,hcut,
    hSparent,hAlign,hResid,hZero,hNorm,hCell,hSlope,hGraph,hMetric,hFib⟩ := Hgraph
  refine ⟨ht,hmu,hretain,H,hHK,hHn,hhalf,p,hp,hHpn,hpop,href,hgrain,hmin,hsat,hprofiles,hcleaned,
    hheightL,hheightU,hdescendant,hplane,hpaid,hell,hell4,
    Nodes,hNodes,u0,hu0,hP0,hd,f,B,hBN,hBn,S,hSeq,hSH,hSn,hSB,hcut,
    hSparent,hAlign,hResid,hZero,hNorm,hCell,hSlope,hGraph,hMetric,hFib,?_⟩
  intro Extra hExtraRefl hExtraSymm
  let plane := nodePlane D (tuple i)
  let P := sliceSpace (plane u0)
  let pop := (lambda*(WeightedRichDirectionalLayers.mass K (pointWeight E2):ℝ)/
    (2*(factor d (g+1) L:ℝ)*(G:ℝ)*(E2.card:ℝ)))*D.thickness^eta
  let keep := pop/rowConstant
  let eps := columnEpsilon D.thickness lambda (seed/8) c2
  let lower := profileLower D.thickness pop eps tau (seed/8)
    (min (boundaryWindow tau) ((tau/16)/1000))
  let upper := profileUpper D.thickness eps tau
  let t := ((cutEdges E2 K).card:ℝ)/(2*((((cutEdges E2 K).image
    (mixedLabel D a (m i) plane ell)).card):ℝ))
  have hdpos := h.1.2.1
  have hCgeom := NativeAnisotropicGlobalSourceBridge.comparisonCost_pos
  have hRow := rowConstant_pos
  have hLower : 0 < lower := by dsimp [lower,profileLower,eps,columnEpsilon]; positivity
  have hUpper : 0 < upper := by dsimp [upper,profileUpper,eps,columnEpsilon]; positivity
  have hHE2 : H⊆E2 := hHK.trans (cutEdges_subset E2 K)
  have hHp2 : parentEdges D a (2^(m i)) H p⊆parentEdges D a (2^(m i)) E2 p := filter_subset_filter _ hHE2
  have hSE : S⊆E2 := hSH.trans (hHp2.trans (filter_subset _ _))
  have hE2R : E2⊆retained original R := h21.trans Hcore.1
  have hpopE2 : pop*(R.filter (fun v => parentLabel D a (2^(m i)) v=p)).card ≤
      D.thickness*(parentEdges D a (2^(m i)) E2 p).card :=
    hpop.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hHp2)) hdpos.le)
  have hKS0 : K⊆S0 := hK.trans (Hhistory.2.2.1 J le_rfl).2.1
  have hSK : ∀z∈S,z.2∈S0 := by
    intro z hz
    exact hKS0 (mem_filter.mp (hHK (mem_filter.mp (hSH hz)).1)).2
  have hSchart : ∀z∈S,cell P=cell (sliceSpace (plane (spatialLabel D (2^(m i)) z.2))) := by
    intro z hz
    apply hCell
    exact hBN (hSB ▸ mem_image_of_mem (fineNode D (m i)) hz)
  have hSmetric : ∀x∈S,∀y∈S,
      ‖f (rawHeight D (m i) x.2)-f (rawHeight D (m i) y.2)‖ ≤ r^(-2*epsilon)*
      |chartHeightCoordinate (m i) 0 (rawHeight D (m i) x.2)-chartHeightCoordinate (m i) 0 (rawHeight D (m i) y.2)| := by
    intro x hx y hy
    have hxB : fineNode D (m i) x∈B := hSB ▸ mem_image_of_mem (fineNode D (m i)) hx
    have hyB : fineNode D (m i) y∈B := hSB ▸ mem_image_of_mem (fineNode D (m i)) hy
    exact ((hMetric _ hxB _ hyB).2 0).trans
      (mul_le_mul_of_nonneg_right hpaid (abs_nonneg _))
  have hCgraph : (0:ℝ)<selectionCost Khalf := by
    dsimp [selectionCost,NativeProjectorCellChart.chartCount]
    positivity
  have hSret : keep*((parentEdges D a (2^(m i)) E2 p).card:ℝ) ≤
      (selectionCost Khalf:ℝ)*S.card :=
    (href E2 hE2R).trans (by exact_mod_cast hcut)

  have hMixed : HasMixedIncidenceThreshold D a (m i) plane ell E2 K S := by
    intro x hx
    have heq := (hFib _ (mem_image_of_mem (mixedLabel D a (m i) plane ell) hx)).1
    have heq' : mixedFiber D a (m i) plane ell S (mixedLabel D a (m i) plane ell x)=
        mixedFiber D a (m i) plane ell (parentEdges D a (2^(m i)) H p) (mixedLabel D a (m i) plane ell x) := heq
    change _ ≤ ((mixedFiber D a (m i) plane ell S (mixedLabel D a (m i) plane ell x)).card) ∧ _
    rw [heq']
    exact hmin x (hSH hx)
  let mu := physicalMesh (m i) (phaseDepth (m i))/8
  let Sq := NativeWeightedGrainQuotientGeometry.retained D a (m i) ell plane S P hP0 hell hell4 hd mu
  let Sthird := second D a (m i) ell plane Sq
  obtain ⟨hSqS,hquot,_hkeys,_hlocal⟩ := NativeWeightedGrainQuotientSource.source_retention h hq hq1 hr
    (hm6 i) hell hell4 (Hsys i) A hA hnear hrD S hSE hSK P hP0 hd hSchart
  have hfour : Sq.card ≤ 4*Sthird.card := card_retention_four D a (m i) ell plane Sq
  have hSthird : (S.card:ℝ) ≤ quotientCost q*Sthird.card := by
    have hh : S.card ≤ (4*⌈quotientCap q⌉₊)*Sthird.card := by nlinarith only [hquot,hfour]
    dsimp only [quotientCost]
    exact_mod_cast hh
  have hRead : ∀x∈S,f (rawHeight D (m i) x.2)=nodeSlope P hP0 ell hell hell4 hd
      (sliceSpace (plane (spatialLabel D (2^(m i)) x.2)))
      (slice_horizontal (plane (spatialLabel D (2^(m i)) x.2))) := by
    intro x hx
    exact hSlope _ (hBN (hSB ▸ mem_image_of_mem (fineNode D (m i)) hx))
  refine ⟨hSthird,?_⟩
  intro Spre hSpre Cpre hCpre hPreRet
  obtain ⟨T,HT⟩ := exists_source_third_XY_bundle h original R E1 E2 h21 hE2 L schedule Rel
    htau heta hseed hg hgl hgrid Hbackbone hschedule Hcore hcost hconditioned hreference G hG lambda hlambda hret
    _hJ m hm6 ell hell4 S0 hS0 Q2 HU hq hq1 point tuple anchor Hsys Hhistory i hf hsmall HP K hK hKn
    p S Spre (hSH.trans hHp2) hSn P hP0 hell hd hSpre f hNorm hRead hMixed hm12 hdimension
    hJhorizontal pop hmu hpopE2 lower upper hLower hUpper
    (fun j => parent_profiles_readback h R E1 E2 level (m i) (NativeFixedHorizontalMenu.depths Jhorizontal (m i) j)
      p pop lambda tau seed c2 (hprofiles j)) Q2 (HParent p).1 (HParent p).2
    keep (selectionCost Khalf) Cpre hretain hCgraph hCpre hSret hPreRet
    Extra hExtraRefl hExtraSymm L3 hL3
  refine ⟨T,HT,?_⟩
  have hTS : T⊆Sthird := HT.1.1.trans hSpre
  have hTSgraph : T⊆S := HT.1.2.2.2.1
  have HmetricT := mapped_chart_metric D a (m i) ell plane Sq T hTS f (r^(-2*epsilon)) 0 (by positivity)
    (fun x hx y hy => hSmetric x (hTSgraph hx) y (hTSgraph hy))
  intro v hv w hw
  have hvS := Finset.image_subset_image hTS hv
  have hwS := Finset.image_subset_image hTS hw
  change ‖fixedField D a (m i) ell plane Sq f v-fixedField D a (m i) ell plane Sq f w‖ ≤ _
  rw [fixedField,NativeReferenceXYGridLinear.totalField_on _ _ _ hvS,
    NativeReferenceXYGridLinear.totalField_on _ _ _ hwS]
  exact HmetricT v hv w hw

end NativeActualPostGraphXYHook
