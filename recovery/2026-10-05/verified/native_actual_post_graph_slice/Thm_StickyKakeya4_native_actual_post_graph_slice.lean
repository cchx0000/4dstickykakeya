import Theorems.Thm_StickyKakeya4_native_post_graph_slice_data
import Theorems.Thm_StickyKakeya4_native_weighted_grain_quotient_cap
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeActualPostGraphSlice
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

theorem attach_actual_post_graph_slice {n d g level J d3 : ℕ} {D : FiniteScaleSource n}
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
    (m ell Q2 : ℕ) (hm6 : 6 ≤ m) (hf : phaseDepth m ≤ level) (hsmall : D.thickness ≤ 1/8)
    (HP : HasUniformFibers E2 Q2 (physicalPair h R a level (phaseDepth m)))
    (HV : HasUniformFibers E2 Q2 (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (hJ : 0 < J) (L3 : ℕ) (hL3 : 0 < L3) (stop Khalf : ℕ)
    (S0 : Finset Index) (point : Index → Index) (tuple : Index → Fin ell → (Fin n × Index))
    (anchor : Index → Fin ell → Fin n)
    (Hsys : IsNodeDirectionSystem D a m E2 S0 q ell point tuple anchor)
    (A : Index → Submodule ℝ E4) (hA : ∀k∈S0,Module.finrank ℝ (A k)=ell)
    (hnear : ∀z∈E2,Metric.infDist (slopeVector D z.1) (A z.2:Set E4) ≤ r)
    (hq : 0 < q) (hq1 : q ≤ 1) (hr : 0 < r) (hrD : r ≤ 64/((2^m:ℕ):ℝ))
    (points : Finset Index) (hpoints : points⊆S0) (Lgrain : ℕ)
    (HParent : ∀p : Parent,
      HasUniformFibers (parentEdges D a (2^m) E2 p) Q2 (fun z => slicePoint D a m p z.2) ∧
      ∀j,HasUniformFibers (parentEdges D a (2^m) E2 p) Q2
        (fun z => columnLabel D a (2^m) p (64/((2^(NativeFixedHorizontalMenu.depths J m j):ℕ):ℝ))
          (64/((2^m:ℕ):ℝ)) z.2))
    (H : HasSharpCurveParentProfiles h original R E1 E2 a level m (nodePlane D tuple)
      points q ell Q2 (factor d (g+1) L) G Lgrain lambda zeta tau seed c2
      (NativeFixedHorizontalMenu.depths J m) stop Khalf tuple r epsilon) :
    HasPostGraphParentProfiles h original R E1 E2 a level m (nodePlane D tuple)
      points q ell Q2 (factor d (g+1) L) G Lgrain lambda zeta tau seed c2
      J d3 L3 stop Khalf tuple r epsilon := by
  obtain ⟨ht,hmu,hretain,H,hHK,hHn,hhalf,p,hp,hHpn,hpop,href,hgrain,hmin,hprofiles,hcleaned,
    hheightL,hheightU,hdescendant,hplane,hpaid,hell,hell4,Hgraph⟩ := H
  obtain ⟨Nodes,hNodes,u0,hu0,hP0,hd,f,B,hBN,hBn,S,hSeq,hSH,hSn,hSB,hcut,
    hSparent,hAlign,hResid,hZero,hNorm,hCell,hSlope,hGraph,hMetric,hFib⟩ := Hgraph
  refine ⟨ht,hmu,hretain,H,hHK,hHn,hhalf,p,hp,hHpn,hpop,href,hgrain,hmin,hprofiles,hcleaned,
    hheightL,hheightU,hdescendant,hplane,hpaid,hell,hell4,
    Nodes,hNodes,u0,hu0,hP0,hd,f,B,hBN,hBn,S,hSeq,hSH,hSn,hSB,hcut,
    hSparent,hAlign,hResid,hZero,hNorm,hCell,hSlope,hGraph,hMetric,hFib,?_⟩
  intro Extra hExtraRefl hExtraSymm
  let plane := nodePlane D tuple
  let P := sliceSpace (plane u0)
  let pop := (lambda*(WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)/
    (2*(factor d (g+1) L:ℝ)*(G:ℝ)*(E2.card:ℝ)))*D.thickness^eta
  let keep := pop/rowConstant
  let eps := columnEpsilon D.thickness lambda (seed/8) c2
  let lower := profileLower D.thickness pop eps tau (seed/8)
    (min (boundaryWindow tau) ((tau/16)/1000))
  let upper := profileUpper D.thickness eps tau
  let t := ((cutEdges E2 points).card:ℝ)/(2*((((cutEdges E2 points).image
    (mixedLabel D a m plane ell)).card):ℝ))
  let Acap := lambda*D.thickness^(2*eta+2*zeta+4*tau)*(1/((2^m:ℕ):ℝ))^(-extremalExponent)
  let Ccap := parentCapConstant*(factor d (g+1) L:ℝ)*G*
    (vertexCap E2 (spatialLabel D (2^(phaseDepth m))) Q2:ℝ)
  have hdpos := h.1.2.1
  have hCgeom := NativeAnisotropicGlobalSourceBridge.comparisonCost_pos
  have hRow := rowConstant_pos
  have hLower : 0 < lower := by dsimp [lower,profileLower,eps,columnEpsilon]; positivity
  have hUpper : 0 < upper := by dsimp [upper,profileUpper,eps,columnEpsilon]; positivity
  have hHE2 : H⊆E2 := hHK.trans (cutEdges_subset E2 points)
  have hHp2 : parentEdges D a (2^m) H p⊆parentEdges D a (2^m) E2 p := filter_subset_filter _ hHE2
  have hSE : S⊆E2 := hSH.trans (hHp2.trans (filter_subset _ _))
  have hE2R : E2⊆retained original R := h21.trans Hcore.1
  have hpopE2 : pop*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E2 p).card :=
    hpop.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hHp2)) hdpos.le)
  have hSpoints : ∀z∈S,z.2∈S0 := by
    intro z hz
    exact hpoints (mem_filter.mp (hHK (mem_filter.mp (hSH hz)).1)).2
  have hSchart : ∀z∈S,cell P=cell (sliceSpace (plane (spatialLabel D (2^m) z.2))) := by
    intro z hz
    apply hCell
    exact hBN (hSB ▸ mem_image_of_mem (fineNode D m) hz)
  have hSmetric : ∀x∈S,∀y∈S,
      ‖f (rawHeight D m x.2)-f (rawHeight D m y.2)‖ ≤ r^(-2*epsilon)*
      |chartHeightCoordinate m 0 (rawHeight D m x.2)-chartHeightCoordinate m 0 (rawHeight D m y.2)| := by
    intro x hx y hy
    have hxB : fineNode D m x∈B := hSB ▸ mem_image_of_mem (fineNode D m) hx
    have hyB : fineNode D m y∈B := hSB ▸ mem_image_of_mem (fineNode D m) hy
    exact ((hMetric _ hxB _ hyB).2 0).trans
      (mul_le_mul_of_nonneg_right hpaid (abs_nonneg _))
  have hCgraph : (0:ℝ)<selectionCost Khalf := by
    dsimp [selectionCost,NativeProjectorCellChart.chartCount]
    positivity
  have hSret : keep*((parentEdges D a (2^m) E2 p).card:ℝ) ≤
      (selectionCost Khalf:ℝ)*S.card :=
    (href E2 hE2R).trans (by exact_mod_cast hcut)
  have hSgrain : ∀c∈S.image (mixedLabel D a m plane ell),
      t ≤ ((mixedFiber D a m plane ell S c).card:ℝ) := by
    intro c hc
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hc
    have hfib : mixedFiber D a m plane ell S (mixedLabel D a m plane ell x)=
        mixedFiber D a m plane ell (parentEdges D a (2^m) H p) (mixedLabel D a m plane ell x) :=
      (hFib _ (mem_image_of_mem _ hx)).1
    rw [hfib]
    exact (hmin x (hSH hx)).2.le
  have hAcap : 0 ≤ Acap := by dsimp [Acap]; positivity
  have hCapPos := parentCapConstant_pos
  have hCcap : 0 ≤ Ccap := by dsimp [Ccap]; positivity
  have hcap : ∀c : Parent × (Index × Index),∀U⊆E2,∀v : Index,
      (∀z∈U,parentLabel D a (2^m) z.1=c.1) →
      (∀z∈U,spatialLabel D (2^(phaseDepth m)) z.2=v) → Acap*(U.card:ℝ) ≤ Ccap := by
    intro c U hUE v hparent hspace
    exact source_parent_vertex_cap h original R E1 E2 h21 hE2 L schedule Rel htau heta hseed hg hgl hgrid
      Hbackbone hschedule Hcore hcost hconditioned hreference G hG lambda hlambda.le hret
      m (phaseDepth m) Q2 (by dsimp [phaseDepth]; omega) (by dsimp [phaseDepth]; omega)
      hf hsmall HP HV U hUE c.1 v hparent hspace
  exact construct_translated_slice_grain h original R level Hbackbone m hm6 hf hJ
    E2 hE2R p pop hmu hpopE2 lower upper hLower hUpper
    (fun j => parent_profiles_readback h R E1 E2 level m (NativeFixedHorizontalMenu.depths J m j)
      p pop lambda tau seed c2 (hprofiles j)) Q2 (HParent p).1 (HParent p).2
    S0 point tuple anchor Hsys A hA hnear hq hq1 hr hrD S (hSH.trans hHp2) hSn hSpoints
    P hP0 hell hell4 hd hSchart f (r^(-2*epsilon)) (by positivity) hNorm hSmetric
    keep (selectionCost Khalf) t Acap Ccap hretain hCgraph hAcap hCcap hSret hSgrain hcap
    Extra hExtraRefl hExtraSymm L3 hL3

end NativeActualPostGraphSlice
