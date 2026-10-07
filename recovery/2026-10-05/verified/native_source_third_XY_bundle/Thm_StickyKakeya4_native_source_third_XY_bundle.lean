import Theorems.Thm_StickyKakeya4_native_third_XY_construction
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data
import Theorems.Thm_StickyKakeya4_native_actual_sharp_X_power_loss
import Theorems.Thm_StickyKakeya4_native_sharp_mixed_grain_core
import Theorems.Thm_StickyKakeya4_native_grain_height_projection_source
import Theorems.Thm_StickyKakeya4_native_actual_sharp_X_power
import Theorems.Thm_StickyKakeya4_native_actual_sharp_X_lower
import Theorems.Thm_StickyKakeya4_native_sharp_X_history_power
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
noncomputable section
namespace NativeSourceThirdXYBundle
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeSpatialAngularGeometry NativeSquaredGrainQueries NativeActualProjectedGrainCount
open NativeQueriedVertexWeights NativeOriginalPacketReference NativeCompatibleNodeDirections
open NativeDirectionRankDichotomy NativeActualGrainHistory NativeHistoryGrainCount NativeHistoryGrainCleanup
open NativeParentGrainIncidenceCleanup NativeParentVertexMassCap NativeSpatialParentCount
open NativeConditionedPairMenu NativeAllTwoScaleConfiguration NativeTwoScaleConfiguration
open NativeMiddleWindowBalance NativeFixedCompactKakeyaExponent NativeFullCoarseShadow
open NativeRetainedFinePairDensity RichDirectionalLayers WeightedRichDirectionalLayers
open NativeSourceParentGrainCleanup NativeHistoryGrainPowerDensity
open scoped BigOperators

open NativeSharpXCapCancellation

open NativeSharpXSourceCount NativeSharpXPowerAlgebra NativeTranslatedGrainHeightFibers
open NativeTranslatedGrainHeightSelection NativeWeightedGrainQuotientGeometry NativeHorizontalGrainSlice
open NativeGrainHeightProjectionFibers NativeGrainQuotientFibers

open NativeActualSharpXLower NativeSharpXHistoryPower NativeRetainedSliceBudgetAlgebra

open NativeThirdXYConstruction NativeThirdXYData NativeThirdXYSourceData
open NativeTranslatedGrainHeightOverlap
open NativeReferenceXYGridField NativeGrainHeightProjectionSource NativeSharpMixedGrainCore
open NativeHeightSlopeCoordinates NativeActualQuotientAD NativeQuotientConstantBound
open NativeAnisotropicShortRowGeometry NativeAnisotropicSliceLabels NativeReferenceSliceClassBounds
open NativeReferenceXYGridPoints
open scoped Matrix.Norms.Elementwise

/-- Construct exactly one actual third core from the paid pre-third subset.
The same T simultaneously carries original-point/caller/XY/grain uniformity,
XY AD, source-derived full X-fiber density, and quotient Y AD. -/
theorem exists_source_third_XY_bundle {n d g level J Jhorizontal d3 : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed tau q c1 c2 : ℝ}
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
    (_hJ : 0 < J) (m : Fin J → ℕ) (hm6 : ∀i,6 ≤ m i) (ell : ℕ) (hell : ell ≤ 4)
    (S0 : Finset Index) (hS0 : S0⊆E2.image Prod.snd) (Q2 : ℕ)
    (HU : ∀i,HasUniformFibers E2 Q2 (fun z => spatialLabel D (2^(phaseDepth (m i))) z.2))
    (hq : 0 < q) (hq1 : q ≤ 1)
    (point : Fin J → Index → Index)
    (tuple : Fin J → Index → Fin ell → (Fin n × Index))
    (anchor : Fin J → Index → Fin ell → Fin n)
    (Hsys : ∀i,IsNodeDirectionSystem D a (m i) E2 S0 q ell (point i) (tuple i) (anchor i))
    (Hhistory : HasGrainHistory D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 Q2 lambda c1 c2)
    (i : Fin J) (hf : phaseDepth (m i) ≤ level) (hsmall : D.thickness ≤ 1/8)
    (HP : HasUniformFibers E2 Q2 (physicalPair h R a level (phaseDepth (m i))))
    (K : Finset Index)
    (hK : K⊆history D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 J)
    (hKn : K.Nonempty)
    (p : Parent) (Hgraph S : Finset (Fin n × Index))
    (hH : Hgraph⊆parentEdges D a (2^(m i)) E2 p) (hHn : Hgraph.Nonempty)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell1 : 1 ≤ ell)
    (hdim : Module.finrank ℝ P=ell-1)
    (hS : S⊆second D a (m i) ell (nodePlane D (tuple i))
      (NativeWeightedGrainQuotientGeometry.retained D a (m i) ell (nodePlane D (tuple i))
        Hgraph P hP hell1 hell hdim (physicalMesh (m i) (phaseDepth (m i))/8)))
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hFraw : ∀height,‖Fraw height‖ ≤ (1/4:ℝ))
    (HreadGraph : ∀x∈Hgraph,Fraw (rawHeight D (m i) x.2)=
      nodeSlope P hP ell hell1 hell hdim
        (sliceSpace (nodePlane D (tuple i) (spatialLabel D (2^(m i)) x.2)))
        (slice_horizontal (nodePlane D (tuple i) (spatialLabel D (2^(m i)) x.2))))
    (hMixed : HasMixedIncidenceThreshold D a (m i) (nodePlane D (tuple i)) ell E2 K Hgraph)
    (hm12 : 12 ≤ m i) (hdimension : extremalExponent+(ell:ℝ) ≤ 4)
    (hJhorizontal : 0 < Jhorizontal)
    (population : ℝ) (hpopulation : 0 < population)
    (hpop : population*(R.filter (fun v => parentLabel D a (2^(m i)) v=p)).card ≤
      D.thickness*(parentEdges D a (2^(m i)) E2 p).card)
    (profileLower profileUpper : ℝ) (hProfileLower : 0 < profileLower) (hProfileUpper : 0 < profileUpper)
    (Hprofile : ∀j,HasColumnPowerProfile D a (m i) (NativeFixedHorizontalMenu.depths Jhorizontal (m i) j)
      E2 p profileLower profileUpper)
    (Qref : ℕ)
    (HPoint : HasUniformFibers (parentEdges D a (2^(m i)) E2 p) Qref
      (fun z => slicePoint D a (m i) p z.2))
    (HColumn : ∀j,HasUniformFibers (parentEdges D a (2^(m i)) E2 p) Qref
      (fun z => columnLabel D a (2^(m i)) p
        (64/((2^(NativeFixedHorizontalMenu.depths Jhorizontal (m i) j):ℕ):ℝ)) (64/((2^(m i):ℕ):ℝ)) z.2))
    (lambdaParent GParent Cpre : ℝ) (hlambdaParent : 0 < lambdaParent) (hGParent : 0 < GParent)
    (hCpre : 0 < Cpre)
    (hParentRet : lambdaParent*((parentEdges D a (2^(m i)) E2 p).card:ℝ) ≤ GParent*Hgraph.card)
    (hPreRet : (Hgraph.card:ℝ) ≤ Cpre*S.card)
    (Rel3 : Fin d3 → (Fin n × Index) → (Fin n × Index) → Prop)
    (hrefl3 : ∀j x,Rel3 j x x) (hsym3 : ∀j x y,Rel3 j x y → Rel3 j y x)
    (L3 : ℕ) (hL3 : 0 < L3) :
    let plane := nodePlane D (tuple i)
    let t := ((cutEdges E2 K).card:ℝ)/(2*((((cutEdges E2 K).image (mixedLabel D a (m i) plane ell)).card):ℝ))
    let F3 := NativeRetainedSliceCore.refinementCost (d3+2) (Jhorizontal+1) L3
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let CX := (Cpre/quotientCost q)*fiberCoefficient D.thickness eta zeta tau c1 c2 lambda
      ((mass K (pointWeight E2):ℝ)/(E2.card:ℝ)) (factor d (g+1) L) G Q2 F3 Q3 q ell
    ∃T,HasThirdXYSourceData (J:=Jhorizontal) D zeta a (m i) plane E2 Hgraph S T P hP hell1 hell hdim
      Fraw p population profileLower profileUpper Qref lambdaParent GParent Cpre t L3 Rel3 CX := by
  intro plane t F3 Q3 CX
  have hE2ret : E2⊆retained original R := h21.trans Hcore.1
  have hgrain : ∀c∈Hgraph.image (mixedLabel D a (m i) plane ell),
      t ≤ ((mixedFiber D a (m i) plane ell Hgraph c).card:ℝ) := by
    intro c hc
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hc
    exact (hMixed x hx).2.le
  obtain ⟨T,HT⟩ := construct_third_XY_data h original R level Hbackbone (m i) (hm6 i) hf hJhorizontal
    E2 hE2ret p population hpopulation hpop profileLower profileUpper hProfileLower hProfileUpper
    Hprofile Qref HPoint HColumn ell P hP hell1 hell hdim plane Hgraph S hH hHn hS Fraw hFraw
    lambdaParent GParent Cpre t hlambdaParent hGParent hCpre hParentRet hPreRet hgrain Rel3 hrefl3 hsym3 L3 hL3
  have HTcopy := HT
  rcases HTcopy with ⟨hTS,hTn,_hCost,hTH,_hFinal,_hExtra,_hOld,_hXY,_hClass,_hGrain,_hKey,hThreshold,_hRet,hAD,_hFieldRead,_hFieldNorm⟩
  let mu := physicalMesh (m i) (phaseDepth (m i))/8
  let Sq := NativeWeightedGrainQuotientGeometry.retained D a (m i) ell plane Hgraph P hP hell1 hell hdim mu
  let KXY := xyConstant D.thickness zeta population profileLower profileUpper lambdaParent
    (GParent*Cpre*(F3:ℝ)) Qref Q3 Jhorizontal (m i)
  have hKXYone : 1 ≤ KXY := xyConstant_one_le _ _ _ _ _ _ _ _ _ _ _
  have hKXYpos : 0 < KXY := lt_of_lt_of_le (by norm_num) hKXYone
  have hTpre : T⊆second D a (m i) ell plane Sq := hTS.trans hS
  have hParentT : ∀x∈T,parentLabel D a (2^(m i)) x.1=p := fun x hx => (mem_filter.mp (hH (hTH hx))).2
  have hTI : T⊆incidences original :=
    hTH.trans (hH.trans ((filter_subset _ _).trans (hE2ret.trans (filter_subset _ _))))
  have Hread : ∀x∈second D a (m i) ell plane Sq,Fraw (rawHeight D (m i) x.2)=
      nodeSlope P hP ell hell1 hell hdim (sliceSpace (plane (spatialLabel D (2^(m i)) x.2)))
        (slice_horizontal (plane (spatialLabel D (2^(m i)) x.2))) := by
    intro x hx
    exact HreadGraph x ((NativeWeightedGrainQuotientGeometry.retained_subset D a (m i) ell plane
      Hgraph P hP hell1 hell hdim mu) ((second_subset D a (m i) ell plane Sq) hx))
  have Hpower := NativeActualSharpXPowerLoss.source_reference_X_power_lower_with_loss h original R E1 E2 h21 hE2 L
    schedule Rel htau heta hseed hg hgl hgrid Hbackbone hschedule Hcore hcost hconditioned hreference
    G hG lambda hlambda hret _hJ m hm6 ell hell S0 hS0 Q2 HU hq hq1 point tuple anchor Hsys Hhistory i hf hsmall
    HP K hK hKn Hgraph T (hH.trans (filter_subset _ _)) P hP hell1 hdim hTpre F3 Q3 Cpre hCpre.le hThreshold
  have HX : ∀x∈T,(rho (m i))^(-((ell:ℝ)-1)) ≤ CX*
      (referenceX D a (m i) ell plane T P hP hell1 hell hdim (NativeReferenceXYGridPoints.mu (m i))
        (referenceKey D a (m i) ell plane P hP hell1 hell hdim (NativeReferenceXYGridPoints.mu (m i)) x)).card := by
    intro x hx
    have hplane : plane=(fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1)
        (List.ofFn (tuple i node))) := rfl
    rw [hplane,NativeReferenceXYGridPoints.mu_phase (m i) (hm6 i)]
    exact Hpower x hx
  have HY := of_reference_cross h original Hbackbone.1 Hbackbone.2.2.1 (m i) level ell hm12 Hbackbone.2.1 hf
    p plane Sq T hTpre hTn hTI hParentT P hP hell1 hell hdim hdimension Fraw hFraw Hread CX KXY hKXYpos HX hAD
  refine ⟨T,HT,HY.1,?_,HY.2,?_⟩
  · intro x hx
    have hh := HX x hx
    rw [NativeReferenceXYGridPoints.mu_phase (m i) (hm6 i)] at hh
    exact hh
  · intro hell2 hell3
    exact quotientConstant_le ell hell2 hell3 extremalExponent KXY CX extremalExponent_nonneg hKXYone HY.1

end NativeSourceThirdXYBundle
