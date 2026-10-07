import Theorems.Thm_StickyKakeya4_native_grain_height_projection_source
import Theorems.Thm_StickyKakeya4_native_actual_quotient_ad
import Theorems.Thm_StickyKakeya4_native_actual_sharp_X_power
import Theorems.Thm_StickyKakeya4_native_sharp_X_history_power
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
noncomputable section
namespace NativeSourceQuotientAD
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

open NativeGrainHeightProjectionSource
open NativeReferenceXYGridMaps NativeReferenceXYGridPoints NativeReferenceXYGridField
open NativeHeightSlopeCoordinates NativeTranslatedGrainHeightOverlap NativeActualQuotientAD
open NativeTwoMapRetainedSliceActualCaps NativeQuotientLatticeTransport NativeEncodedQuotientAD NativeSliceClassBalls
open scoped Matrix.Norms.Elementwise

/-- The same actual source/history and third-core grain threshold produce
quotient AD, with no X-population or quotient-AD premise. XY AD is read from
the already constructed same-core ambient endpoint. -/
theorem source_quotient_AD {n d g level J : ℕ} {D : FiniteScaleSource n}
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
    (Hgraph T : Finset (Fin n × Index)) (hHE2 : Hgraph⊆E2)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell1 : 1 ≤ ell)
    (hdim : Module.finrank ℝ P=ell-1)
    (hT : T⊆second D a (m i) ell
      (fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node)))
      (NativeWeightedGrainQuotientGeometry.retained D a (m i) ell
        (fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node)))
        Hgraph P hP hell1 hell hdim (physicalMesh (m i) (phaseDepth (m i))/8)))
    (F3 Q3 : ℕ)
    (hthreshold : ∀x∈T,
      ((cutEdges E2 K).card:ℝ)/(2*((((cutEdges E2 K).image
        (mixedLabel D a (m i)
          (fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node))) ell)).card):ℝ)) ≤
        (quotientCost q*(F3:ℝ)*(Q3:ℝ)^2)*(mixedFiber D a (m i)
          (fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node))) ell T
          (mixedLabel D a (m i)
            (fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node))) ell x)).card)
    (p : Parent) (hTn : T.Nonempty) (hm12 : 12 ≤ m i)
    (hparent : ∀x∈T,parentLabel D a (2^(m i)) x.1=p)
    (hdimension : extremalExponent+(ell:ℝ) ≤ 4)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hFraw : ∀t,‖Fraw t‖ ≤ (1/4:ℝ))
    (Hread : let plane := nodePlane D (tuple i)
      let Sq := NativeWeightedGrainQuotientGeometry.retained D a (m i) ell plane Hgraph P hP hell1 hell hdim
        (physicalMesh (m i) (phaseDepth (m i))/8)
      ∀x∈second D a (m i) ell plane Sq,Fraw (rawHeight D (m i) x.2)=
        nodeSlope P hP ell hell1 hell hdim (sliceSpace (plane (spatialLabel D (2^(m i)) x.2)))
          (slice_horizontal (plane (spatialLabel D (2^(m i)) x.2))))
    (KXY : ℝ) (hKXY : 0 < KXY)
    (HXY : let plane := nodePlane D (tuple i)
      let Sq := NativeWeightedGrainQuotientGeometry.retained D a (m i) ell plane Hgraph P hP hell1 hell hdim
        (physicalMesh (m i) (phaseDepth (m i))/8)
      ∀height : ℤ,FiniteVoronoiRealADCoarsening.ADBounds
        (realizedSlice (T.image (fun x => encodedPoint D a (m i) ell p P hP hell1 hell hdim
          (fixedField D a (m i) ell plane Sq Fraw) x.2)) (NativeReferenceXYGridPoints.mu (m i)) height)
        (NativeReferenceXYGridPoints.mu (m i)) KXY (3-extremalExponent)) :
    let plane := nodePlane D (tuple i)
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a (m i) ell plane Hgraph P hP hell1 hell hdim
      (physicalMesh (m i) (phaseDepth (m i))/8)
    let CX := fiberCoefficient D.thickness eta zeta tau c1 c2 lambda
      ((mass K (pointWeight E2):ℝ)/(E2.card:ℝ)) (factor d (g+1) L) G Q2 F3 Q3 q ell
    0 < CX ∧ ∀height : ℤ,FiniteVoronoiRealADCoarsening.ADBounds
      (((productSlice (T.image (fun x => pxy D a (m i) ell p P hP hell1 hell hdim
        (fixedField D a (m i) ell plane Sq Fraw) x.2)) height).image Prod.snd).image
          (NativeQuotientGridCenters.center (NativeReferenceXYGridPoints.mu (m i))))
      (NativeReferenceXYGridPoints.mu (m i))
      (quotientConstant (ell-1) (4-ell) (1/((32:ℝ)^(ell-1)*CX)) KXY (3-extremalExponent))
      (4-(ell:ℝ)-extremalExponent) := by
  intro plane Sq CX
  have hpower := NativeActualSharpXPower.source_reference_X_power_lower h original R E1 E2 h21 hE2 L schedule Rel
    htau heta hseed hg hgl hgrid Hbackbone hschedule Hcore hcost hconditioned hreference
    G hG lambda hlambda hret _hJ m hm6 ell hell S0 hS0 Q2 HU hq hq1 point tuple anchor Hsys Hhistory
    i hf hsmall HP K hK hKn Hgraph T hHE2 P hP hell1 hdim hT F3 Q3 hthreshold
  have hTI : T⊆incidences original := by
    exact hT.trans ((second_subset D a (m i) ell plane Sq).trans
      ((NativeWeightedGrainQuotientGeometry.retained_subset D a (m i) ell plane Hgraph P hP hell1 hell hdim
        (physicalMesh (m i) (phaseDepth (m i))/8)).trans
        (hHE2.trans (h21.trans (Hcore.1.trans (filter_subset _ _))))))
  have hcross : ∀x∈T,(NativeReferenceXYGridPoints.rho (m i))^(-((ell:ℝ)-1)) ≤ CX*
      (referenceX D a (m i) ell plane T P hP hell1 hell hdim (NativeReferenceXYGridPoints.mu (m i))
        (referenceKey D a (m i) ell plane P hP hell1 hell hdim (NativeReferenceXYGridPoints.mu (m i)) x)).card := by
    intro x hx
    have hplane : plane=(fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1)
        (List.ofFn (tuple i node))) := rfl
    rw [hplane,NativeReferenceXYGridPoints.mu_phase (m i) (hm6 i)]
    exact hpower x hx
  exact of_reference_cross h original Hbackbone.1 Hbackbone.2.2.1 (m i) level ell hm12 Hbackbone.2.1 hf
    p plane Sq T hT hTn hTI hparent P hP hell1 hell hdim hdimension Fraw hFraw Hread CX KXY hKXY hcross HXY

end NativeSourceQuotientAD
