import Theorems.Thm_StickyKakeya4_native_sharp_X_source_count
import Theorems.Thm_StickyKakeya4_native_sharp_X_power_algebra
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeActualSharpXLower
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

theorem source_reference_X_cross {n d g level J : ℕ} {D : FiniteScaleSource n}
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
    (loss : ℝ) (hloss : 0 ≤ loss)
    (hthreshold : ∀x∈T,
      ((cutEdges E2 K).card:ℝ)/(2*((((cutEdges E2 K).image
        (mixedLabel D a (m i)
          (fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node))) ell)).card):ℝ)) ≤
        loss*(mixedFiber D a (m i)
          (fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node))) ell T
          (mixedLabel D a (m i)
            (fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node))) ell x)).card) :
    let plane := fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node))
    let Lgrain := predecessorProduct D (m i) E2 Q2
      (scaleThreshold D E2 (m i)
        (history D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 i.val)
        ell (natStageDirectionIndex h (tuple i))) ell
    let mu := physicalMesh (m i) (phaseDepth (m i))/8
    ∀x∈T,
      lambda*D.thickness^(2*eta+3*zeta+7*tau)*(mass K (pointWeight E2):ℝ)*Lgrain ≤
        parentGrainConstant*transverseCost q ell*(Q2:ℝ)^2*(factor d (g+1) L:ℝ)*G*E2.card*
          loss*(((2^(phaseDepth (m i)-m i):ℕ):ℝ))*
            (referenceX D a (m i) ell plane T P hP hell1 hell hdim mu
              (referenceKey D a (m i) ell plane P hP hell1 hell hdim mu x)).card := by
  intro plane Lgrain mu x hx
  let M := vertexCap E2 (spatialLabel D (2^(phaseDepth (m i)))) Q2
  let A := lambda*D.thickness^(2*eta+2*zeta+4*tau)*(1/((2^(m i):ℕ):ℝ))^(-extremalExponent)
  let C := parentCapConstant*(factor d (g+1) L:ℝ)*G*(M:ℝ)
  have hmi : m i ≤ phaseDepth (m i) := by have hh := hm6 i; dsimp [phaseDepth]; omega
  have hAcap : 0 ≤ A := by dsimp [A]; have hd := h.1.2.1; positivity
  have hCcap : 0 ≤ C := by dsimp [C]; have hh := parentCapConstant_pos; positivity
  have hcap : ∀c : Parent × (Index × Index),∀U⊆E2,∀v : Index,
      (∀z∈U,parentLabel D a (2^(m i)) z.1=c.1) →
      (∀z∈U,spatialLabel D (2^(phaseDepth (m i))) z.2=v) → A*(U.card:ℝ) ≤ C := by
    intro c U hUE v hparent hspace
    exact source_parent_vertex_cap h original R E1 E2 h21 hE2 L schedule Rel htau heta hseed hg hgl hgrid
      Hbackbone hschedule Hcore hcost hconditioned hreference G hG lambda hlambda.le hret
      (m i) (phaseDepth (m i)) Q2 hmi ((hm6 i).trans hmi) hf hsmall HP (HU i) U hUE c.1 v hparent hspace
  have hc := every_reference_fiber_density_cross D a (m i) ell hmi plane E2 Hgraph T hHE2
    P hP hell1 hell hdim mu (div_pos (physicalMesh_pos _ _) (by norm_num)) le_rfl hT
    A C loss _ hAcap hCcap hloss hcap hthreshold x hx
  exact source_threshold_cross_cancellation h original R E1 E2 h21 hE2 L schedule Rel htau heta hseed hg hgl hgrid
    Hbackbone hschedule Hcore hcost hconditioned hreference G hG lambda hlambda hret _hJ m hm6 ell hell
    S0 hS0 Q2 HU hq hq1 point tuple anchor Hsys Hhistory i hf hsmall HP K hK hKn
    loss _ _ hloss (Nat.cast_nonneg _) (Nat.cast_nonneg _) hc

end NativeActualSharpXLower
