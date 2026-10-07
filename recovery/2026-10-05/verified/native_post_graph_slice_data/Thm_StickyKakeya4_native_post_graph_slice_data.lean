import Theorems.Thm_StickyKakeya4_native_sharp_parent_graph_configuration
import Theorems.Thm_StickyKakeya4_native_translated_slice_grain_join
import Theorems.Thm_StickyKakeya4_native_reference_slice_budget_readback
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace NativePostGraphSliceData
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

open NativeCompatibleAngularCandidates
open NativeHeightSlopeCoordinates NativeHorizontalGraphCoordinates NativeOriginalCellChartGeometry
open NativeSharpParentGraphData NativeReferenceSliceBudgetAlgebra NativeReferenceSliceBudgetReadback
open NativeParentHeightAlignment NativeParentHeightGraphCore NativeSharpMixedGrainCore
open NativeOriginalPacketReference NativeQueriedVertexWeights NativeParentVertexMassCap
open NativeActualProjectedGrainCount RichDirectionalLayers WeightedRichDirectionalLayers
open NativeSourceParentGrainCleanup NativeActivePhasePopulation NativePhaseHeightPopulation
open NativeCombinedParentProfiles NativeFullCoarseShadow NativeAllTwoScaleConfiguration

/-- The literal output of the one third refinement on the stored graph core. -/
def HasTranslatedSliceData {n d J ell : ℕ} (D : FiniteScaleSource n) (zeta a q : ℝ)
    (m : ℕ) (tuple : Index → Fin ell → (Fin n × Index)) (H : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (p : Parent) (metric population profileLower profileUpper : ℝ) (Qref : ℕ)
    (lambda G t Acap Ccap : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) : Prop :=
  let plane := nodePlane D tuple
    let mu := physicalMesh m (phaseDepth m)/8
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell plane H P hP hell hell4 hd mu
    let S := second D a m ell plane Sq
    let Cq : ℝ := 4*⌈quotientCap q⌉₊
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let F3 := refinementCost (d+1) (J+1) L3
    let pt := fun z : Fin n × Index => slicePoint D a m p z.2
    let grain := mixedLabel D a m plane ell
    let key := referenceKey D a m ell plane P hP hell hell4 hd mu
    let Flow := mapped D a m ell plane Sq Fraw
    let low := lowerCountCoefficient D.thickness zeta population profileUpper
    let up := upperCountCoefficient D.thickness zeta profileLower
    let gap : ℝ := max 8 ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)
    let KAD := constant (lambda*(low/up)/((G*Cq*(F3:ℝ))*(Qref:ℝ)^2*(Q3:ℝ)^4))
      ((Qref:ℝ)^4*up/low) gap (3-extremalExponent)
    ∃T⊆S,T.Nonempty ∧ T⊆H ∧ H.card ≤ (4*⌈quotientCap q⌉₊)*F3*T.card ∧
      (∀j x y,x∈T → y∈T → degree (fun _ : Fin n × Index => 1) (Rel j) T x ≤
        Q3^2*degree (fun _ : Fin n × Index => 1) (Rel j) T y) ∧
      HasUniformFibers T Q3 pt ∧
      (∀j,HasUniformFibers T Q3 (fun z => sliceClass m (NativeFixedHorizontalMenu.depths J m j) (pt z))) ∧
      HasUniformFibers T Q3 grain ∧
      (∀x y,x∈T → y∈T → grain x=grain y → key x=key y) ∧
      (∀x∈T,t ≤ Cq*(F3:ℝ)*(Q3:ℝ)^2*(mixedFiber D a m plane ell T (grain x)).card) ∧
      (∀height : ℤ,ADBounds (NativeSliceClassBalls.realizedSlice (T.image pt)
        (horizontalMesh m) height) (horizontalMesh m) KAD (3-extremalExponent)) ∧
      (∀x∈T,Flow (translatedHeight D a m x.2)=Fraw (rawHeight D m x.2)) ∧
      (∀height,‖Flow height‖ ≤ (1/4:ℝ)) ∧
      (∀s∈T.image (fun z => translatedHeight D a m z.2),∀u∈T.image (fun z => translatedHeight D a m z.2),
        ‖Flow s-Flow u‖ ≤ (3*metric)*|referenceHeight m s-referenceHeight m u|) ∧
      ∀x∈T,Acap*t ≤ (Cq*(F3:ℝ)*(Q3:ℝ)^2)*Ccap*(((2^(phaseDepth m-m):ℕ):ℝ))*
        (referenceX D a m ell plane T P hP hell hell4 hd mu (key x)).card

def HasHeightCoreWith {n ell : ℕ} (D : FiniteScaleSource n) (a q : ℝ)
    (m stop K : ℕ) (H : Finset (Fin n × Index))
    (tuple : Index → Fin ell → (Fin n × Index)) (p : Parent)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (Finish : (P : Submodule ℝ E4) → P≤heightKernel →
      Module.finrank ℝ P=ell-1 → (ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) →
      Finset (Fin n × Index) → Prop) : Prop :=
    let plane := fun u => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple u))
    let horizontal := fun u => sliceSpace (plane u)
    let L := metricConstant ((stop-6)/(2*K)+1) (NativeSeparatedSpanControl.coefficientCost 2 q ell)
    ∃A⊆H.image (fineNode D m),∃u0∈A,∃hP0 : horizontal u0≤heightKernel,
      ∃hd : Module.finrank ℝ (horizontal u0)=ell-1,
      ∃f : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ,
      ∃B⊆A,B.Nonempty ∧ ∃S : Finset (Fin n × Index),
        S=nodeCut D m H B ∧ S⊆H ∧ S.Nonempty ∧ S.image (fineNode D m)=B ∧
        H.card ≤ selectionCost K*S.card ∧
        (∀z∈S,parentLabel D a (2^m) z.1=p) ∧
        (∀j u v,u∈A→v∈A→
          spatialAncestor m (halfDepth K stop j) u (3:Fin 4)=spatialAncestor m (halfDepth K stop j) v (3:Fin 4)→
          spatialAncestor m (halfDepth K stop j) u=spatialAncestor m (halfDepth K stop j) v) ∧
        (∀j u v,u∈B→v∈B→|u (3:Fin 4)-v (3:Fin 4)| < ((2^(m-halfDepth K stop j):ℕ):ℤ)→
          spatialAncestor m (halfDepth K stop j) u (3:Fin 4)=spatialAncestor m (halfDepth K stop j) v (3:Fin 4)) ∧
        (∀t,t∉A.image (fun u => u (3:Fin 4))→f t=0) ∧ (∀t,‖f t‖ ≤ (1/4:ℝ)) ∧
        (∀u∈A,cell (horizontal u0)=cell (horizontal u)) ∧
        (∀u∈A,f (u (3:Fin 4))=nodeSlope (horizontal u0) hP0 ell hell hell4 hd
          (horizontal u) (show horizontal u≤heightKernel from inf_le_right)) ∧
        (∀u∈A,∀v : E4,v∈horizontal u ↔ ∃x : EuclideanSpace ℝ (Fin (ell-1)),
          ((domainBasis (horizontal u0) ell hd).repr.symm x:horizontal u0)+
            (((normalBasis (horizontal u0) hP0 ell hell hell4 hd).repr.symm
              (matrixVector (f (u (3:Fin 4))) x):normalSpace (horizontal u0)):E4)=v) ∧
        (∀u∈B,∀v∈B,
          (‖f (u (3:Fin 4))-f (v (3:Fin 4))‖ ≤ L*
            |rawHeightCoordinate m (u (3:Fin 4))-rawHeightCoordinate m (v (3:Fin 4))|) ∧
          ∀shift : ℝ,‖f (u (3:Fin 4))-f (v (3:Fin 4))‖ ≤ (512*L)*
            |chartHeightCoordinate m shift (u (3:Fin 4))-chartHeightCoordinate m shift (v (3:Fin 4))|) ∧
        (∀c∈S.image (mixedLabel D a m plane ell),
          mixedFiber D a m plane ell S c=mixedFiber D a m plane ell H c ∧
          ∀b,mixedVertices D a m b plane ell S c=mixedVertices D a m b plane ell H c) ∧
        Finish (horizontal u0) hP0 hd f S

def HasPostGraphParentProfiles {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 E2 : Finset (Fin n × Index)) (a : ℝ) (level m : ℕ)
    (plane : Index → Submodule ℝ E4) (points : Finset Index) (q : ℝ) (ell Q2 F1 G Lgrain : ℕ)
    (lambda zeta tau seed c2 : ℝ) (J d3 L3 : ℕ)
    (stop Khalf : ℕ) (tuple : Index → Fin ell → (Fin n × Index)) (r epsilon : ℝ) : Prop :=
  let depths := NativeFixedHorizontalMenu.depths J m
  let W := mass points (pointWeight E2)
  let theta := lambda*(W:ℝ)/(2*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ))
  let mu := theta*D.thickness^eta
  let retain := mu/rowConstant
  0 < theta ∧ 0 < mu ∧ 0 < retain ∧
    ∃H⊆cutEdges E2 points,H.Nonempty ∧ W ≤ 2*H.card ∧
      ∃p∈R.image (parentLabel D a (2^m)),(parentEdges D a (2^m) H p).Nonempty ∧
        mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤ D.thickness*(parentEdges D a (2^m) H p).card ∧
        (∀I⊆retained original R,retain*(parentEdges D a (2^m) I p).card ≤ (parentEdges D a (2^m) H p).card) ∧
        (∀x∈parentEdges D a (2^m) H p,
          lambda*D.thickness^(2*eta+3*zeta+7*tau)*(W:ℝ)*Lgrain <
            parentGrainConstant*transverseCost q ell*(Q2:ℝ)^2*(F1:ℝ)*G*E2.card*
              (mixedVertices D a m (phaseDepth m) plane ell (parentEdges D a (2^m) H p)
                (mixedLabel D a m plane ell x)).card) ∧
        HasMixedIncidenceThreshold D a m plane ell E2 points (parentEdges D a (2^m) H p) ∧
        (∀u,HasParentProfiles h R E1 E2 a level m (depths u) p retain lambda tau seed c2) ∧
        (∀u,
          let relative := (64/((2^(depths u):ℕ):ℝ))/(64/((2^m:ℕ):ℝ))
          let M := (NativeFiniteKakeyaCounts.multiplicity
            (fullSource h R a level (depths u) (parentEdges D a (2^m) H p))).toReal
          retain*D.thickness^(tau+seed/8+10*min (boundaryWindow tau) ((tau/16)/1000))*relative^(-extremalExponent) ≤ M ∧
            M ≤ D.thickness^(-(3*tau))*relative^(-extremalExponent)) ∧
        mu ≤ (43904*(64/((2^m:ℕ):ℝ)))*(heightLabels D a (64/((2^m:ℕ):ℝ)) (parentEdges D a (2^m) E2 p)).card ∧
        (64/((2^m:ℕ):ℝ))*(heightLabels D a (64/((2^m:ℕ):ℝ)) (parentEdges D a (2^m) E2 p)).card ≤ 10 ∧
        (∀f : ℕ,m ≤ f → f ≤ level →
          (mu*D.thickness^(2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3 ≤
            rowConstant*(activePhases D a f (parentEdges D a (2^m) E2 p)).card ∧
          ((activePhases D a f (parentEdges D a (2^m) E2 p)).card:ℝ) ≤
            D.thickness^(-2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3) ∧
          mu*D.thickness^(2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3 ≤
            (43904*(64/((2^m:ℕ):ℝ)))*
              (phaseHeightLabels D a (64/((2^m:ℕ):ℝ)) f (parentEdges D a (2^m) E2 p)).card) ∧
        plane=(fun u => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple u))) ∧
        512*metricConstant ((stop-6)/(2*Khalf)+1) (NativeSeparatedSpanControl.coefficientCost 2 q ell) ≤ r^(-2*epsilon) ∧
        ∃hell : 1 ≤ ell,∃hell4 : ell ≤ 4,
          HasHeightCoreWith D a q m stop Khalf (parentEdges D a (2^m) H p) tuple p hell hell4
            (fun P hP hd f Hgraph =>
              ∀Rel : Fin d3 → (Fin n × Index) → (Fin n × Index) → Prop,
                (∀j x,Rel j x x) → (∀j x y,Rel j x y → Rel j y x) →
                HasTranslatedSliceData (J:=J) D zeta a q m tuple Hgraph P hP hell hell4 hd f p
                  (r^(-2*epsilon)) mu
                  (profileLower D.thickness mu (columnEpsilon D.thickness lambda (seed/8) c2)
                    tau (seed/8) (min (boundaryWindow tau) ((tau/16)/1000)))
                  (profileUpper D.thickness (columnEpsilon D.thickness lambda (seed/8) c2) tau) Q2
                  retain (selectionCost Khalf)
                  (((cutEdges E2 points).card:ℝ)/(2*((((cutEdges E2 points).image
                    (mixedLabel D a m plane ell)).card):ℝ)))
                  (lambda*D.thickness^(2*eta+2*zeta+4*tau)*(1/((2^m:ℕ):ℝ))^(-extremalExponent))
                  (parentCapConstant*(F1:ℝ)*G*(vertexCap E2 (spatialLabel D (2^(phaseDepth m))) Q2:ℝ))
                  L3 Rel)



end NativePostGraphSliceData
