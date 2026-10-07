import Theorems.Thm_StickyKakeya4_native_post_graph_slice_data
import Theorems.Thm_StickyKakeya4_native_source_third_XY_bundle
import Theorems.Thm_StickyKakeya4_native_saturated_parent_graph_data
import Theorems.Thm_StickyKakeya4_native_sharp_parent_graph_configuration
import Theorems.Thm_StickyKakeya4_native_translated_slice_grain_join
import Theorems.Thm_StickyKakeya4_native_reference_slice_budget_readback
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace NativePostGraphXYHookData
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

open NativePostGraphSliceData NativeThirdXYSourceData NativeSharpXPowerAlgebra NativeRetainedSliceBudgetAlgebra
open NativeReferenceXYGridField NativeSaturatedMixedGrainCore

/-- One literal third-core family. Its field is fixed from the paid quotient
source before T, and all X/Y assertions concern that exact T. -/
def HasThirdXYFinish {n d3 J ell : ℕ} (D : FiniteScaleSource n)
    (eta zeta a q tau c1 c2 lambda b : ℝ) (F1 G Q2 : ℕ) (m : ℕ)
    (tuple : Index → Fin ell → (Fin n × Index)) (E H : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (p : Parent) (population PL PU retain Cgraph t metric : ℝ) (L3 : ℕ)
    (Rel3 : Fin d3 → (Fin n × Index) → (Fin n × Index) → Prop) : Prop :=
  let plane := nodePlane D tuple
  let mu := physicalMesh m (phaseDepth m)/8
  let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell plane H P hP hell hell4 hd mu
  let S := second D a m ell plane Sq
  let field := fixedField D a m ell plane Sq Fraw
  (H.card:ℝ) ≤ quotientCost q*S.card ∧
  ∀Spre⊆S,∀Cpre : ℝ,0 < Cpre → (H.card:ℝ) ≤ Cpre*Spre.card →
  let Q3 := NativeSourceSizeBounds.radix Spre.card L3
  let F3 := refinementCost (d3+2) (J+1) L3
  let CX := (Cpre/quotientCost q)*fiberCoefficient D.thickness eta zeta tau c1 c2 lambda b F1 G Q2 F3 Q3 q ell
  ∃T,HasThirdXYSourceData (J:=J) D zeta a m plane E H Spre T P hP hell hell4 hd Fraw p
    population PL PU Q2 retain Cgraph Cpre t L3 Rel3 CX ∧
    ∀s∈T.image (fun z => translatedHeight D a m z.2),∀u∈T.image (fun z => translatedHeight D a m z.2),
      ‖field s-field u‖ ≤ (3*metric)*|referenceHeight m s-referenceHeight m u|


def HasXYParentProfiles {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
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
        HasPointSaturation (parentEdges D a (2^m) E2 p) (parentEdges D a (2^m) H p) ∧
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
                HasThirdXYFinish (J:=J) D eta zeta a q tau (seed/8) c2 lambda
                  ((W:ℝ)/(E2.card:ℝ)) F1 G Q2 m tuple E2 Hgraph P hP hell hell4 hd f p mu
                  (profileLower D.thickness mu (columnEpsilon D.thickness lambda (seed/8) c2)
                    tau (seed/8) (min (boundaryWindow tau) ((tau/16)/1000)))
                  (profileUpper D.thickness (columnEpsilon D.thickness lambda (seed/8) c2) tau)
                  retain (selectionCost Khalf)
                  (((cutEdges E2 points).card:ℝ)/(2*((((cutEdges E2 points).image
                    (mixedLabel D a m plane ell)).card):ℝ))) (r^(-2*epsilon)) L3 Rel)

end NativePostGraphXYHookData
