import Theorems.Thm_StickyKakeya4_native_parent_local_XY_grain_core
import Theorems.Thm_StickyKakeya4_native_quotient_fiber_readback
import Theorems.Thm_StickyKakeya4_native_translated_grain_height_chart

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
noncomputable section
namespace NativeThirdXYData
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore
open NativeJointUniformCoarseRelations NativeSquaredGrainQueries NativeRetainedSliceCore
open NativeReferenceColumnExponents NativeSliceADConstant NativeAnisotropicSliceLabels
open NativeParentGrainIncidenceCleanup NativeSpatialAngularGeometry NativeHorizontalGrainSlice
open NativeTranslatedGrainHeightSelection NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightFibers
open NativeGrainQuotientFibers NativeReferenceXYGridField NativeReferenceXYGridPoints
open NativeTwoMapRetainedSliceActualCaps NativeSliceClassBalls NativeFixedCompactKakeyaExponent
open FiniteVoronoiRealADCoarsening SelfUniform
open scoped Matrix.Norms.Elementwise

/-- Explicit constant of the actual two-map ambient AD endpoint. -/
def xyConstant (delta zeta population profileLower profileUpper lambda loss : ℝ)
    (Qref Q3 J m : ℕ) : ℝ :=
  let low := lowerCountCoefficient delta zeta population profileUpper
  let up := upperCountCoefficient delta zeta profileLower
  let Ci : ℝ := ((201^3:ℕ):ℝ)
  let Cf : ℝ := ((1201^3:ℕ):ℝ)
  let gap : ℝ := max 64 ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)
  constant (lambda*(low/up)/(loss*(Qref:ℝ)^2*Ci*Cf*(Q3:ℝ)^4))
    ((27*Cf)*(Cf*Ci*((Qref:ℝ)^4*up/low))) gap (3-extremalExponent)

lemma xyConstant_one_le (delta zeta population profileLower profileUpper lambda loss : ℝ)
    (Qref Q3 J m : ℕ) :
    1 ≤ xyConstant delta zeta population profileLower profileUpper lambda loss Qref Q3 J m :=
  one_le_constant _ _ _ _

/-- Reusable Finish data for one and the same third core. The pre-third S
may already carry any independently paid whole-point coherence cut. -/
def HasThirdXYData {n d J ell : ℕ} (D : FiniteScaleSource n) (zeta a : ℝ) (m : ℕ)
    (plane : Index → Submodule ℝ E4) (E Hgraph S T : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (p : Parent) (population profileLower profileUpper : ℝ) (Qref : ℕ)
    (lambda G Cpre t : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) : Prop :=
  let mu := physicalMesh m (phaseDepth m)/8
  let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell plane Hgraph P hP hell hell4 hd mu
  let field := fixedField D a m ell plane Sq Fraw
  let xy := fun z : Fin n × Index => encodedPoint D a m ell p P hP hell hell4 hd field z.2
  let grain := mixedLabel D a m plane ell
  let key := referenceKey D a m ell plane P hP hell hell4 hd mu
  let Q3 := NativeSourceSizeBounds.radix S.card L3
  let F3 := refinementCost (d+2) (J+1) L3
  let KXY := xyConstant D.thickness zeta population profileLower profileUpper lambda
    (G*Cpre*(F3:ℝ)) Qref Q3 J m
  T⊆S ∧ T.Nonempty ∧ S.card ≤ F3*T.card ∧ T⊆Hgraph ∧
    (Hgraph.card:ℝ) ≤ Cpre*(F3:ℝ)*T.card ∧
    (∀j x y,x∈T → y∈T → degree (fun _ : Fin n × Index => 1) (Rel j) T x ≤
      Q3^2*degree (fun _ : Fin n × Index => 1) (Rel j) T y) ∧
    HasUniformFibers T Q3 Prod.snd ∧ HasUniformFibers T Q3 xy ∧
    (∀j,HasUniformFibers T Q3 (fun z => horizontalCoarsen (phaseDepth m)
      (NativeFixedHorizontalMenu.depths J m j) (xy z))) ∧
    HasUniformFibers T Q3 grain ∧
    (∀x y,x∈T → y∈T → grain x=grain y → key x=key y) ∧
    (∀x∈T,t ≤ Cpre*(F3:ℝ)*(Q3:ℝ)^2*(mixedFiber D a m plane ell T (grain x)).card) ∧
    (lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ (G*Cpre*(F3:ℝ))*T.card) ∧
    (∀height : ℤ,ADBounds (realizedSlice (T.image xy) (NativeReferenceXYGridPoints.mu m) height)
      (NativeReferenceXYGridPoints.mu m) KXY (3-extremalExponent)) ∧
    (∀x∈T,field (translatedHeight D a m x.2)=Fraw (rawHeight D m x.2)) ∧
    (∀height,‖field height‖ ≤ (1/4:ℝ))

end NativeThirdXYData
