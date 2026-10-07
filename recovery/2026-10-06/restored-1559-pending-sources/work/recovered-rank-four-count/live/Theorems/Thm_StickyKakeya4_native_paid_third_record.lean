import Theorems.Thm_StickyKakeya4_native_paid_third_data
import Theorems.Thm_StickyKakeya4_native_actual_quotient_ad
import Theorems.Thm_StickyKakeya4_native_quotient_constant_bound

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
noncomputable section
namespace NativePaidThirdRecord
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeJointUniformCoarseRelations NativeSquaredGrainQueries NativeRetainedSliceCore
open NativeParentGrainIncidenceCleanup NativeSpatialAngularGeometry NativeHorizontalGrainSlice
open NativeTranslatedGrainHeightSelection NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightFibers
open NativeGrainQuotientFibers NativeReferenceXYGridField NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeThirdXYData NativeQuotientLatticeTransport NativeEncodedQuotientAD NativeFixedCompactKakeyaExponent
open FiniteVoronoiRealADCoarsening
open scoped Matrix.Norms.Elementwise

open NativeThirdXYSourceData NativeTwoMapRetainedSliceActualCaps NativeSliceClassBalls

/-- Paid regularity and density on the same third incidence set, retaining
all of its original source data and the explicit pre-refinement multiplier. -/
def HasPaidThirdXYSourceData {n d J ell : ℕ} (D : FiniteScaleSource n) (zeta a : ℝ) (m : ℕ)
    (plane : Index → Submodule ℝ E4) (E Hgraph S T : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (p : Parent) (population profileLower profileUpper : ℝ) (Qref : ℕ)
    (lambda G Cpre t : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) (CX epsilonPaid M : ℝ) : Prop :=
  let mu := physicalMesh m (phaseDepth m)/8
  let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell plane Hgraph P hP hell hell4 hd mu
  let field := fixedField D a m ell plane Sq Fraw
  let Q3 := NativeSourceSizeBounds.radix S.card L3
  let F3 := refinementCost (d+2) (J+1) L3
  let KXY := xyConstant D.thickness zeta population profileLower profileUpper lambda
    (G*Cpre*(F3:ℝ)) Qref Q3 J m
  let KY := quotientConstant (ell-1) (4-ell) (1/((32:ℝ)^(ell-1)*CX)) KXY (3-extremalExponent)
  let rho := NativeReferenceXYGridPoints.rho m
  let xy := fun z : Fin n × Index => encodedPoint D a m ell p P hP hell hell4 hd field z.2
  HasThirdXYSourceData (J:=J) D zeta a m plane E Hgraph S T P hP hell hell4 hd Fraw p
      population profileLower profileUpper Qref lambda G Cpre t L3 Rel CX ∧
    1 ≤ M ∧ KXY ≤ M*rho^(-(epsilonPaid/2)) ∧ KY ≤ M^2*rho^(-epsilonPaid) ∧
    (∀height : ℤ,ADBounds (realizedSlice (T.image xy) (NativeReferenceXYGridPoints.mu m) height)
      (NativeReferenceXYGridPoints.mu m) (M*rho^(-(epsilonPaid/2))) (3-extremalExponent)) ∧
    (∀height : ℤ,ADBounds
      (((productSlice (T.image (fun z => pxy D a m ell p P hP hell hell4 hd field z.2)) height).image
        Prod.snd).image (NativeQuotientGridCenters.center (NativeReferenceXYGridPoints.mu m)))
      (NativeReferenceXYGridPoints.mu m) (M^2*rho^(-epsilonPaid)) (4-(ell:ℝ)-extremalExponent)) ∧
    ∀x∈T,rho^(epsilonPaid/4)*rho^(-((ell:ℝ)-1)) ≤ M*
      (referenceX D a m ell plane T P hP hell hell4 hd mu
        (referenceKey D a m ell plane P hP hell hell4 hd mu x)).card

end NativePaidThirdRecord
