import Theorems.Thm_StickyKakeya4_native_encoded_quotient_ad
import Theorems.Thm_StickyKakeya4_native_actual_quotient_density
import Theorems.Thm_StickyKakeya4_native_actual_quotient_support
import Theorems.Thm_StickyKakeya4_native_fixed_compact_kakeya_exponent

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
namespace NativeActualQuotientAD
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeQuotientLatticeTransport NativeQuotientFiberReadback GridQuotientAD
open NativeReferenceXYGridMaps NativeReferenceXYGridPoints NativeReferenceXYGridField NativeReferenceXYGridSupport
open NativeTranslatedGrainHeightFibers NativeTranslatedGrainHeightSelection NativeTranslatedGrainHeightOverlap
open NativeHorizontalGrainSlice NativeHeightSlopeCoordinates NativeOriginalParentSelection NativeSpatialAngularGeometry
open NativeActualQuotientDensity NativeActualQuotientSupport NativeEncodedQuotientAD
open NativeTwoMapRetainedSliceActualCaps NativeSliceClassBalls NativeCubicalIncidenceCounts
open NativeFixedCompactKakeyaExponent
open scoped Matrix.Norms.Elementwise

/-- Geometric consumer of the existing sharp source cross bound. All point
sets remain literal images of the prescribed third core T. The source caller
supplies HX by the already proved original-incidence/history theorem. -/
theorem of_reference_cross {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level ell : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hf : NativeSquaredGrainQueries.phaseDepth m ≤ level)
    (p : Parent) (plane : Index → Submodule ℝ E4) (S T : Finset (Fin n × Index))
    (hT : T⊆second D a m ell plane S) (hTn : T.Nonempty)
    (hTI : T⊆incidences original) (hp : ∀x∈T,parentLabel D a (2^m) x.1=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (hdimension : extremalExponent+(ell:ℝ) ≤ 4)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hFraw : ∀t,‖Fraw t‖ ≤ (1/4:ℝ))
    (Hread : ∀x∈second D a m ell plane S,Fraw (rawHeight D m x.2)=
      nodeSlope P hP ell hell hell4 hd (sliceSpace (plane (spatialLabel D (2^m) x.2)))
        (slice_horizontal (plane (spatialLabel D (2^m) x.2))))
    (C KXY : ℝ) (hKXY : 0 < KXY)
    (HX : ∀x∈T,(rho m)^(-((ell:ℝ)-1)) ≤ C*
      (referenceX D a m ell plane T P hP hell hell4 hd (mu m)
        (referenceKey D a m ell plane P hP hell hell4 hd (mu m) x)).card)
    (HXY : ∀height : ℤ,FiniteVoronoiRealADCoarsening.ADBounds
      (realizedSlice (T.image (fun x => encodedPoint D a m ell p P hP hell hell4 hd
        (fixedField D a m ell plane S Fraw) x.2)) (mu m) height) (mu m) KXY (3-extremalExponent)) :
    0 < C ∧ ∀height : ℤ,FiniteVoronoiRealADCoarsening.ADBounds
      (((productSlice (T.image (fun x => pxy D a m ell p P hP hell hell4 hd
        (fixedField D a m ell plane S Fraw) x.2)) height).image Prod.snd).image
          (NativeQuotientGridCenters.center (mu m)))
      (mu m) (quotientConstant (ell-1) (4-ell) (1/((32:ℝ)^(ell-1)*C)) KXY (3-extremalExponent))
      (4-(ell:ℝ)-extremalExponent) := by
  have hdense := reference_cross_dense D a m ell (by omega) p plane S T hT hTn hp P hP hell hell4 hd Fraw Hread C HX
  have hC : 0 < C := hdense.1
  have hlam : 0 < 1/((32:ℝ)^(ell-1)*C) := by positivity
  refine ⟨hC,?_⟩
  intro height
  have hsupport := product_support h original horiginal ha m level ell hm hdy hf p T hTI hp
    P hP hell hell4 hd (fixedField D a m ell plane S Fraw) (fixedField_norm D a m ell plane S Fraw hFraw) height
  have hdim := dimension_sum ell hell hell4
  have hk : ((ell-1:ℕ):ℝ) ≤ 3-extremalExponent := by
    rw [Nat.cast_sub hell,Nat.cast_one]
    linarith only [hdimension]
  have ht : 3-extremalExponent ≤ (((ell-1)+(4-ell):ℕ):ℝ) := by
    rw [hdim]
    norm_num only [Nat.cast_ofNat]
    linarith only [extremalExponent_nonneg]
  have hxy := HXY height
  rw [←encoded_image D a m ell p T P hP hell hell4 hd
    (fixedField D a m ell plane S Fraw)] at hxy
  have hh := quotient_AD_of_encoded_AD (k:=ell-1) (l:=4-ell) hdim
    (T.image (fun x => pxy D a m ell p P hP hell hell4 hd (fixedField D a m ell plane S Fraw) x.2))
    height (halfWidth m) (halfWidth_pos m) (mu:=mu m)
    (lam:=1/((32:ℝ)^(ell-1)*C)) (K:=KXY) (t:=3-extremalExponent) (mu_pos m) hlam hKXY
    (mu_halfWidth m (by omega)) hk ht hsupport.1 hsupport.2 (hdense.2 height) hxy
  rw [←quotient_exponent ell hell extremalExponent]
  exact hh.2

end NativeActualQuotientAD
