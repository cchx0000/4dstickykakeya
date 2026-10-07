import Theorems.Thm_StickyKakeya4_native_window_quotient_global_count
import Theorems.Thm_StickyKakeya4_native_encoded_quotient_ad
import Theorems.Thm_StickyKakeya4_native_actual_quotient_density
import Theorems.Thm_StickyKakeya4_native_actual_quotient_support
import Theorems.Thm_StickyKakeya4_native_fixed_compact_kakeya_exponent

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
namespace NativeActualWindowGlobalCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeQuotientLatticeTransport NativeQuotientFiberReadback GridQuotientAD
open NativeReferenceXYGridMaps NativeReferenceXYGridPoints NativeReferenceXYGridField NativeReferenceXYGridSupport
open NativeTranslatedGrainHeightFibers NativeTranslatedGrainHeightSelection NativeTranslatedGrainHeightOverlap
open NativeHorizontalGrainSlice NativeHeightSlopeCoordinates NativeOriginalParentSelection NativeSpatialAngularGeometry
open NativeActualQuotientDensity NativeActualQuotientSupport NativeEncodedQuotientAD
open NativeTwoMapRetainedSliceActualCaps NativeSliceClassBalls NativeCubicalIncidenceCounts
open NativeFixedCompactKakeyaExponent
open scoped Matrix.Norms.Elementwise

open NativeWindowXYLabels NativeWindowQuotientTransport NativeTwoMapRetainedSliceLabels
open NativeWindowQuotientGlobalCount

/-- The source X bound and actual support give the whole coarse-window
quotient count with its existing quotient AD constant. -/
theorem of_reference_cross {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level ell f : ℕ) (hm : 12 ≤ m) (hmf : m ≤ f) (hfb : f ≤ NativeSquaredGrainQueries.phaseDepth m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
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
      (realizedSlice
        (((T.image (fun x => pxy D a m ell p P hP hell hell4 hd
          (fixedField D a m ell plane S Fraw) x.2)).image
            (window (8*factor m f) (factor m f))).image (encode (dimension_sum ell hell hell4)))
        (mu m*(factor m f:ℝ)) height) (mu m*(factor m f:ℝ)) KXY (3-extremalExponent)) :
    0 < C ∧ ∀height : ℤ,
      (((productSlice
        ((T.image (fun x => pxy D a m ell p P hP hell hell4 hd
          (fixedField D a m ell plane S Fraw) x.2)).image (window (8*factor m f) (factor m f)))
        height).image Prod.snd).card:ℝ) ≤
      (quotientConstant (ell-1) (4-ell) (1/((32:ℝ)^(ell-1)*C)) KXY (3-extremalExponent))*
        (windowHalfWidth m f:ℝ)^(4-(ell:ℝ)-extremalExponent) := by
  have hdense := reference_cross_dense D a m ell (by omega) p plane S T hT hTn hp P hP hell hell4 hd Fraw Hread C HX
  have hC : 0 < C := hdense.1
  have hlam : 0 < 1/((32:ℝ)^(ell-1)*C) := by positivity
  let W := T.image (fun x => pxy D a m ell p P hP hell hell4 hd
    (fixedField D a m ell plane S Fraw) x.2)
  have hmem (z) (hz : z∈W) : z.2∈productSlice W z.1 :=
    mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,rfl⟩,rfl⟩
  have hsup (z) (hz : z∈W) := product_support h original horiginal ha m level ell hm hdy hf p T hTI hp
    P hP hell hell4 hd (fixedField D a m ell plane S Fraw) (fixedField_norm D a m ell plane S Fraw hFraw) z.1
  have hx : ∀z∈W,∀j,|z.2.1 j| ≤ (halfWidth m:ℤ) := by
    intro z hz j
    exact (hsup z hz).1 z.2 (hmem z hz) j
  have hy : ∀z∈W,∀j,|z.2.2 j| ≤ ((2*halfWidth m:ℕ):ℤ) := by
    intro z hz j
    exact (hsup z hz).2 z.2 (hmem z hz) j
  have hden : ∀z∈W,(1/((32:ℝ)^(ell-1)*C))*(halfWidth m:ℝ)^(ell-1) ≤
      ((fiber (productSlice W z.1) z.2.2).card:ℝ) := by
    intro z hz
    exact hdense.2 z.1 z.2.2 (mem_image_of_mem Prod.snd (hmem z hz))
  have hdim := dimension_sum ell hell hell4
  have hk : ((ell-1:ℕ):ℝ) ≤ 3-extremalExponent := by
    rw [Nat.cast_sub hell,Nat.cast_one]
    linarith only [hdimension]
  have hfactor : 0 < factor m f := by unfold factor; positivity
  have hwidth : 1 ≤ windowHalfWidth m f := Nat.one_le_pow _ _ (by norm_num)
  have HH := window_global_count hdim W (8*factor m f) (factor m f) (halfWidth m) (windowHalfWidth m f)
    hfactor (width_factorization m f (by omega) hmf hfb) hwidth
    (mu_pos m) hlam hKXY (mu_halfWidth m (by omega)) hk hx hy hden HXY
  refine ⟨hC,?_⟩
  intro height
  rw [←quotient_exponent ell hell extremalExponent]
  exact HH height

end NativeActualWindowGlobalCount
