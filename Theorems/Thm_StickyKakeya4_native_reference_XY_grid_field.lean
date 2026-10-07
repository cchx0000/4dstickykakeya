import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_maps
import Theorems.Thm_StickyKakeya4_native_anisotropic_slice_labels

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeReferenceXYGridField
open Classical Finset StickyKakeya4 NativeReferenceXYGridLinear NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightSelection NativeTranslatedGrainHeightMetric
open NativeWeightedGrainQuotientGeometry NativeWeightedGrainQuotientFibers NativeGrainQuotientBins NativeGrainQuotientImage
open NativeHorizontalGrainSlice NativeHeightSlopeCoordinates NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeSpatialAngularGeometry NativeSquaredGrainQueries NativeOriginalPacketReference
open NativeAnisotropicShortRowGeometry
open scoped Matrix.Norms.Elementwise

lemma slice_horizontal (Q : Submodule ℝ E4) : sliceSpace Q≤heightKernel := fun _ hx => hx.2

/-- Chosen from the pre-third-core source ONCE, then defined on ALL reference
heights. In particular it does not depend on the later retained incidence set. -/
def fixedField {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (S : Finset (Fin n × Index))
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) :
    ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ :=
  totalField ((second D a m ell plane S).image (fun z => translatedHeight D a m z.2))
    (mapped D a m ell plane S Fraw)

lemma fixedField_norm {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (S : Finset (Fin n × Index))
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖Fraw t‖ ≤ (1/4:ℝ)) :
    ∀t,‖fixedField D a m ell plane S Fraw t‖ ≤ (1/4:ℝ) := by
  apply totalField_norm
  intro t _ht
  exact hF (rawAt D a m ell plane S t)

lemma fixedField_zero_off {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (S : Finset (Fin n × Index))
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (t : ℤ)
    (ht : t∉(second D a m ell plane S).image (fun z => translatedHeight D a m z.2)) :
    fixedField D a m ell plane S Fraw t=0 := totalField_off _ _ _ ht

lemma fixedField_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (S : Finset (Fin n × Index))
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (x : Fin n × Index) (hx : x∈second D a m ell plane S) :
    fixedField D a m ell plane S Fraw (translatedHeight D a m x.2)=Fraw (rawHeight D m x.2) := by
  rw [fixedField,totalField_on _ _ _ (mem_image_of_mem _ hx)]
  exact mapped_readback D a m ell plane S Fraw x hx

/-- The actual source XY map is recovered on every retained occurrence.
Off this source, fixedField remains bounded and height-only; no planarity
claim is made or needed there. -/
theorem fixed_pxy_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (plane : Index → Submodule ℝ E4) (S : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (Hread : ∀x∈second D a m ell plane S,Fraw (rawHeight D m x.2)=
      nodeSlope P hP ell hell hell4 hd (sliceSpace (plane (spatialLabel D (2^m) x.2)))
        (slice_horizontal (plane (spatialLabel D (2^m) x.2))))
    (x : Fin n × Index) (hx : x∈second D a m ell plane S) (hp : parentLabel D a (2^m) x.1=p) :
    pxy D a m ell p P hP hell hell4 hd (fixedField D a m ell plane S Fraw) x.2=
      (translatedHeight D a m x.2,(edgeX D a m ell P hd (mu m) x,
        quotientLabel D a m ell plane P hP hell hell4 hd (mu m) x)) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp only [pxy,edgeX,rawTangent,rawPoint,rawVertex,hp]
    · change label (mu m) (quotientMap P hP ell hell hell4 hd
        (fixedField D a m ell plane S Fraw (translatedHeight D a m x.2)) (rawPoint D a m p x.2))=_
      rw [fixedField_readback D a m ell plane S Fraw x hx,Hread x hx]
      have hnode := quotient_nodeSlope P (sliceSpace (plane (spatialLabel D (2^m) x.2))) hP
        (slice_horizontal (plane (spatialLabel D (2^m) x.2))) ell hell hell4 hd (rawPoint D a m p x.2)
      rw [hnode]
      simp only [quotientLabel,hp,NativeGrainQuotientBins.rawCoordinates,rawPoint,rawVertex]

lemma pref_squared {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (hm : 6 ≤ m) (p : Parent) (k : Index) :
    pref D a m p k=columnLabel D a (2^m) p ((rho m)^2) (rho m) k := by
  unfold pref sigma rho
  rw [squared_scale_identity m hm]

lemma coarseIndex_horizontalCoarsen (fine coarse : ℕ) (k : Index) :
    coarseIndex (2^(fine-coarse)) k=NativeAnisotropicSliceLabels.horizontalCoarsen fine coarse k := rfl

end NativeReferenceXYGridField
