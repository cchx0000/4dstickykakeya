import Theorems.Thm_StickyKakeya4_native_quotient_lattice_transport
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_support
import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_actual_caps

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000
noncomputable section
namespace NativeActualQuotientSupport
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeQuotientLatticeTransport NativeReferenceXYGridMaps NativeReferenceXYGridPoints
open NativeReferenceXYGridSupport NativeOriginalParentSelection NativeCubicalIncidenceCounts
open NativeHorizontalGrainSlice NativeTwoMapRetainedSliceActualCaps
open scoped Matrix.Norms.Elementwise

/-- The actual same-parent incidence set gives both lattice support bounds;
no point support certificate is required. -/
theorem product_support {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level ell : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hf : NativeSquaredGrainQueries.phaseDepth m ≤ level)
    (p : Parent) (T : Finset (Fin n × Index)) (hT : T⊆incidences original)
    (hp : ∀x∈T,parentLabel D a (2^m) x.1=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (height : ℤ) :
    let A := productSlice (T.image (fun x => pxy D a m ell p P hP hell hell4 hd F x.2)) height
    (∀z∈A,∀j,|z.1 j| ≤ (halfWidth m:ℤ)) ∧
    (∀z∈A,∀j,|z.2 j| ≤ ((2*halfWidth m:ℕ):ℤ)) := by
  dsimp only
  have hbound : ∀z∈productSlice (T.image (fun x => pxy D a m ell p P hP hell hell4 hd F x.2)) height,
      (∀j,|z.1 j| ≤ (halfWidth m:ℤ)) ∧ (∀j,|z.2 j| ≤ ((2*halfWidth m:ℕ):ℤ)) := by
    intro z hz
    simp only [productSlice,mem_image,mem_filter] at hz
    obtain ⟨u,⟨⟨x,hx,rfl⟩,_hh⟩,rfl⟩ := hz
    exact dyadic_pxy_support h original horiginal ha m level hm hdy hf p x.1 x.2 (hT hx)
      (hp x hx) P hP ell hell hell4 hd F hF
  exact ⟨fun z hz => (hbound z hz).1,fun z hz => (hbound z hz).2⟩

lemma encoded_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (T : Finset (Fin n × Index)) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) :
    (T.image (fun x => pxy D a m ell p P hP hell hell4 hd F x.2)).image
        (NativeTwoMapRetainedSliceLabels.encode (dimension_sum ell hell hell4))=
      T.image (fun x => encodedPoint D a m ell p P hP hell hell4 hd F x.2) := by
  rw [image_image]
  rfl

lemma halfWidth_pos (m : ℕ) : 1 ≤ halfWidth m := by
  unfold halfWidth
  exact Nat.succ_le_of_lt (by positivity)

lemma quotient_exponent (ell : ℕ) (hell : 1 ≤ ell) (kappa : ℝ) :
    (3-kappa)-((ell-1:ℕ):ℝ)=4-(ell:ℝ)-kappa := by
  rw [Nat.cast_sub hell,Nat.cast_one]
  ring

end NativeActualQuotientSupport
