import Theorems.Thm_StickyKakeya4_native_quotient_lattice_transport
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_field

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeQuotientFiberReadback
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open GridQuotientAD NativeTwoMapRetainedSliceLabels NativeQuotientLatticeTransport
open NativeReferenceXYGridField NativeReferenceXYGridMaps NativeReferenceXYGridPoints
open NativeTranslatedGrainHeightFibers NativeTranslatedGrainHeightSelection
open NativeTranslatedGrainHeightOverlap NativeWeightedGrainQuotientGeometry NativeWeightedGrainQuotientFibers
open NativeHorizontalGrainSlice NativeHeightSlopeCoordinates NativeOriginalParentSelection NativeSpatialAngularGeometry

/-- The quotient fiber contains precisely the distinct tangent labels at the
same height and quotient key. Repeated original incidences are counted once. -/
lemma product_fiber_image {A : Type*} {k l : ℕ} (T : Finset A) (f : A → XY k l)
    (height : ℤ) (y : GridQuotientAD.Lattice l) :
    (fiber (productSlice (T.image f) height) y).image Prod.fst=
      (T.filter (fun x => (f x).1=height ∧ (f x).2.2=y)).image (fun x => (f x).2.1) := by
  ext u
  simp only [fiber,productSlice,mem_image,mem_filter]
  constructor
  · rintro ⟨p,⟨⟨z,⟨⟨x,hx,rfl⟩,hh⟩,rfl⟩,hy⟩,rfl⟩
    exact ⟨x,⟨hx,hh,hy⟩,rfl⟩
  · rintro ⟨x,⟨hx,hh,hy⟩,rfl⟩
    exact ⟨(f x).2,⟨⟨f x,⟨⟨x,hx,rfl⟩,hh⟩,rfl⟩,hy⟩,rfl⟩

lemma product_fiber_card {A : Type*} {k l : ℕ} (T : Finset A) (f : A → XY k l)
    (height : ℤ) (y : GridQuotientAD.Lattice l) :
    (fiber (productSlice (T.image f) height) y).card=
      ((T.filter (fun x => (f x).1=height ∧ (f x).2.2=y)).image (fun x => (f x).2.1)).card := by
  rw [←product_fiber_image]
  symm
  apply card_image_iff.mpr
  intro p hp q hq he
  exact Prod.ext he ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm)

/-- The actual total height-only XY map has the exact same X fibers as the
previously constructed translated-key grain density endpoint. -/
theorem actual_referenceX_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (plane : Index → Submodule ℝ E4) (S T : Finset (Fin n × Index))
    (hT : T⊆second D a m ell plane S)
    (hp : ∀x∈T,parentLabel D a (2^m) x.1=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (Hread : ∀x∈second D a m ell plane S,Fraw (rawHeight D m x.2)=
      nodeSlope P hP ell hell hell4 hd (sliceSpace (plane (spatialLabel D (2^m) x.2)))
        (slice_horizontal (plane (spatialLabel D (2^m) x.2))))
    (height : ℤ) (y : GridQuotientAD.Lattice (4-ell)) :
    (fiber (productSlice (T.image (fun x => pxy D a m ell p P hP hell hell4 hd
      (fixedField D a m ell plane S Fraw) x.2)) height) y).card=
      (referenceX D a m ell plane T P hP hell hell4 hd (mu m) (height,y)).card := by
  rw [product_fiber_card]
  congr 1
  ext u
  simp only [referenceX,mem_image,mem_filter]
  constructor
  · rintro ⟨x,⟨hx,hh,hy⟩,hu⟩
    have hr := fixed_pxy_readback D a m ell p plane S P hP hell hell4 hd Fraw Hread x (hT hx) (hp x hx)
    rw [hr] at hh hy hu
    exact ⟨x,⟨hx,Prod.ext hh hy⟩,hu⟩
  · rintro ⟨x,⟨hx,hkey⟩,hu⟩
    have hr := fixed_pxy_readback D a m ell p plane S P hP hell hell4 hd Fraw Hread x (hT hx) (hp x hx)
    refine ⟨x,⟨hx,?_,?_⟩,?_⟩
    · rw [hr]
      exact congrArg Prod.fst hkey
    · rw [hr]
      exact congrArg Prod.snd hkey
    · rw [hr]
      exact hu

end NativeQuotientFiberReadback
