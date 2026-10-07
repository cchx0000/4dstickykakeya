import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_caps
import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_labels

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 11000000

noncomputable section
namespace NativeTwoMapRetainedSliceActualCaps
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeHorizontalGrainSlice NativeReferenceXYGridLinear NativeReferenceXYGridPoints
open NativeReferenceXYGridMaps NativeReferenceXYGridCaps NativeAnisotropicSliceLabels
open NativeTwoMapRetainedSliceLabels
open scoped Matrix.Norms.Elementwise

lemma dimension_sum (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) : (ell-1)+(4-ell)=3 := by omega

def encodedPoint {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (k : Index) : Index :=
  encode (dimension_sum ell hell hell4) (pxy D a m ell p P hP hell hell4 hd F k)

lemma encodedPoint_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (k : Index) :
    encodedPoint D a m ell p P hP hell hell4 hd F k (3:Fin 4)=pref D a m p k (3:Fin 4) := by
  rw [encodedPoint,encode_height]
  exact pxy_height D a m ell p P hP hell hell4 hd F k

lemma encodedPoint_coarse {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (fine depth : ℕ) (k : Index) :
    horizontalCoarsen fine depth (encodedPoint D a m ell p P hP hell hell4 hd F k)=
      encode (dimension_sum ell hell hell4)
        (coarseXY ell (2^(fine-depth)) (pxy D a m ell p P hP hell hell4 hd F k)) :=
  (encode_coarse (dimension_sum ell hell hell4) fine depth _).symm

lemma image_composed_encode_card {A : Type*} {a b : ℕ} (hd : a+b=3)
    (I : Finset A) (f : A → NativeTwoMapRetainedSliceLabels.XY a b) :
    (I.image (fun x => encode hd (f x))).card=(I.image f).card := by
  have hh := image_encode_card hd (I.image f)
  simpa only [image_image,Function.comp_def] using hh

/-- All finite two-map capacities are derived for the encoded actual XY
coordinates on any reference incidence set. F is one fixed total bounded
height field; no off-core plane or XY-uniformity premise is introduced. -/
theorem encoded_capacities {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (I : Finset (Fin n × Index)) :
    let ref := fun z : Fin n × Index => pref D a m p z.2
    let xy := fun z : Fin n × Index => encodedPoint D a m ell p P hP hell hell4 hd F z.2
    (∀z∈I.image xy,((I.filter (fun x => xy x=z)).image ref).card ≤ 201^3) ∧
    (∀z∈I.image ref,((I.filter (fun x => ref x=z)).image xy).card ≤ 1201^3) ∧
    ∀fine depth : ℕ,
      (∀z∈(I.image ref).image (horizontalCoarsen fine depth),
        ((I.filter (fun x => horizontalCoarsen fine depth (ref x)=z)).image
          (fun x => horizontalCoarsen fine depth (xy x))).card ≤ 1201^3) ∧
      (∀z∈I.image (fun x => horizontalCoarsen fine depth (xy x)),
        ((I.filter (fun x => horizontalCoarsen fine depth (xy x)=z)).image
          (fun x => horizontalCoarsen fine depth (ref x))).card ≤ 201^3) := by
  intro ref xy
  let rawxy := fun z : Fin n × Index => pxy D a m ell p P hP hell hell4 hd F z.2
  let hdim := dimension_sum ell hell hell4
  refine ⟨?_,?_,?_⟩
  · intro z hz
    obtain ⟨v,_hv,rfl⟩ := mem_image.mp hz
    have he : I.filter (fun x => xy x=xy v)=I.filter (fun x => rawxy x=rawxy v) := by
      apply filter_congr
      intro x _hx
      exact (encode_injective hdim).eq_iff
    rw [he]
    exact lift_incidence_capacity I Prod.snd (pxy D a m ell p P hP hell hell4 hd F) (pref D a m p)
      (201^3) (fun S z => fine_inverse_capacity h m ell hm p i hi P hP hell hell4 hd F hF S z) (rawxy v)
  · intro z _hz
    change ((I.filter (fun x => ref x=z)).image (fun x => encode hdim (rawxy x))).card ≤ _
    rw [image_composed_encode_card]
    exact lift_incidence_capacity I Prod.snd (pref D a m p) (pxy D a m ell p P hP hell hell4 hd F)
      (1201^3) (fun S z => fine_forward_capacity h m ell hm p i hi P hP hell hell4 hd F hF S z) z
  · intro fine depth
    let R := 2^(fine-depth)
    have hR : 0 < R := by dsimp [R]; positivity
    have hcomm (x : Fin n × Index) : horizontalCoarsen fine depth (xy x)=
        encode hdim (coarseXY ell R (rawxy x)) :=
      encodedPoint_coarse D a m ell p P hP hell hell4 hd F fine depth x.2
    constructor
    · intro z _hz
      have he : (I.filter (fun x => horizontalCoarsen fine depth (ref x)=z)).image
          (fun x => horizontalCoarsen fine depth (xy x))=
          (I.filter (fun x => horizontalCoarsen fine depth (ref x)=z)).image
            (fun x => encode hdim (coarseXY ell R (rawxy x))) := by
        apply image_congr
        intro x _hx
        exact hcomm x
      rw [he,image_composed_encode_card]
      exact lift_incidence_capacity I Prod.snd (fun k => coarseIndex R (pref D a m p k))
        (fun k => coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k)) (1201^3)
        (fun S z => forward_capacity h m ell hm p i hi P hP hell hell4 hd F hF R hR S z) z
    · intro z hz
      obtain ⟨v,_hv,rfl⟩ := mem_image.mp hz
      have he : I.filter (fun x => horizontalCoarsen fine depth (xy x)=horizontalCoarsen fine depth (xy v))=
          I.filter (fun x => coarseXY ell R (rawxy x)=coarseXY ell R (rawxy v)) := by
        apply filter_congr
        intro x _hx
        rw [hcomm x,hcomm v]
        exact (encode_injective hdim).eq_iff
      rw [he]
      exact lift_incidence_capacity I Prod.snd
        (fun k => coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k))
        (fun k => coarseIndex R (pref D a m p k)) (201^3)
        (fun S z => inverse_capacity h m ell hm p i hi P hP hell hell4 hd F hF R hR S z)
        (coarseXY ell R (rawxy v))

end NativeTwoMapRetainedSliceActualCaps
