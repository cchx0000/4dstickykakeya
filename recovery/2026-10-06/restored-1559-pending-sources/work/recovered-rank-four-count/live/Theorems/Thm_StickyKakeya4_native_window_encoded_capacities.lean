import Theorems.Thm_StickyKakeya4_native_window_XY_source_caps
import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_actual_caps

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeWindowEncodedCapacities
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeSquaredGrainQueries
open NativeReferenceXYGridLinear NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeWindowXYReferenceMaps NativeWindowXYMetric NativeWindowXYLabels NativeWindowXYSourceCaps
open NativeHorizontalGrainSlice NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric
open NativeOffsetAngularGeometry NativeAnisotropicShortRowGeometry NativeAnisotropicSliceLabels
open NativeTwoMapRetainedSliceLabels NativeTwoMapRetainedSliceActualCaps
open scoped Matrix.Norms.Elementwise

/-- The reference column at space g in the physical f-window. -/
def referencePoint {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f g : ℕ)
    (p : Parent) (k : Index) : Index :=
  columnLabel D a (2^m) p (64/((2^g:ℕ):ℝ)) (64/((2^(f-m+3):ℕ):ℝ)) k

/-- The literal varying-field XY image at space g in that same window. -/
def xyPoint {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell f g : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (k : Index) : Index :=
  encode (dimension_sum ell hell hell4)
    (window (8*2^(phaseDepth m-f)) (2^(phaseDepth m-g)) (pxy D a m ell p P hP hell hell4 hd F k))

lemma referencePoint_coarsen {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f g : ℕ)
    (hgf : g ≤ f) (p : Parent) (k : Index) :
    horizontalCoarsen f g (referencePoint D a m f f p k)=referencePoint D a m f g p k :=
  columnLabel_horizontalCoarsen D a (2^m) (by positivity) p _ f g hgf k

lemma xyPoint_coarsen {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell f g : ℕ)
    (hgf : g ≤ f) (hfb : f ≤ phaseDepth m) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (k : Index) :
    horizontalCoarsen f g (xyPoint D a m ell f f p P hP hell hell4 hd F k)=
      xyPoint D a m ell f g p P hP hell hell4 hd F k := by
  unfold xyPoint
  rw [encode_window_coarse,←pow_add,show phaseDepth m-f+(f-g)=phaseDepth m-g by omega]

lemma xyPoint_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell f g : ℕ)
    (hm : 6 ≤ m) (hmf : m ≤ f) (hgf : g ≤ f) (hfb : f ≤ phaseDepth m) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (k : Index) :
    xyPoint D a m ell f g p P hP hell hell4 hd F k (3:Fin 4)=referencePoint D a m f g p k (3:Fin 4) := by
  unfold xyPoint referencePoint
  rw [encode_height,window_height,pxy_height,
    ←scheduled_reference_readback D a m f g hm hmf hgf hfb p k,windowIndex_height]

/-- All four encoded capacities follow from the proved actual geometric
window caps on this same supported incidence set. -/
theorem encoded_capacities {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : phaseDepth m ≤ level)
    (p : Parent) (I : Finset (Fin n × Index)) (hI : I⊆incidences original)
    (hp : ∀z∈I,parentLabel D a (2^m) z.1=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀z∈I,‖F (translatedHeight D a m z.2)‖ ≤ (1/4:ℝ))
    (hLip : ∀z∈I,∀w∈I,‖F (translatedHeight D a m z.2)-F (translatedHeight D a m w.2)‖ ≤
      L*|referenceHeight m (translatedHeight D a m z.2)-referenceHeight m (translatedHeight D a m w.2)|)
    (f : ℕ) (hmf : m ≤ f) (hfb : f ≤ phaseDepth m) :
    let ref := fun z : Fin n × Index => referencePoint D a m f f p z.2
    let xy := fun z : Fin n × Index => xyPoint D a m ell f f p P hP hell hell4 hd F z.2
    let C := (2*menuRadius L+1)^3
    (∀z∈I.image xy,((I.filter (fun x => xy x=z)).image ref).card ≤ C) ∧
    (∀z∈I.image ref,((I.filter (fun x => ref x=z)).image xy).card ≤ C) ∧
    ∀g : ℕ,g ≤ f →
      (∀z∈(I.image ref).image (horizontalCoarsen f g),
        ((I.filter (fun x => horizontalCoarsen f g (ref x)=z)).image
          (fun x => horizontalCoarsen f g (xy x))).card ≤ C) ∧
      (∀z∈I.image (fun x => horizontalCoarsen f g (xy x)),
        ((I.filter (fun x => horizontalCoarsen f g (xy x)=z)).image
          (fun x => horizontalCoarsen f g (ref x))).card ≤ C) := by
  intro ref xy C
  let rawxy (g : ℕ) := fun z : Fin n × Index => window (8*2^(phaseDepth m-f)) (2^(phaseDepth m-g))
    (pxy D a m ell p P hP hell hell4 hd F z.2)
  let hdim := dimension_sum ell hell hell4
  have hcaps (g : ℕ) (hgf : g ≤ f) := scheduled_window_capacities h original horiginal ha level m hm hdy hf
    p I hI hp P hP ell hell hell4 hd F L hL hF hLip f g hmf hgf hfb
  refine ⟨?_,?_,?_⟩
  · intro z hz
    obtain ⟨v,_hv,rfl⟩ := mem_image.mp hz
    have he : I.filter (fun x => xy x=xy v)=I.filter (fun x => rawxy f x=rawxy f v) := by
      apply filter_congr
      intro x _hx
      exact (encode_injective hdim).eq_iff
    rw [he]
    exact (hcaps f le_rfl).1 (rawxy f v)
  · intro z _hz
    change ((I.filter (fun x => ref x=z)).image (fun x => encode hdim (rawxy f x))).card ≤ C
    rw [image_composed_encode_card]
    exact (hcaps f le_rfl).2 z
  · intro g hgf
    have hcomm (x : Fin n × Index) : horizontalCoarsen f g (xy x)=encode hdim (rawxy g x) :=
      xyPoint_coarsen D a m ell f g hgf hfb p P hP hell hell4 hd F x.2
    have href (x : Fin n × Index) : horizontalCoarsen f g (ref x)=referencePoint D a m f g p x.2 :=
      referencePoint_coarsen D a m f g hgf p x.2
    constructor
    · intro z _hz
      simp only [hcomm,href,image_composed_encode_card]
      exact (hcaps g hgf).2 z
    · intro z hz
      obtain ⟨v,_hv,rfl⟩ := mem_image.mp hz
      have he : I.filter (fun x => horizontalCoarsen f g (xy x)=horizontalCoarsen f g (xy v))=
          I.filter (fun x => rawxy g x=rawxy g v) := by
        apply filter_congr
        intro x _hx
        rw [hcomm x,hcomm v]
        exact (encode_injective hdim).eq_iff
      rw [he]
      simp only [href]
      exact (hcaps g hgf).1 (rawxy g v)

end NativeWindowEncodedCapacities
