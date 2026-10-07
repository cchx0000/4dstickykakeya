import Theorems.Thm_StickyKakeya4_native_translated_grain_height_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeTranslatedGrainHeightFibers
open Classical Finset StickyKakeya4 NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightSelection
open NativeWeightedGrainQuotientGeometry NativeWeightedGrainQuotientFibers NativeWeightedGrainQuotientHereditary
open NativeGrainQuotientFibers NativeHorizontalGrainSlice NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeSquaredGrainQueries NativeParentGrainIncidenceCleanup NativeSpatialAngularGeometry RichDirectionalLayers
open NativeAnisotropicShortRowGeometry

/-- The final key uses the ACTUAL translated reference height. -/
def referenceKey {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (z : Fin n × Index) : ℤ × (Fin (4-ell) → ℤ) :=
  (translatedHeight D a m z.2,quotientLabel D a m ell plane P hP hell hell4 hd mu z)

/-- All actual tangent bins on the SAME later H3 at a reference key. -/
def referenceX {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H3 : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (b : ℤ × (Fin (4-ell) → ℤ)) : Finset (Fin (ell-1) → ℤ) :=
  (H3.filter (fun z => referenceKey D a m ell plane P hP hell hell4 hd mu z=b)).image
    (edgeX D a m ell P hd mu)

lemma referenceKey_column {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell N : ℕ)
    (plane : Index → Submodule ℝ E4) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (p : Parent) (sigma : ℝ) (z : Fin n × Index) :
    referenceKey D a m ell plane P hP hell hell4 hd mu z=
      (columnLabel D a N p sigma (64/((2^m:ℕ):ℝ)) z.2 (3:Fin 4),
        quotientLabel D a m ell plane P hP hell hell4 hd mu z) :=
  Prod.ext (translatedHeight_column D a m N p sigma z.2) rfl

/-- Same old mixed grain means same ACTUAL translated key after the two
weighted height cuts, even after the later H3 refinement. -/
lemma mixed_reference_key_eq {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H H3 : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (h3 : H3⊆second D a m ell plane (retained D a m ell plane H P hP hell hell4 hd mu))
    (c : Parent × (Index × Index)) (x y : Fin n × Index)
    (hx : x∈mixedFiber D a m plane ell H3 c) (hy : y∈mixedFiber D a m plane ell H3 c) :
    referenceKey D a m ell plane P hP hell hell4 hd mu x=
      referenceKey D a m ell plane P hP hell hell4 hd mu y := by
  have hx3 := hx
  have hy3 := hy
  simp only [mixedFiber,classFiber,mem_filter] at hx3 hy3
  have hg := hx3.2.trans hy3.2.symm
  have ht := (hereditary_alignment D a m ell plane _ H3 h3).2 x y hx3.1 hy3.1 hg
  have h3S := h3.trans (second_subset D a m ell plane _)
  have hxS : x∈mixedFiber D a m plane ell (retained D a m ell plane H P hP hell hell4 hd mu) c := by
    simp only [mixedFiber,classFiber,mem_filter]
    exact ⟨h3S hx3.1,hx3.2⟩
  have hyS : y∈mixedFiber D a m plane ell (retained D a m ell plane H P hP hell hell4 hd mu) c := by
    simp only [mixedFiber,classFiber,mem_filter]
    exact ⟨h3S hy3.1,hy3.2⟩
  have hq := congrArg Prod.snd (mixed_key_eq D a m ell plane H P hP hell hell4 hd mu c x y hxS hyS)
  exact Prod.ext ht hq

/-- The same H3 mixed-grain image lies in the ACTUAL reference-height fiber. -/
theorem mixed_X_subset_referenceX {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H H3 : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (h3 : H3⊆second D a m ell plane (retained D a m ell plane H P hP hell hell4 hd mu))
    (x : Fin n × Index) (hx : x∈H3) :
    (mixedFiber D a m plane ell H3 (mixedLabel D a m plane ell x)).image (edgeX D a m ell P hd mu) ⊆
      referenceX D a m ell plane H3 P hP hell hell4 hd mu
        (referenceKey D a m ell plane P hP hell hell4 hd mu x) := by
  apply image_subset_image
  intro y hy
  have hy3 := hy
  simp only [mixedFiber,classFiber,mem_filter] at hy3
  have hxF : x∈mixedFiber D a m plane ell H3 (mixedLabel D a m plane ell x) := by
    simp only [mixedFiber,classFiber,mem_filter]
    exact ⟨hx,True.intro⟩
  exact mem_filter.mpr ⟨hy3.1,mixed_reference_key_eq D a m ell plane H H3 P hP hell hell4 hd mu h3 _ y x hy hxF⟩

/-- Final same-source density at actual reference-height/quotient fibers.
B includes the already proved weighted-height retention and H3 uniformity
loss; all raw vertex and original parent caps apply to H3 itself. -/
theorem every_reference_fiber_density_cross {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4)
    (E0 H H3 : Finset (Fin n × Index)) (hHE0 : H⊆E0)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8)
    (h3 : H3⊆second D a m ell plane (retained D a m ell plane H P hP hell hell4 hd mu))
    (A C B t : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (HC : ∀c : Parent × (Index × Index),∀T⊆E0,∀v : Index,
      (∀z∈T,parentLabel D a (2^m) z.1=c.1) →
      (∀z∈T,spatialLabel D (2^(phaseDepth m)) z.2=v) → A*(T.card:ℝ) ≤ C)
    (hthreshold : ∀x∈H3,t ≤ B*((mixedFiber D a m plane ell H3 (mixedLabel D a m plane ell x)).card:ℝ)) :
    ∀x∈H3,A*t ≤ B*C*(((2^(phaseDepth m-m):ℕ):ℝ))*
      (referenceX D a m ell plane H3 P hP hell hell4 hd mu
        (referenceKey D a m ell plane P hP hell hell4 hd mu x)).card := by
  intro x hx
  have h3S := h3.trans (second_subset D a m ell plane _)
  have hcross := hereditary_X_cross D a m ell hm plane E0 H H3 hHE0 P hP hell hell4 hd mu hmu hmesh h3S
    (mixedLabel D a m plane ell x) A C hC (HC _)
  have hsub := mixed_X_subset_referenceX D a m ell plane H H3 P hP hell hell4 hd mu h3 x hx
  have hlocal : A*t ≤ B*C*(((2^(phaseDepth m-m):ℕ):ℝ))*
      ((mixedFiber D a m plane ell H3 (mixedLabel D a m plane ell x)).image (edgeX D a m ell P hd mu)).card := by
    have hl := mul_le_mul_of_nonneg_left (hthreshold x hx) hA
    have hu := mul_le_mul_of_nonneg_left hcross hB
    nlinarith only [hl,hu]
  exact hlocal.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hsub))
    (mul_nonneg (mul_nonneg hB hC) (Nat.cast_nonneg _)))

end NativeTranslatedGrainHeightFibers
