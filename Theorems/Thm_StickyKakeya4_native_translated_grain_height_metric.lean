import Theorems.Thm_StickyKakeya4_native_translated_grain_height_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeTranslatedGrainHeightMetric
open Classical Finset StickyKakeya4 NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightSelection
open NativeWeightedGrainQuotientSelection NativeCommonCubicalMesh NativeOriginalParentSelection

/-- The actual raw-height choice at a translated reference height, made by
stage2 original-edge weights. No independent height representative is assumed. -/
def rawAt {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (S : Finset (Fin n × Index)) (t : ℤ) : ℤ :=
  chosen (fun _ => 1) (first D a m ell plane S)
    (fun z => translatedHeight D a m z.2) (fun z => rawHeight D m z.2) t

lemma rawAt_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (S : Finset (Fin n × Index)) (x : Fin n × Index)
    (hx : x∈second D a m ell plane S) : rawAt D a m ell plane S (translatedHeight D a m x.2)=rawHeight D m x.2 := by
  have hh := hx
  simp only [second,selected,mem_filter] at hh
  exact hh.2.symm

/-- A raw-height slope function transported to the actual reference alphabet. -/
def mapped {n : ℕ} {V : Type*} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (S : Finset (Fin n × Index)) (F : ℤ → V) (t : ℤ) : V :=
  F (rawAt D a m ell plane S t)

lemma mapped_readback {n : ℕ} {V : Type*} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (S : Finset (Fin n × Index)) (F : ℤ → V) (x : Fin n × Index)
    (hx : x∈second D a m ell plane S) :
    mapped D a m ell plane S F (translatedHeight D a m x.2)=F (rawHeight D m x.2) := by
  unfold mapped
  rw [rawAt_readback D a m ell plane S x hx]

/-- Literal physical center of the translated parent column-height cell. -/
def referenceHeight (m : ℕ) (t : ℤ) : ℝ := (64/((2^m:ℕ):ℝ))/512*((t:ℝ)+1/2)

lemma referenceHeight_distance (m : ℕ) (t u : ℤ) :
    |referenceHeight m t-referenceHeight m u|=
      ((64/((2^m:ℕ):ℝ))/512)*|(t:ℝ)-u| := by
  unfold referenceHeight
  rw [←mul_sub,add_sub_add_right_eq_sub,abs_mul,abs_of_pos (by positivity : (0:ℝ)<(64/((2^m:ℕ):ℝ))/512)]

/-- The same later source H3 uses the same composed function. Normalized
reference-height distances pay exactly512 times the floor-overlap cost3. -/
theorem mapped_metric {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (S H3 : Finset (Fin n × Index))
    (h3 : H3⊆second D a m ell plane S) (F : ℤ → V) (L : ℝ) (hL : 0 ≤ L)
    (Hraw : ∀x∈H3,∀y∈H3,‖F (rawHeight D m x.2)-F (rawHeight D m y.2)‖ ≤
      L*(64/((2^m:ℕ):ℝ))*|(rawHeight D m x.2:ℝ)-rawHeight D m y.2|) :
    ∀t∈H3.image (fun z => translatedHeight D a m z.2),
      ∀u∈H3.image (fun z => translatedHeight D a m z.2),
        ‖mapped D a m ell plane S F t-mapped D a m ell plane S F u‖ ≤
          (1536*L)*|referenceHeight m t-referenceHeight m u| := by
  intro t ht u hu
  obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hu
  by_cases he : translatedHeight D a m x.2=translatedHeight D a m y.2
  · rw [he,sub_self,norm_zero,sub_self,abs_zero,mul_zero]
  · rw [mapped_readback D a m ell plane S F x (h3 hx),mapped_readback D a m ell plane S F y (h3 hy)]
    have hgap := actual_height_metric D a m x.2 y.2 he
    have hscaled := mul_le_mul_of_nonneg_left hgap
      (by positivity : (0:ℝ) ≤ L*(64/((2^m:ℕ):ℝ)))
    have hh := (Hraw x hx y hy).trans hscaled
    rw [referenceHeight_distance]
    nlinarith only [hh]

lemma mapped_norm_on_image {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (S H3 : Finset (Fin n × Index))
    (h3 : H3⊆second D a m ell plane S) (F : ℤ → V) (B : ℝ)
    (Hnorm : ∀x∈H3,‖F (rawHeight D m x.2)‖ ≤ B) :
    ∀t∈H3.image (fun z => translatedHeight D a m z.2),‖mapped D a m ell plane S F t‖ ≤ B := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
  rw [mapped_readback D a m ell plane S F x (h3 hx)]
  exact Hnorm x hx

end NativeTranslatedGrainHeightMetric
