import Theorems.Thm_StickyKakeya4_native_single_height_recoding
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_field
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_points

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeTranslatedHeightFreeze
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric
open NativeSingleHeightRecoding NativeMatrixHeightWholePoint NativeReferenceXYGridPoints

/-- The actual translated time center, with its physical factor1/8, has
exactly the original integer coarse-height label. Negative heights are included. -/
lemma reference_height_coarse_floor (m R : ℕ) (z : ℤ) :
    ⌊referenceHeight m z/(mu m*(R:ℝ))⌋=z/((8*R:ℕ):ℤ) := by
  have hscale : heightMesh m*((8*R:ℕ):ℝ)=mu m*(R:ℝ) := by
    rw [heightMesh_eq]
    push_cast
    ring
  rw [←hscale]
  exact coarse_height_readback (heightMesh m) (heightMesh_pos m) (8*R) z

/-- A field is frozen from the selected ORIGINAL edges, before all later
restrictions. Its sampler is the actual translated physical time coordinate. -/
def frozen {n : ℕ} {V : Type*} [Zero V] (D : FiniteScaleSource n) (a : ℝ)
    (m R : ℕ) (T : Finset (Fin n × Index)) (F : ℤ → V) : ℤ → V :=
  NativeFrozenTimeField.field T
    (fun z => referenceHeight m (translatedHeight D a m z.2))
    (fun z => F (translatedHeight D a m z.2)) (mu m*(R:ℝ))

/-- This namespace-level lemma is universe-polymorphic, so the two
frozen fields may take values in unrelated types. -/
lemma frozen_readback {n : ℕ} {V : Type*} [Zero V]
    (D : FiniteScaleSource n) (a : ℝ) (m R : ℕ)
    (T : Finset (Fin n × Index)) (F : ℤ → V)
    (hsingle : ∀u∈T,∀v∈T,
      translatedHeight D a m u.2 / ((8 * R : ℕ) : ℤ) =
        translatedHeight D a m v.2 / ((8 * R : ℕ) : ℤ) →
      translatedHeight D a m u.2 = translatedHeight D a m v.2)
    {z : Fin n × Index} (hz : z∈T) :
    frozen D a m R T F (translatedHeight D a m z.2 / ((8 * R : ℕ) : ℤ)) =
      F (translatedHeight D a m z.2) := by
  have hex : ∃u∈T,⌊referenceHeight m (translatedHeight D a m u.2) / (mu m * (R : ℝ))⌋ =
      translatedHeight D a m z.2 / ((8 * R : ℕ) : ℤ) :=
    ⟨z, hz, reference_height_coarse_floor m R _⟩
  obtain ⟨u, hu, he, hread⟩ := NativeFrozenTimeField.field_realization T
    (fun v => referenceHeight m (translatedHeight D a m v.2))
    (fun v => F (translatedHeight D a m v.2)) (mu m * (R : ℝ)) hex
  rw [reference_height_coarse_floor] at he
  have hh := hsingle u hu z hz he
  change NativeFrozenTimeField.field T _ _ _ _ = F _
  rw [hread, hh]

/-- An actual single-height cut on the unchanged native point labels. Both
fields use one selected old height per coarse bin, so the frozen fields agree
EXACTLY at every retained point. The third core can keep its original primary
XY field and transfer to these frozen values by this equality. -/
theorem select_and_freeze {n : ℕ} {V W : Type*} [Zero V] [Zero W]
    (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (S : Finset (Fin n × Index)) (hS : S.Nonempty)
    (F : ℤ → V) (G : ℤ → W) (R : ℕ) (hR : 0< R) :
    ∃B⊆S.image Prod.snd,let T:=edgeLift S Prod.snd B
      T.Nonempty ∧ T⊆S ∧ S.card≤ (8*R)*T.card ∧
      (∀k∈B,T.filter (fun z => z.2=k)=S.filter (fun z => z.2=k)) ∧
      (∀z∈T,∀u∈T,
        translatedHeight D a m z.2/((8*R:ℕ):ℤ)=translatedHeight D a m u.2/((8*R:ℕ):ℤ) →
        translatedHeight D a m z.2=translatedHeight D a m u.2) ∧
      ∀U⊆T,∀z∈U,
        frozen D a m R T F (translatedHeight D a m z.2/((8*R:ℕ):ℤ))=
          F (translatedHeight D a m z.2) ∧
        frozen D a m R T G (translatedHeight D a m z.2/((8*R:ℕ):ℤ))=
          G (translatedHeight D a m z.2) := by
  obtain ⟨B,hB,hTS,hret,hfiber,hheight⟩ := select_original_edges S Prod.snd
    (translatedHeight D a m) F G (8*R) (by positivity)
  let T:=edgeLift S Prod.snd B
  have hT : T.Nonempty := by
    by_contra hn
    have hz : T.card=0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)
    change S.card≤ (8*R)*T.card at hret
    rw [hz,mul_zero] at hret
    have hp:=card_pos.mpr hS
    omega
  refine ⟨B,hB,hT,hTS,hret,hfiber,?_,?_⟩
  · intro z hz u hu heq
    exact (hheight z hz u hu heq).1
  · intro U hUT z hz
    have hzT:=hUT hz
    have hs : ∀u∈T,∀v∈T,
        translatedHeight D a m u.2 / ((8 * R : ℕ) : ℤ) =
          translatedHeight D a m v.2 / ((8 * R : ℕ) : ℤ) →
        translatedHeight D a m u.2 = translatedHeight D a m v.2 :=
      fun u hu v hv he => (hheight u hu v hv he).1
    exact ⟨frozen_readback D a m R T F hs hzT, frozen_readback D a m R T G hs hzT⟩

end NativeTranslatedHeightFreeze
