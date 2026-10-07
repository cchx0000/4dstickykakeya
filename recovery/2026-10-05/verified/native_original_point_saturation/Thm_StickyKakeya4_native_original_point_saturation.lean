import Theorems.Thm_StickyKakeya4_native_weighted_grain_quotient_geometry
import Theorems.Thm_StickyKakeya4_native_translated_grain_height_selection
import Theorems.Thm_StickyKakeya4_native_parent_height_alignment
import Theorems.Thm_StickyKakeya4_native_joint_uniform_coarse_relations

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeOriginalPointSaturation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeParentGrainIncidenceCleanup NativeParentHeightAlignment NativeHorizontalGrainSlice
open NativeWeightedGrainQuotientSelection NativeWeightedGrainQuotientGeometry
open NativeTranslatedGrainHeightSelection NativeJointUniformCoarseRelations

def Saturated {A X : Type*} (E S : Finset A) (point : A → X) : Prop :=
  S⊆E ∧ ∀x∈S,∀y∈E,point y=point x → y∈S

theorem saturated_filter {A X : Type*} (E S : Finset A) (point : A → X)
    (HS : Saturated E S point) (test : A → Prop) [DecidablePred test]
    (hTest : ∀x∈E,∀y∈E,point y=point x → (test y↔test x)) :
    Saturated E (S.filter test) point := by
  refine ⟨(filter_subset _ _).trans HS.1,?_⟩
  intro x hx y hy he
  obtain ⟨hx,hxt⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨HS.2 x hx y hy he,(hTest x (HS.1 hx) y hy he).mpr hxt⟩

theorem saturated_selected {A X G B : Type*} [DecidableEq G] [DecidableEq B] [Inhabited B]
    (w : A → ℕ) (E S : Finset A) (point : A → X) (g : A → G) (f : A → B)
    (HS : Saturated E S point)
    (hg : ∀x∈E,∀y∈E,point y=point x → g y=g x)
    (hf : ∀x∈E,∀y∈E,point y=point x → f y=f x) :
    Saturated E (selected w S g f) point := by
  apply saturated_filter E S point HS
  intro x hx y hy he
  rw [hg x hx y hy he,hf x hx y hy he]

theorem original_fiber_eq {A X : Type*} [DecidableEq X]
    (E S : Finset A) (point : A → X) (HS : Saturated E S point)
    (x : A) (hx : x∈S) :
    S.filter (fun y => point y=point x)=E.filter (fun y => point y=point x) := by
  ext y
  simp only [mem_filter]
  exact ⟨fun hy => ⟨HS.1 hy.1,hy.2⟩,fun hy => ⟨HS.2 x hx y hy.1 hy.2,hy.2⟩⟩

/-- Whole ORIGINAL-point selection preserves its inherited exact degree
uniformity. This is not a statement about coarse slicePoint fibers. -/
theorem point_uniformity {A X : Type*} [DecidableEq A] [DecidableEq X]
    (E S : Finset A) (point : A → X) (HS : Saturated E S point) (Q : ℕ)
    (HU : HasUniformFibers E Q point) : HasUniformFibers S Q point := by
  intro x hx y hy
  rw [original_fiber_eq E S point HS x hx,original_fiber_eq E S point HS y hy]
  exact HU x (HS.1 hx) y (HS.1 hy)

theorem nodeCut_saturation {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E S : Finset (Fin n × Index)) (HS : Saturated E S Prod.snd) (B : Finset Index) :
    Saturated E (nodeCut D m S B) Prod.snd := by
  apply saturated_filter E S Prod.snd HS
  intro x _hx y _hy he
  simp only [fineNode,he]

lemma same_point_mixed {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (p : Parent) (E : Finset (Fin n × Index))
    (hparent : ∀z∈E,parentLabel D a (2^m) z.1=p)
    (x y : Fin n × Index) (hx : x∈E) (hy : y∈E) (he : y.2=x.2) :
    mixedLabel D a m plane ell y=mixedLabel D a m plane ell x := by
  simp only [mixedLabel,hparent x hx,hparent y hy,he]

theorem quotient_saturation {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (p : Parent) (E S : Finset (Fin n × Index))
    (hparent : ∀z∈E,parentLabel D a (2^m) z.1=p) (HS : Saturated E S Prod.snd)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1≤ell) (hell4 : ell≤4)
    (hd : Module.finrank ℝ P=ell-1) (mu : ℝ) :
    Saturated E (NativeWeightedGrainQuotientGeometry.retained D a m ell plane S P hP hell hell4 hd mu) Prod.snd := by
  apply saturated_selected (fun _ => 1) E S Prod.snd
    (mixedLabel D a m plane ell) (quotientLabel D a m ell plane P hP hell hell4 hd mu) HS
  · exact fun x hx y hy he => same_point_mixed D a m ell plane p E hparent x y hx hy he
  · intro x hx y hy he
    simp only [quotientLabel,hparent x hx,hparent y hy,he]

theorem translated_heights_saturation {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (p : Parent) (E S : Finset (Fin n × Index))
    (hparent : ∀z∈E,parentLabel D a (2^m) z.1=p) (HS : Saturated E S Prod.snd) :
    Saturated E (second D a m ell plane S) Prod.snd := by
  have hfirst : Saturated E (first D a m ell plane S) Prod.snd := by
    apply saturated_selected (fun _ => 1) E S Prod.snd
      (mixedLabel D a m plane ell) (fun z => NativeTranslatedGrainHeightOverlap.translatedHeight D a m z.2) HS
    · exact fun x hx y hy he => same_point_mixed D a m ell plane p E hparent x y hx hy he
    · intro x _hx y _hy he
      exact congrArg _ he
  apply saturated_selected (fun _ => 1) E (first D a m ell plane S) Prod.snd
    (fun z => NativeTranslatedGrainHeightOverlap.translatedHeight D a m z.2)
    (fun z => NativeTranslatedGrainHeightOverlap.rawHeight D m z.2) hfirst
  · intro x _hx y _hy he
    exact congrArg _ he
  · intro x _hx y _hy he
    exact congrArg _ he

/-- Deterministic original-point saturation through the actual existing
graph-node, weighted quotient, and two height cuts. No new refinement occurs. -/
theorem saturated_graph_quotient_heights {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (p : Parent) (E Hp : Finset (Fin n × Index))
    (hparent : ∀z∈E,parentLabel D a (2^m) z.1=p) (HS : Saturated E Hp Prod.snd)
    (B : Finset Index) (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1≤ell) (hell4 : ell≤4)
    (hd : Module.finrank ℝ P=ell-1) (mu : ℝ) (Q : ℕ) (HU : HasUniformFibers E Q Prod.snd) :
    let S0 := nodeCut D m Hp B
    let S1 := NativeWeightedGrainQuotientGeometry.retained D a m ell plane S0 P hP hell hell4 hd mu
    let S2 := second D a m ell plane S1
    Saturated E S2 Prod.snd ∧ HasUniformFibers S2 Q Prod.snd ∧
      ∀x∈S2,S2.filter (fun y => y.2=x.2)=E.filter (fun y => y.2=x.2) := by
  intro S0 S1 S2
  have h0 := nodeCut_saturation D m E Hp HS B
  have h1 := quotient_saturation D a m ell plane p E S0 hparent h0 P hP hell hell4 hd mu
  have h2 := translated_heights_saturation D a m ell plane p E S1 hparent h1
  exact ⟨h2,point_uniformity E S2 Prod.snd h2 Q HU,fun x hx => original_fiber_eq E S2 Prod.snd h2 x hx⟩

end NativeOriginalPointSaturation
