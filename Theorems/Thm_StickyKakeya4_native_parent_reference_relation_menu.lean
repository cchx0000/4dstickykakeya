import Theorems.Thm_StickyKakeya4_native_parent_original_point_menu
import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeParentReferenceRelationMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations SelfUniform

/-- All caller slots, one original-point slot, and exactly two slots per
relative scale, with a cardinal fixed before the original source. -/
def relations {n d K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (m : ℕ) (scales : Fin K → ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) :
    Fin ((d+1)+(K+K)) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.addCases (NativeParentOriginalPointMenu.relations D a m Rel)
    (NativeNormalizedCellRelativeCore.relations h R a m scales)

lemma relations_refl {n d K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (m : ℕ) (scales : Fin K → ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) (H : ∀j x,Rel j x x) :
    ∀j x,relations h R a m scales Rel j x x := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro j x
    simpa only [relations,Fin.addCases_left] using NativeParentOriginalPointMenu.relations_refl D a m Rel H j x
  · intro j x
    simpa only [relations,Fin.addCases_right] using NativeNormalizedCellRelativeCore.relations_refl h R a m scales j x

lemma relations_symm {n d K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (m : ℕ) (scales : Fin K → ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀j x y,Rel j x y → Rel j y x) :
    ∀j x y,relations h R a m scales Rel j x y → relations h R a m scales Rel j y x := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro j x y hxy
    simp only [relations,Fin.addCases_left] at hxy ⊢
    exact NativeParentOriginalPointMenu.relations_symm D a m Rel H j x y hxy
  · intro j x y hxy
    simp only [relations,Fin.addCases_right] at hxy ⊢
    exact NativeNormalizedCellRelativeCore.relations_symm h R a m scales j x y hxy

/-- Read all three components from the same E2, keeping the full-R relative
representatives and literal original points. -/
theorem uniformities {n d K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (m : ℕ) (scales : Fin K → ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (relations h R a m scales Rel j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (relations h R a m scales Rel j) E y) :
    (∀j x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Rel j) E x ≤
      Q^2*degree (fun _ : Fin n × Index => 1) (Rel j) E y) ∧
    (∀p : Parent,HasUniformFibers (parentEdges D a (2^m) E p) Q Prod.snd) ∧
    ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (NativeNormalizedCellRelativeCore.relations h R a m scales j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (NativeNormalizedCellRelativeCore.relations h R a m scales j) E y := by
  have hFirst : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (NativeParentOriginalPointMenu.relations D a m Rel j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (NativeParentOriginalPointMenu.relations D a m Rel j) E y := by
    intro j x y hx hy
    simpa only [relations,Fin.addCases_left] using H (Fin.castAdd (K+K) j) x y hx hy
  obtain ⟨hOld,hPoint⟩ := NativeParentOriginalPointMenu.parent_original_point_uniformities D a m Rel E Q hFirst
  refine ⟨hOld,hPoint,?_⟩
  intro j x y hx hy
  simpa only [relations,Fin.addCases_right] using H (Fin.natAdd (d+1) j) x y hx hy

end NativeParentReferenceRelationMenu
