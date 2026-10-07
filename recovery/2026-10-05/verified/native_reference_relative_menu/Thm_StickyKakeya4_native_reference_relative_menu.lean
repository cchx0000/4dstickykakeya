import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeReferenceRelativeMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeRelativeCoarseReadback SelfUniform

/-- One parent equality and two relative equalities per requested scale,
for every predetermined candidate middle depth. The original R fixes every
representative before the ONE enlarged E1 core is selected. -/
def relations {n G K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (depth : Fin G → ℕ) (scales : Fin G → Fin K → ℕ) :
    Fin (G+G*(K+K)) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.addCases (fun i x y => parentLabel D a (2^(depth i)) x.1=parentLabel D a (2^(depth i)) y.1)
    (fun j => let ik : Fin G × Fin (K+K) := finProdFinEquiv.symm j
      NativeNormalizedCellRelativeCore.relations h R a (depth ik.1) (scales ik.1) ik.2)

lemma relation_count (G K : ℕ) : G+G*(K+K)=G*(1+2*K) := by ring

lemma relations_refl {n G K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (depth : Fin G → ℕ) (scales : Fin G → Fin K → ℕ) : ∀j x,relations h R a depth scales j x x := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i x
    simp only [relations,Fin.addCases_left]
  · intro j x
    simp only [relations,Fin.addCases_right]
    exact NativeNormalizedCellRelativeCore.relations_refl h R a _ _ _ x

lemma relations_symm {n G K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (depth : Fin G → ℕ) (scales : Fin G → Fin K → ℕ) :
    ∀j x y,relations h R a depth scales j x y → relations h R a depth scales j y x := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i x y H
    simp only [relations,Fin.addCases_left] at H ⊢
    exact H.symm
  · intro j x y H
    simp only [relations,Fin.addCases_right] at H ⊢
    exact NativeNormalizedCellRelativeCore.relations_symm h R a _ _ _ x y H

/-- Decode the installed enlarged E1 menu. This lemma does not refine an
existing E1, and it does not replace its actual enlarged retention factor. -/
theorem caller_uniformities {n G K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (depth : Fin G → ℕ) (scales : Fin G → Fin K → ℕ)
    (E1 : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈E1 → y∈E1 →
      degree (fun _ : Fin n × Index => 1) (relations h R a depth scales j) E1 x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (relations h R a depth scales j) E1 y)
    (i : Fin G) :
    (∀x y,x∈E1 → y∈E1 →
      (parentEdges D a (2^(depth i)) E1 (parentLabel D a (2^(depth i)) x.1)).card ≤
        Q^2*(parentEdges D a (2^(depth i)) E1 (parentLabel D a (2^(depth i)) y.1)).card) ∧
    ∀p : Parent,∀hp : (NativeLocalParentSource.parentLabels D R a (2^(depth i)) p).Nonempty,
      ∀j : Fin K,
      HasUniformFibers (parentEdges D a (2^(depth i)) E1 p) Q
        (doublePair h R a (depth i) p hp (scales i j)) ∧
      HasUniformFibers (parentEdges D a (2^(depth i)) E1 p) Q
        (fun z => (doublePair h R a (depth i) p hp (scales i j) z).2) := by
  constructor
  · intro x y hx hy
    simpa only [relations,Fin.addCases_left,unit_degree_eq_parentEdges] using
      H (Fin.castAdd (G*(K+K)) i) x y hx hy
  · intro p hp j
    apply NativeNormalizedCellRelativeCore.caller_relative_uniformities h R a (depth i) (scales i) E1 Q _ p hp j
    intro k x y hx hy
    have hh := H (Fin.natAdd G (finProdFinEquiv (i,k))) x y hx hy
    simpa only [relations,Fin.addCases_right,Equiv.symm_apply_apply] using hh

end NativeReferenceRelativeMenu
