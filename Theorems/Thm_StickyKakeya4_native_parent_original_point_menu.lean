import Theorems.Thm_StickyKakeya4_native_parent_slice_relation_readback

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeParentOriginalPointMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore
open NativeJointUniformCoarseRelations NativeConditionedPairMenu NativeLocalMenuInterpolation SelfUniform

/-- One pre-E2 slot for literal original-point degrees in every middle parent. -/
def relations {n d : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) :
    Fin (d+1) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.addCases Rel (fun _ : Fin 1 => parentPointRel D a (2^m))

lemma relations_refl {n d : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) (H : ∀j x,Rel j x x) :
    ∀j x,relations D a m Rel j x x := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro j x
    simpa only [relations,Fin.addCases_left] using H j x
  · intro j x
    simpa only [relations,Fin.addCases_right] using parentPointRel_refl D a (2^m) x

lemma relations_symm {n d : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀j x y,Rel j x y → Rel j y x) :
    ∀j x y,relations D a m Rel j x y → relations D a m Rel j y x := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro j x y hxy
    simp only [relations,Fin.addCases_left] at hxy ⊢
    exact H j x y hxy
  · intro j x y hxy
    simp only [relations,Fin.addCases_right] at hxy ⊢
    exact hxy.symm

/-- Decode the installed slot as original-point uniformity, not coarse
anisotropic-cell uniformity, on the unchanged E2 parent. -/
theorem parent_original_point_uniformities {n d : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (relations D a m Rel j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (relations D a m Rel j) E y) :
    (∀j x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Rel j) E x ≤
      Q^2*degree (fun _ : Fin n × Index => 1) (Rel j) E y) ∧
    ∀p : Parent,HasUniformFibers (parentEdges D a (2^m) E p) Q Prod.snd := by
  have Hpoint : HasUniformFibers E Q (fun z => (parentLabel D a (2^m) z.1,z.2)) := by
    intro x hx y hy
    have hh := H (Fin.natAdd d (0:Fin 1)) x y hx hy
    simp only [relations,Fin.addCases_right] at hh
    change degree (fun _ : Fin n × Index => 1)
      (fun x y => (parentLabel D a (2^m) x.1,x.2)=(parentLabel D a (2^m) y.1,y.2)) E x ≤
      Q^2*degree (fun _ : Fin n × Index => 1)
      (fun x y => (parentLabel D a (2^m) x.1,x.2)=(parentLabel D a (2^m) y.1,y.2)) E y at hh
    simpa only [unit_degree_eq_fiber] using hh
  refine ⟨?_,fun p => conditioned_uniformity E (fun z => parentLabel D a (2^m) z.1) Prod.snd Q Hpoint p⟩
  intro j x y hx hy
  simpa only [relations,Fin.addCases_left] using H (Fin.castAdd 1 j) x y hx hy

end NativeParentOriginalPointMenu
