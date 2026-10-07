import Theorems.Thm_StickyKakeya4_native_master_point_relations

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace NativeInitialExtraRelations
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh SelfUniform
open NativeMasterPointRelations

/-- Additional source-independent slots and the mandatory original point menu
are installed in one core. No projection to a cheaper retention factor is used. -/
def relations {n d g : ℕ} (D : FiniteScaleSource n) (a : ℝ) {level : ℕ}
    (schedule : Fin g → Fin (level+1))
    (Extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) :
    Fin (d+(1+g)) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.addCases Extra (masterRelations D a schedule)

lemma relations_refl {n d g : ℕ} (D : FiniteScaleSource n) (a : ℝ) {level : ℕ}
    (schedule : Fin g → Fin (level+1))
    (Extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀i x,Extra i x x) : ∀i x,relations D a schedule Extra i x x := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j x
    simpa only [relations,Fin.addCases_left] using H j x
  · intro j x
    simpa only [relations,Fin.addCases_right] using masterRelations_refl D a schedule j x

lemma relations_symm {n d g : ℕ} (D : FiniteScaleSource n) (a : ℝ) {level : ℕ}
    (schedule : Fin g → Fin (level+1))
    (Extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀i x y,Extra i x y → Extra i y x) :
    ∀i x y,relations D a schedule Extra i x y → relations D a schedule Extra i y x := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j x y hh
    simpa only [relations,Fin.addCases_left] using H j x y
      (by simpa only [relations,Fin.addCases_left] using hh)
  · intro j x y hh
    simpa only [relations,Fin.addCases_right] using masterRelations_symm D a schedule j x y
      (by simpa only [relations,Fin.addCases_right] using hh)

theorem caller_uniformities {n d g : ℕ} (D : FiniteScaleSource n) (a : ℝ) {level : ℕ}
    (schedule : Fin g → Fin (level+1))
    (Extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀i x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (relations D a schedule Extra i) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (relations D a schedule Extra i) E y) :
    (∀i x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Extra i) E x ≤
      Q^2*degree (fun _ : Fin n × Index => 1) (Extra i) E y) ∧
    (∀i x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (masterRelations D a schedule i) E x ≤
      Q^2*degree (fun _ : Fin n × Index => 1) (masterRelations D a schedule i) E y) := by
  constructor
  · intro i x y hx hy
    simpa only [relations,Fin.addCases_left] using H (Fin.castAdd (1+g) i) x y hx hy
  · intro i x y hx hy
    simpa only [relations,Fin.addCases_right] using H (Fin.natAdd d i) x y hx hy

end NativeInitialExtraRelations
