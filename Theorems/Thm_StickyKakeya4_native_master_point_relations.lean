import Theorems.Thm_StickyKakeya4_native_conditioned_pair_menu
import Theorems.Thm_StickyKakeya4_native_local_menu_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

noncomputable section
namespace NativeMasterPointRelations
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeLocalMenuInterpolation NativeJointUniformCoarseRelations SelfUniform

/-- Global ORIGINAL fine-point equality is installed before the one E is
selected, alongside every scheduled formal parent-point relation. -/
def masterRelations {n g level : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (schedule : Fin g → Fin (level+1)) :
    Fin (1+g) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.addCases (fun _ : Fin 1 => fun x y => x.2=y.2)
    (fun j => parentPointRel D a (2^(schedule j).val))

lemma masterRelations_refl {n g level : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (schedule : Fin g → Fin (level+1)) : ∀j x,masterRelations D a schedule j x x := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro _j x
    simp only [masterRelations,Fin.addCases_left]
  · intro j x
    simpa only [masterRelations,Fin.addCases_right] using parentPointRel_refl D a (2^(schedule j).val) x

lemma masterRelations_symm {n g level : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (schedule : Fin g → Fin (level+1)) :
    ∀j x y,masterRelations D a schedule j x y → masterRelations D a schedule j y x := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro _j x y H
    simp only [masterRelations,Fin.addCases_left] at H ⊢
    exact H.symm
  · intro j x y H
    simp only [masterRelations,Fin.addCases_right] at H ⊢
    exact parentPointRel_symm D a (2^(schedule j).val) x y H

/-- Read both original point uniformity and the full formal menu directly
from that same selected incidence set. -/
theorem master_uniformities {n g level : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (schedule : Fin g → Fin (level+1)) (E : Finset (Fin n × Index)) (rad : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (masterRelations D a schedule j) E x ≤
        rad^2*degree (fun _ : Fin n × Index => 1) (masterRelations D a schedule j) E y) :
    (∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^(schedule j).val)) E x ≤
        rad^2*degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^(schedule j).val)) E y) ∧
      HasUniformFibers E rad Prod.snd := by
  constructor
  · intro j x y hx hy
    simpa only [masterRelations,Fin.addCases_right] using H (Fin.natAdd 1 j) x y hx hy
  · intro x hx y hy
    simpa only [masterRelations,Fin.addCases_left,unit_degree_eq_fiber] using
      H (Fin.castAdd g (0:Fin 1)) x y hx hy

end NativeMasterPointRelations
