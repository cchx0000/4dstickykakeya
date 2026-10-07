import Theorems.Thm_StickyKakeya4_native_parent_point_region_counts
import Theorems.Thm_StickyKakeya4_native_actual_query_rank_configuration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3500000

noncomputable section
namespace NativeParentSliceCallerMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeConditionedPairMenu
open NativeCoarseShadingUniformity SelfUniform

/-- Parent-dependent point cells, computed from the unchanged original cell
and parent. X may encode the coarse physical height and the three fine
sheared spatial labels; the parent is part of one global equality relation. -/
def pointLabel {n : ℕ} {X : Type*} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (point : Parent → Index → X) (z : Fin n × Index) : Parent × X :=
  (parentLabel D a N z.1,point (parentLabel D a N z.1) z.2)

/-- A horizontal class map may keep the point's chosen slice height fixed
while coarsening only its three spatial coordinates. -/
def classLabel {n K : ℕ} {X Y : Type*} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (point : Parent → Index → X) (classes : Parent → Fin K → X → Y)
    (j : Fin K) (z : Fin n × Index) : Parent × Y :=
  (parentLabel D a N z.1,classes (parentLabel D a N z.1) j (point (parentLabel D a N z.1) z.2))

/-- Exactly1+K caller relations suffice for all source-dependent parents,
all slice heights, and a fixed K-element horizontal scale menu. K is fixed
before the source; these literal functions can be chosen before its one E2. -/
def relations {n K : ℕ} {X Y : Type*} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (point : Parent → Index → X) (classes : Parent → Fin K → X → Y) :
    Fin (1+K) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.addCases (fun _ : Fin 1 => fun x y => pointLabel D a N point x=pointLabel D a N point y)
    (fun j x y => classLabel D a N point classes j x=classLabel D a N point classes j y)

lemma relations_refl {n K : ℕ} {X Y : Type*} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (point : Parent → Index → X) (classes : Parent → Fin K → X → Y) :
    ∀j x,relations D a N point classes j x x := by
  intro j
  refine Fin.addCases ?_ ?_ j <;> intro _j x <;>
    simp only [relations,Fin.addCases_left,Fin.addCases_right]

lemma relations_symm {n K : ℕ} {X Y : Type*} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (point : Parent → Index → X) (classes : Parent → Fin K → X → Y) :
    ∀j x y,relations D a N point classes j x y → relations D a N point classes j y x := by
  intro j
  refine Fin.addCases ?_ ?_ j <;> intro _j x y H <;>
    simp only [relations,Fin.addCases_left,Fin.addCases_right] at H ⊢ <;> exact H.symm

/-- Decode the actual caller output of HasQuerySecondStageCore. The
relations have to be installed BEFORE E2; this does not refine an existing E2. -/
theorem parent_uniformities {n K : ℕ} {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (point : Parent → Index → X) (classes : Parent → Fin K → X → Y)
    (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (relations D a N point classes j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (relations D a N point classes j) E y)
    (p : Parent) :
    HasUniformFibers (parentEdges D a N E p) Q (fun z => point p z.2) ∧
    ∀j,HasUniformFibers (parentEdges D a N E p) Q (fun z => classes p j (point p z.2)) := by
  have hPoint : HasUniformFibers E Q (pointLabel D a N point) := by
    intro x hx y hy
    simpa only [relations,Fin.addCases_left,unit_degree_eq_fiber] using H (Fin.castAdd K (0:Fin 1)) x y hx hy
  have hClass : ∀j,HasUniformFibers E Q (classLabel D a N point classes j) := by
    intro j x hx y hy
    simpa only [relations,Fin.addCases_right,unit_degree_eq_fiber] using H (Fin.natAdd 1 j) x y hx hy
  constructor
  · apply uniformity_congr _ (fun z => point (parentLabel D a N z.1) z.2) _ Q
    · intro z hz
      rw [(mem_filter.mp hz).2]
    · exact conditioned_uniformity E (fun z => parentLabel D a N z.1) _ Q hPoint p
  · intro j
    apply uniformity_congr _ (fun z => classes (parentLabel D a N z.1) j (point (parentLabel D a N z.1) z.2)) _ Q
    · intro z hz
      rw [(mem_filter.mp hz).2]
    · exact conditioned_uniformity E (fun z => parentLabel D a N z.1) _ Q (hClass j) p

/-- The new caller fields give comparable DISTINCT occupied anisotropic
point counts in every occupied horizontal class of one actual parent. No
regularity exponent or later-cut lower bound is assumed. -/
theorem parent_occupied_class_counts {n K : ℕ} {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (point : Parent → Index → X) (classes : Parent → Fin K → X → Y)
    (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (relations D a N point classes j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (relations D a N point classes j) E y)
    (p : Parent) (j : Fin K) :
    let P := (parentEdges D a N E p).image (fun z => point p z.2)
    ∀x∈P,∀y∈P,(P.filter (fun z => classes p j z=classes p j x)).card ≤
      Q^4*(P.filter (fun z => classes p j z=classes p j y)).card := by
  obtain ⟨hPoint,hClass⟩ := parent_uniformities D a N point classes E Q H p
  dsimp only
  intro x hx y hy
  have hh := nested_image_fiber_card_comparable (parentEdges D a N E p) (fun z => point p z.2)
    (classes p j) (Q^2) (Q^2) hPoint (hClass j) (classes p j x) (classes p j y)
    (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)
  simpa only [show Q^2*Q^2=Q^4 by ring] using hh

end NativeParentSliceCallerMenu
