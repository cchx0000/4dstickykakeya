import Theorems.Thm_StickyKakeya4_native_configured_third_relation
import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeConfiguredJointRelation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeTranslatedGrainHeightOverlap NativeNormalizedCellRelativeMenu
open CanonicalConfiguredE4Bridge NativeJointUniformCoarseRelations SelfUniform

/-- The actual joint label at a prepared first-chart depth. Its tube width
is (64/2^depth)/512, hence the relative tube-parent depth is depth+9. The
height, spatial cell and tube class remain attached to the same old edge.
Using this label on the deduplicated final pair additionally requires the
actual depth guard depth+9<=u+12; the definition asserts no such descent. -/
def jointKey {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (R depth : ℕ) (z : Fin n × Index) : ℤ × (Index × Parent) :=
  (translatedHeight D a m z.2/((8*R:ℕ):ℤ),
    physicalCell D a (2^m) (2^depth) p z.2,
    NativeRelativeParentLabels.relativeLabel D a (2^m) p (2^(depth+9)) z.1)

/-- Exactly one relation per prepared depth. The menu cardinality is fixed
before the source; its actual depth values are fixed before the sole third
core. No uncharged logarithmic family is inserted. -/
def relations {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (R : ℕ) (depths : Fin K → ℕ) :
    Fin K → (Fin n × Index) → (Fin n × Index) → Prop :=
  fun j x y => jointKey D a m p R (depths j) x=jointKey D a m p R (depths j) y

lemma relations_refl {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (R : ℕ) (depths : Fin K → ℕ) : ∀j x,relations D a m p R depths j x x := fun _ _ => rfl

lemma relations_symm {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (R : ℕ) (depths : Fin K → ℕ) :
    ∀j x y,relations D a m p R depths j x y → relations D a m p R depths j y x :=
  fun _ _ _ h => h.symm

/-- Decode the joint slots on the SAME third T. The actual combined table
has the existing coarse-Y/pair/point prefix, then these K joint slots, then
the untouched window/other extras. Its full dimension is K+d+3, and the
third factor retains its existing additional+2. No new core is selected. -/
theorem caller_joint_uniformity {n K d : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (p : Parent) (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R u : ℕ) (depths : Fin K → ℕ)
    (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (T : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈T → y∈T →
      degree (fun _ : Fin n × Index => 1)
        (NativeConfiguredThirdRelation.completeRelations D a m p s P hP hd F Fcfg R u
          (Fin.addCases (relations D a m p R depths) extra) j) T x ≤
      Q^2*degree (fun _ : Fin n × Index => 1)
        (NativeConfiguredThirdRelation.completeRelations D a m p s P hP hd F Fcfg R u
          (Fin.addCases (relations D a m p R depths) extra) j) T y) :
    ∀j,HasUniformFibers T Q (jointKey D a m p R (depths j)) := by
  intro j x hx y hy
  have hh:=H (Fin.succ (Fin.succ (Fin.succ (j.castAdd d)))) x y hx hy
  simp only [NativeConfiguredThirdRelation.completeRelations,NativeConfiguredThirdRelation.relations,
    Fin.cases_succ,Fin.addCases_left,relations] at hh
  simpa only [unit_degree_eq_fiber] using hh

end NativeConfiguredJointRelation
