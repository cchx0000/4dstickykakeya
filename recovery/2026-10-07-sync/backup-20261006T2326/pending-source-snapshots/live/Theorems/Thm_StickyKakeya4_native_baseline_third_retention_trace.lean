import Theorems.Thm_StickyKakeya4_native_third_XY_source_data
import Theorems.Thm_StickyKakeya4_native_parent_height_graph_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeBaselineThirdRetentionTrace
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeThirdXYSourceData NativeParentHeightGraphCore NativeRetainedSliceCore

/-- The actual D3 record yields the baseline ORIGINAL-edge retention.
Its full relation dimension and its actual Cpre (including newCutCharge)
are kept. No Y-cut Q^4 has been inserted into this baseline factor. -/
theorem from_third_source {n d J ell : ℕ} (D : FiniteScaleSource n) (zeta a : ℝ) (m : ℕ)
    (plane : Index → Submodule ℝ E4) (E Hp Hgraph S T : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (p : Parent)
    (population PL PU : ℝ) (Qref : ℕ) (lambda G Cpre threshold : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) (CX : ℝ)
    (Hdata : HasThirdXYSourceData (J:=J) D zeta a m plane E Hgraph S T P hP
      hell hell4 hd Fraw p population PL PU Qref lambda G Cpre threshold L3 Rel CX)
    (Khalf : ℕ) (hgraph : Hp.card ≤ selectionCost Khalf*Hgraph.card) :
    let F3:=refinementCost (d+2) (J+1) L3
    1 ≤ F3 ∧ (Hp.card:ℝ) ≤ ((selectionCost Khalf:ℝ)*Cpre*(F3:ℝ))*(T.card:ℝ) := by
  intro F3
  have hF3 : 0 < F3 := refinementCost_pos (d+2) (J+1) L3
  refine ⟨by omega,?_⟩
  have hg : (Hp.card:ℝ) ≤ (selectionCost Khalf:ℝ)*(Hgraph.card:ℝ) := by exact_mod_cast hgraph
  have ht : (Hgraph.card:ℝ) ≤ Cpre*(F3:ℝ)*(T.card:ℝ) := Hdata.1.2.2.2.2.1
  calc
    _ ≤ (selectionCost Khalf:ℝ)*(Hgraph.card:ℝ) := hg
    _ ≤ (selectionCost Khalf:ℝ)*(Cpre*(F3:ℝ)*(T.card:ℝ)) :=
      mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
    _ = _ := by ring

end NativeBaselineThirdRetentionTrace
