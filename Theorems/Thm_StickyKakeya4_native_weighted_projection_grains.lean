import Theorems.Thm_StickyKakeya4_native_quantized_projection_grains
import Theorems.Thm_StickyKakeya4_backward_fiber_grains

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeWeightedProjectionGrains
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeQuantizedProjectionGrains BackwardFiberGrains
open scoped BigOperators

/-- Dense grains at one fixed projection scale. All selected objects are
original occurrence labels, and every mass uses the unchanged original weight.
The computed fiber minimum may be zero; no richness is inferred from geometry.
The maximum in the denominator also covers an empty original vertex set. -/
theorem dense_projection_grains {α : Type*} (A : Finset Index) (B : Finset α)
    (loc : α → Index) (mesh : ℝ) (P : Submodule ℝ E4) (H : ℝ) (hH : 0 < H)
    (w : α → ℝ) (hw : ∀b∈B,0 ≤ w b) (hM : 0 < ∑b∈B,w b) :
    let f := fun b => vertexLabel mesh P H (loc b)
    let q := minimumFiber A B loc mesh P H
    let N := max 1 (625*A.card)
    let M := ∑b∈B,w b
    let t := M*q/(2*N)
    let R := denseClassRestriction B f w t
    (B.image f).card*q ≤ 625*A.card ∧ R⊆B ∧ R.Nonempty ∧
      M/2 ≤ ∑b∈R,w b ∧ (R.image f).card*q ≤ 625*A.card ∧
      (∀b∈R,t ≤ classMass R f w (f b) ∧ classMass R f w (f b)=classMass B f w (f b)) ∧
      ∀c : {c : Index // c∈R.image f},representative R f c∈R ∧
        f (representative R f c)=c.val ∧
        ∀b∈R,f b=c.val → Metric.infDist
          (cellCenter mesh (loc b)-cellCenter mesh (loc (representative R f c))) (P:Set E4) ≤ 2*H := by
  intro f q N M t R
  have hcount : (B.image f).card*q ≤ 625*A.card := grain_count_computed A B loc mesh P H hH
  have hN : 0 < N := lt_of_lt_of_le (by decide : 0 < (1:ℕ)) (le_max_left _ _)
  have hcountN : (B.image f).card*q ≤ N := hcount.trans (le_max_right _ _)
  have hret := dense_class_retains_half B f w N q hN hw hM (by
    have he : @Finset.image α Index (fun a b => Classical.propDecidable (a=b)) f B = B.image f := by
      ext c
      simp only [mem_image]
    rw [he]
    exact hcountN)
  have hRB : R⊆B := filter_subset _ _
  have hmass : M/2 ≤ ∑b∈R,w b := hret.1
  have hRn : R.Nonempty := by
    by_contra hnot
    have he : R=∅ := not_nonempty_iff_eq_empty.mp hnot
    rw [he,sum_empty] at hmass
    have hM' : 0 < M := hM
    linarith
  have hRcount : (R.image f).card*q ≤ 625*A.card :=
    (Nat.mul_le_mul_right q (card_le_card (image_subset_image hRB))).trans hcount
  refine ⟨hcount,hRB,hRn,hmass,hRcount,?_,?_⟩
  · intro b hb
    exact ⟨hret.2 b hb,retained_classMass_eq B f w t b hb⟩
  · exact representatives_cover R loc mesh P H hH

/-- On any nonempty original vertex set, the normalization is exactly the
advertised overlap constant times its cardinality. -/
lemma normalization_of_nonempty (A : Finset Index) (hA : A.Nonempty) :
    max 1 (625*A.card)=625*A.card := by
  apply max_eq_right
  have hp := card_pos.mpr hA
  omega

end NativeWeightedProjectionGrains
