import Theorems.Thm_StickyKakeya4_native_coarse_cell_source
import Theorems.Thm_StickyKakeya4_native_relative_parent_labels

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
noncomputable section
namespace NativeCoarseSourceParentReadback
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeUnitParentNormalization NativeRelativeParentLabels NativeCommonCubicalMesh

/-- This is an equality of actual marked lines, including their offsets and
marks. It is not inferred from an equality of direction vectors or carriers. -/
lemma contracted_line_eq_local_one {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (p : Parent) (i : Fin n) :
    NativeContractedUnitParent.line D a p i = NativeLocalParentGeometry.line D a 1 p i := by
  simp only [NativeContractedUnitParent.line, NativeLocalParentGeometry.line,
    NativeLocalParentGeometry.baseLine, newLine, newSlope, newIntercept,
    NativeLocalParentGeometry.localSlope, NativeLocalParentGeometry.localIntercept,
    Nat.cast_one, one_mul]

/-- At height zero, the chart mesh has no effect on the graph intercept.
This is the exact source-label fact needed when the coarse thickness changes. -/
lemma shiftedIntercept_zero (line : MarkedLine) (mesh : ℝ) (j : Fin 3) :
    shiftedIntercept line mesh 0 j = shiftedIntercept line 1 0 j := by
  simp only [shiftedIntercept, Int.cast_zero, zero_mul, mul_zero, add_zero]

/-- The fixed homothety preserves slope labels and groups512 old intercept
labels in each of the three coordinates. -/
def zeroProjection (z : Parent) : Parent := (z.1, fun j => z.2 j / 512)

lemma projection_zero (M : ℕ) (z : Parent) :
    projection (0, 0) M z = zeroProjection z := by
  apply Prod.ext <;> funext j <;> simp [projection, zeroProjection]

/-- The real coarse-source parent label is read from the actual old
representative line. Its own mesh disappears only because its height shift
is literally zero. -/
theorem source_parentLabel_relative {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (level b : ℕ)
    (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hsep : ∀p∈Q,∀q∈Q,p ≠ q → 64 / ((2 ^ b : ℕ) : ℝ) ≤
      dist (direction (D.line (rep p))) (direction (D.line (rep q))))
    (M : ℕ) (i : Fin Q.card) :
    parentLabel (NativeCoarseCellSource.source h a level b Q rep E hsep) 0 M i =
      relativeLabel D a 1 (0, 0) M (rep (NativeCoarseCellSource.parentIndex Q i)) := by
  have hline := NativeCoarseCellSource.source_line h a level b Q rep E hsep i
  rw [contracted_line_eq_local_one] at hline
  apply Prod.ext
  · funext j
    change ⌊(M : ℝ) * slope ((NativeCoarseCellSource.source h a level b Q rep E hsep).line i) j⌋ = _
    rw [hline]
    rfl
  · funext j
    change ⌊(M : ℝ) * shiftedIntercept ((NativeCoarseCellSource.source h a level b Q rep E hsep).line i)
      (NativeOriginalParentSelection.mesh _) (shift _ 0) j⌋ = _
    simp only [shift, zero_div, Int.floor_zero]
    rw [hline, shiftedIntercept_zero]
    rfl

/-- Literal old-to-current parent map for the same representatives.
In particular the current parent is generally not the old parent label. -/
theorem source_parentLabel {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (level b : ℕ)
    (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hsep : ∀p∈Q,∀q∈Q,p ≠ q → 64 / ((2 ^ b : ℕ) : ℝ) ≤
      dist (direction (D.line (rep p))) (direction (D.line (rep q))))
    (M : ℕ) (i : Fin Q.card) :
    parentLabel (NativeCoarseCellSource.source h a level b Q rep E hsep) 0 M i =
      zeroProjection (parentLabel D a M (rep (NativeCoarseCellSource.parentIndex Q i))) := by
  rw [source_parentLabel_relative, relativeLabel_eq_projection, mul_one, projection_zero]

/-- A current parent contains at most512 cubed DISTINCT old parent labels.
No assertion is made that it contains at most that many tube indices. -/
theorem parent_fiber_old_labels {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (level b : ℕ)
    (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hsep : ∀p∈Q,∀q∈Q,p ≠ q → 64 / ((2 ^ b : ℕ) : ℝ) ≤
      dist (direction (D.line (rep p))) (direction (D.line (rep q))))
    (I : Finset (Fin Q.card)) (M : ℕ) (q : Parent) :
    ((I.filter (fun i => parentLabel (NativeCoarseCellSource.source h a level b Q rep E hsep) 0 M i = q)).image
      (fun i => parentLabel D a M (rep (NativeCoarseCellSource.parentIndex Q i)))).card ≤ 512 ^ 3 := by
  apply (card_le_card (show _ ⊆ projectionBox (0, 0) M q from ?_)).trans_eq
    (projectionBox_card (0, 0) M q)
  intro z hz
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
  apply projection_mem_box
  rw [projection_zero, ← source_parentLabel h a level b Q rep E hsep M i]
  exact (mem_filter.mp hi).2

/-- Exact image readback, retaining the original representative assignment. -/
theorem parent_image {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (level b : ℕ)
    (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hsep : ∀p∈Q,∀q∈Q,p ≠ q → 64 / ((2 ^ b : ℕ) : ℝ) ≤
      dist (direction (D.line (rep p))) (direction (D.line (rep q))))
    (I : Finset (Fin Q.card)) (M : ℕ) :
    I.image (parentLabel (NativeCoarseCellSource.source h a level b Q rep E hsep) 0 M) =
      (I.image (fun i => parentLabel D a M (rep (NativeCoarseCellSource.parentIndex Q i)))).image zeroProjection := by
  rw [image_image]
  apply image_congr
  intro i _hi
  exact source_parentLabel h a level b Q rep E hsep M i

end NativeCoarseSourceParentReadback
