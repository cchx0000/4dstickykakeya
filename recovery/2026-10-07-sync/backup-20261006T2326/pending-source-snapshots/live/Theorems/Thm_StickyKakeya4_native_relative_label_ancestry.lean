import Theorems.Thm_StickyKakeya4_native_relative_parent_labels
import Theorems.Thm_StickyKakeya4_native_dyadic_parent_cells

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeJointKeyDescent
open Classical Finset StickyKakeya4 NativeOriginalParentSelection
open NativeRelativeParentLabels NativeDyadicParentCells

/-- Relative phase labels use one fixed local line, so their dyadic
ancestor is exact, including the intercept coordinates. -/
theorem relative_ancestor {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (fine coarse : ℕ) (hcf : coarse ≤ fine) (i : Fin n) :
    ancestor fine coarse (relativeLabel D a N p (2^fine) i) =
      relativeLabel D a N p (2^coarse) i := by
  apply Prod.ext
  · funext j
    simp only [ancestor, relativeLabel, Nat.cast_pow, Nat.cast_ofNat]
    exact (floor_dyadic_ancestor _ hcf).symm
  · funext j
    simp only [ancestor, relativeLabel, Nat.cast_pow, Nat.cast_ofNat]
    exact (floor_dyadic_ancestor _ hcf).symm

/-- Coarser actual relative parents form an image of the finer parent
image. This is a support bound only; it asserts no bound on image fibers. -/
theorem relative_image_card_antitone {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (I : Finset (Fin n)) (fine coarse : ℕ) (hcf : coarse ≤ fine) :
    (I.image (relativeLabel D a N p (2^coarse))).card ≤
      (I.image (relativeLabel D a N p (2^fine))).card := by
  have he : I.image (relativeLabel D a N p (2^coarse)) =
      (I.image (relativeLabel D a N p (2^fine))).image (ancestor fine coarse) := by
    rw [image_image]
    apply image_congr
    intro i _hi
    exact (relative_ancestor D a N p fine coarse hcf i).symm
  rw [he]
  exact card_image_le

end NativeJointKeyDescent
