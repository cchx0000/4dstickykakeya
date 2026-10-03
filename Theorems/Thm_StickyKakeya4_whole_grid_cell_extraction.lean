import Mathlib.Data.Int.DivMod
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace WholeGridCellExtraction

abbrev Grid (d : ℕ) := Fin d → ℤ

def cell {d : ℕ} (r : ℕ) (p : Grid d) : Grid d := fun i => p i / (r : ℤ)

lemma cell_mul {d : ℕ} (r s : ℕ) (p : Grid d) :
    cell s (cell r p) = cell (r * s) p := by
  funext i
  simpa only [cell, Nat.cast_mul] using
    (Int.ediv_ediv_of_nonneg (x := p i) (y := (r : ℤ)) (z := (s : ℤ))
      (by positivity))

/-- All original points in current cells which meet the actual witness set. -/
noncomputable def extract {d : ℕ} (E W : Finset (Grid d)) (r : ℕ) : Finset (Grid d) := by
  classical
  exact E.filter (fun p => cell r p ∈ W.image (cell r))

lemma mem_extract {d : ℕ} (E W : Finset (Grid d)) (r : ℕ) (p : Grid d) :
    p ∈ extract E W r ↔ p ∈ E ∧ ∃ w ∈ W, cell r w = cell r p := by
  classical
  simp only [extract, Finset.mem_filter, Finset.mem_image]

lemma extract_subset {d : ℕ} (E W : Finset (Grid d)) (r : ℕ) :
    extract E W r ⊆ E := by
  classical
  exact Finset.filter_subset _ _

lemma witness_subset_extract {d : ℕ} {E W : Finset (Grid d)} (hWE : W ⊆ E) (r : ℕ) :
    W ⊆ extract E W r := by
  intro p hp
  exact (mem_extract E W r p).mpr ⟨hWE hp, p, hp, rfl⟩

/-- Coarser image counts do not increase at all when whole fine cells are extracted. -/
lemma ancestor_image_eq {d : ℕ} {E W : Finset (Grid d)} (hWE : W ⊆ E) (r s : ℕ) :
    (extract E W r).image (cell (r * s)) = W.image (cell (r * s)) := by
  classical
  apply Finset.Subset.antisymm
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨_, w, hw, hwp⟩ := (mem_extract E W r p).mp hp
    apply Finset.mem_image.mpr ⟨w, hw, ?_⟩
    rw [← cell_mul r s w, ← cell_mul r s p, hwp]
  · exact Finset.image_subset_image (witness_subset_extract hWE r)

lemma fine_image_eq {d : ℕ} {E W : Finset (Grid d)} (hWE : W ⊆ E) (r : ℕ) :
    (extract E W r).image (cell r) = W.image (cell r) := by
  simpa using ancestor_image_eq hWE r 1

/-- Removing the extracted points empties every selected fine cell. -/
lemma residual_cell_images_disjoint {d : ℕ} (E W : Finset (Grid d)) (r : ℕ) :
    Disjoint ((E \ extract E W r).image (cell r)) (W.image (cell r)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro q hq hW
  obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
  obtain ⟨hpE, hpnot⟩ := Finset.mem_sdiff.mp hp
  apply hpnot
  exact Finset.mem_filter.mpr ⟨hpE, hpq ▸ hW⟩

lemma same_cell_coordinate_close {d r : ℕ} (hr : 0 < r) {p w : Grid d}
    (h : cell r p = cell r w) (i : Fin d) :
    |p i - w i| < (r : ℤ) := by
  have hr' : (0 : ℤ) < r := by exact_mod_cast hr
  have heq : p i / (r : ℤ) = w i / (r : ℤ) := congrFun h i
  have hp := (Int.ediv_eq_iff_of_pos hr').mp heq
  have hw := (Int.ediv_eq_iff_of_pos hr').mp (rfl : w i / (r : ℤ) = w i / (r : ℤ))
  apply abs_lt.mpr
  constructor <;> omega

lemma extract_has_original_near_witness {d r : ℕ} (hr : 0 < r)
    {E W : Finset (Grid d)} {p : Grid d} (hp : p ∈ extract E W r) :
    ∃ w ∈ W, ∀ i, |p i - w i| < (r : ℤ) := by
  obtain ⟨_, w, hw, hwp⟩ := (mem_extract E W r p).mp hp
  exact ⟨w, hw, fun i => same_cell_coordinate_close hr hwp.symm i⟩

end WholeGridCellExtraction
