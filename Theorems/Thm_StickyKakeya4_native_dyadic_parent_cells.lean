import Theorems.Thm_StickyKakeya4_native_original_slope_cube_packing
import Theorems.Thm_StickyKakeya4_native_original_parent_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeDyadicParentCells
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeOriginalSlopeCubePacking

def ancestor (fine coarse : ℕ) (p : Parent) : Parent :=
  (fun j => p.1 j / (2^(fine-coarse):ℕ), fun j => p.2 j / (2^(fine-coarse):ℕ))
def fineParents {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) (a : ℝ) (level : ℕ) : Finset Parent :=
  R.image (parentLabel D a (2^level))
def descendants {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) (a : ℝ)
    (fine coarse : ℕ) (p : Parent) : Finset Parent :=
  (fineParents D R a fine).filter (fun q => ancestor fine coarse q = p)

lemma floor_dyadic_ancestor (x : ℝ) {coarse fine : ℕ} (h : coarse ≤ fine) :
    ⌊(2:ℝ)^coarse*x⌋ = ⌊(2:ℝ)^fine*x⌋ / (2^(fine-coarse):ℕ) := by
  have hp : (2:ℝ)^fine = (2:ℝ)^coarse*(2:ℝ)^(fine-coarse) := by
    rw [←pow_add,Nat.add_sub_of_le h]
  have he : ((2:ℝ)^fine*x)/((2^(fine-coarse):ℕ):ℝ) = (2:ℝ)^coarse*x := by
    rw [Nat.cast_pow,Nat.cast_ofNat,hp]
    field_simp
  have hh := Int.floor_div_natCast ((2:ℝ)^fine*x) (2^(fine-coarse))
  rwa [he] at hh

lemma parent_ancestor_eq {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    {coarse fine : ℕ} (h : coarse ≤ fine) (i : Fin n) :
    ancestor fine coarse (parentLabel D a (2^fine) i) = parentLabel D a (2^coarse) i := by
  apply Prod.ext
  · funext j
    simp only [ancestor,parentLabel,Nat.cast_pow,Nat.cast_ofNat]
    exact (floor_dyadic_ancestor _ h).symm
  · funext j
    simp only [ancestor,parentLabel,Nat.cast_pow,Nat.cast_ofNat]
    exact (floor_dyadic_ancestor _ h).symm

/-- Literal dyadic nesting identifies actual fine cells inside one ancestor
with the image of exactly those original labels in that ancestor. -/
lemma image_parent_fiber_eq_descendants {n : ℕ} (D : FiniteScaleSource n)
    (R : Finset (Fin n)) (a : ℝ) {coarse fine : ℕ} (h : coarse ≤ fine) (p : Parent) :
    (R.filter (fun i => parentLabel D a (2^coarse) i = p)).image (parentLabel D a (2^fine)) =
      descendants D R a fine coarse p := by
  ext q
  constructor
  · intro hq
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hq
    exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mp hi).1,
      (parent_ancestor_eq D a h i).trans (mem_filter.mp hi).2⟩
  · intro hq
    obtain ⟨hqF,hqp⟩ := mem_filter.mp hq
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hqF
    exact mem_image.mpr ⟨i,mem_filter.mpr ⟨hi,by rwa [parent_ancestor_eq D a h i] at hqp⟩,rfl⟩

lemma dyadic_fine_scale {delta : ℝ} {level : ℕ} (h : delta=(2:ℝ)⁻¹^level) :
    ((2^level:ℕ):ℝ)*delta=1 := by
  rw [h,Nat.cast_pow,Nat.cast_ofNat,inv_pow]
  exact mul_inv_cancel₀ (by positivity)

/-- Original direction separation gives the exact fixed occupancy bound in
every actual finest dyadic parameter cell, also after any original selection. -/
lemma finest_cell_occupancy {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    {level : ℕ} (hdy : D.thickness=(2:ℝ)⁻¹^level) (p : Parent) :
    (R.filter (fun i => parentLabel D a (2^level) i=p)).card ≤ 5832 := by
  have hs := dyadic_fine_scale hdy
  have hu := native_retained_parent_card_le h R a (2^level) (by positivity) hs.le p
  rw [hs] at hu
  norm_num at hu
  exact_mod_cast hu

/-- Actual occupied fine-cell counts differ from original tube-label counts
by at most the derived constant 5832, with exact ancestor nesting. -/
theorem descendants_card_comparison {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    {coarse fine : ℕ} (hle : coarse ≤ fine) (hdy : D.thickness=(2:ℝ)⁻¹^fine) (p : Parent) :
    (descendants D R a fine coarse p).card ≤ (R.filter (fun i => parentLabel D a (2^coarse) i=p)).card ∧
    (R.filter (fun i => parentLabel D a (2^coarse) i=p)).card ≤
      5832*(descendants D R a fine coarse p).card := by
  rw [←image_parent_fiber_eq_descendants D R a hle p]
  refine ⟨card_image_le,?_⟩
  apply card_le_mul_card_image_of_maps_to (f := parentLabel D a (2^fine))
  · intro i hi
    exact mem_image_of_mem _ hi
  · intro q _hq
    exact finest_cell_occupancy h (R.filter (fun i => parentLabel D a (2^coarse) i=p)) a hdy q

end NativeDyadicParentCells
