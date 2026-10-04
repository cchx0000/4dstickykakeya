import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Tactic
import Theorems.Thm_StickyKakeya4_two_tube_path_collision_count

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

namespace ShiftedLabelEnergy
open scoped BigOperators
open TwoTubePathCollisionCount
noncomputable section
variable {P : Type*} [DecidableEq P]

def population (A : Finset P) (f : P → ℤ) (u : ℤ) : ℕ := (A.filter (fun p => f p = u)).card

def shiftedPairs (A : Finset P) (f : P → ℤ) (k : ℤ) : Finset (P × P) :=
  (A.product A).filter (fun p => f p.1 - f p.2 = k)

omit [DecidableEq P] in
lemma population_zero (A : Finset P) (f : P → ℤ) {u : ℤ} (hu : u ∉ A.image f) :
    population A f u = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hpA, hpu⟩ := Finset.mem_filter.mp hp
  exact hu (Finset.mem_image.mpr ⟨p, hpA, hpu⟩)

omit [DecidableEq P] in
lemma shifted_count_by_original_points (A : Finset P) (f : P → ℤ) (k : ℤ) :
    (shiftedPairs A f k).card = ∑ p ∈ A, population A f (f p-k) := by
  simp only [shiftedPairs, population, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro q _hq
  have heq : f p - f q = k ↔ f q = f p-k := by omega
  simp only [heq]

omit [DecidableEq P] in
lemma shifted_count_by_labels (A : Finset P) (f : P → ℤ) (k : ℤ) :
    (shiftedPairs A f k).card = ∑ u ∈ A.image f, population A f u * population A f (u-k) := by
  rw [shifted_count_by_original_points]
  simpa only [population, Finset.sum_const, Nat.nsmul_eq_mul] using
    (Finset.sum_fiberwise_of_maps_to' (s := A) (t := A.image f) (g := f)
      (fun p hp => Finset.mem_image_of_mem f hp) (fun u => population A f (u-k))).symm

omit [DecidableEq P] in
lemma shifted_square_sum_le (A : Finset P) (f : P → ℤ) (k : ℤ) :
    (∑ u ∈ A.image f, population A f (u-k) ^ 2) ≤
      ∑ u ∈ A.image f, population A f u ^ 2 := by
  have heq : (∑ u ∈ A.image f, population A f (u-k) ^ 2) =
      ∑ v ∈ (A.image f).image (fun u => u-k), population A f v ^ 2 := by
    symm
    exact Finset.sum_image (fun a _ha b _hb hab => by omega)
  rw [heq]
  apply Finset.sum_le_sum_of_ne_zero
  intro u _hu hn
  by_contra hnot
  simp only [population_zero A f hnot, zero_pow (by decide : 2 ≠ 0)] at hn
  exact hn rfl

/-- Cauchy bounds every actual shifted label correlation by the zero-shift
energy, even when the two label supports do not coincide. -/
theorem shifted_pairs_le_zero_energy (A : Finset P) (f : P → ℤ) (k : ℤ) :
    (shiftedPairs A f k).card ≤ (collisions A f).card := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (A.image f)
    (fun u => population A f u) (fun u => population A f (u-k))
  have hs := shifted_square_sum_le A f k
  have heq : (collisions A f).card = ∑ u ∈ A.image f, population A f u ^ 2 :=
    card_collisions_eq_sum_fiber_sq A f
  rw [← shifted_count_by_labels] at hc
  have hbound : (shiftedPairs A f k).card ^ 2 ≤ (collisions A f).card ^ 2 := by
    calc
      _ ≤ _ := hc
      _ ≤ (∑ u ∈ A.image f, population A f u ^ 2) *
          (∑ u ∈ A.image f, population A f u ^ 2) := Nat.mul_le_mul_left _ hs
      _ = _ := by rw [← heq]; ring
  nlinarith

/-- The strict floor-error interval is what gives five, including the
closed near-collision boundary. -/
lemma five_discrepancies {x y δ : ℝ} {i j : ℤ} (hδ : 0 < δ)
    (hx : 0 ≤ x-δ*(i : ℝ) ∧ x-δ*(i : ℝ) < 2*δ)
    (hy : 0 ≤ y-δ*(j : ℝ) ∧ y-δ*(j : ℝ) < 2*δ)
    (hxy : |x-y| ≤ δ) : -2 ≤ i-j ∧ i-j ≤ 2 := by
  obtain ⟨hl, hu⟩ := abs_le.mp hxy
  have hlow : (-3 : ℝ) < (i : ℝ)-(j : ℝ) := by nlinarith
  have hhigh : (i : ℝ)-(j : ℝ) < 3 := by nlinarith
  have hlow' : (-3 : ℤ) < i-j := by exact_mod_cast hlow
  have hhigh' : i-j < (3 : ℤ) := by exact_mod_cast hhigh
  omega

def nearPairs (A : Finset P) (v : P → ℝ) (δ : ℝ) : Finset (P × P) :=
  (A.product A).filter (fun p => |v p.1-v p.2| ≤ δ)

/-- Original near pairs are contained in five literal shifted-correlation
classes. Nothing is independently resampled or balanced. -/
theorem near_pairs_le_five_energy (A : Finset P) (f : P → ℤ) (v : P → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (herror : ∀ p ∈ A, 0 ≤ v p-δ*(f p : ℝ) ∧ v p-δ*(f p : ℝ) < 2*δ) :
    (nearPairs A v δ).card ≤ 5 * (collisions A f).card := by
  classical
  have hsub : nearPairs A v δ ⊆
      (Finset.Icc (-2 : ℤ) 2).biUnion (shiftedPairs A f) := by
    intro p hp
    obtain ⟨hpA, hnear⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpA
    have hk := five_discrepancies hδ (herror p.1 hp₁) (herror p.2 hp₂) hnear
    exact Finset.mem_biUnion.mpr ⟨f p.1-f p.2, Finset.mem_Icc.mpr hk,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp₁,hp₂⟩, rfl⟩⟩
  calc
    _ ≤ ((Finset.Icc (-2 : ℤ) 2).biUnion (shiftedPairs A f)).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.Icc (-2 : ℤ) 2, (shiftedPairs A f k).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.Icc (-2 : ℤ) 2, (collisions A f).card :=
      Finset.sum_le_sum (fun k _ => shifted_pairs_le_zero_energy A f k)
    _ = _ := by
      have hc : (Finset.Icc (-2 : ℤ) 2).card = 5 := by decide
      simp only [Finset.sum_const, hc, Nat.nsmul_eq_mul]
end
end ShiftedLabelEnergy
