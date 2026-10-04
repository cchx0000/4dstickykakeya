import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Tactic
import Theorems.Thm_StickyKakeya4_two_tube_path_collision_count

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

namespace AbelianShiftedLabelEnergy
open scoped BigOperators
open TwoTubePathCollisionCount
noncomputable section
variable {P G : Type*} [DecidableEq P] [AddCommGroup G] [DecidableEq G]

def population (A : Finset P) (f : P → G) (u : G) : ℕ := (A.filter (fun p => f p = u)).card

def shiftedPairs (A : Finset P) (f : P → G) (k : G) : Finset (P × P) :=
  (A.product A).filter (fun p => f p.1 - f p.2 = k)

omit [DecidableEq P] [AddCommGroup G] in
private lemma population_zero (A : Finset P) (f : P → G) {u : G} (hu : u ∉ A.image f) :
    population A f u = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hpA, hpu⟩ := Finset.mem_filter.mp hp
  exact hu (Finset.mem_image.mpr ⟨p, hpA, hpu⟩)

omit [DecidableEq P] in
private lemma shifted_count_by_original_points (A : Finset P) (f : P → G) (k : G) :
    (shiftedPairs A f k).card = ∑ p ∈ A, population A f (f p-k) := by
  simp only [shiftedPairs, population, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro q _hq
  have heq : f p - f q = k ↔ f q = f p-k := by
    constructor
    · intro h; rw [← h]; abel
    · intro h; rw [h]; abel
  simp only [heq]

omit [DecidableEq P] in
private lemma shifted_count_by_labels (A : Finset P) (f : P → G) (k : G) :
    (shiftedPairs A f k).card = ∑ u ∈ A.image f, population A f u * population A f (u-k) := by
  rw [shifted_count_by_original_points]
  simpa only [population, Finset.sum_const, Nat.nsmul_eq_mul] using
    (Finset.sum_fiberwise_of_maps_to' (s := A) (t := A.image f) (g := f)
      (fun p hp => Finset.mem_image_of_mem f hp) (fun u => population A f (u-k))).symm

omit [DecidableEq P] in
private lemma shifted_square_sum_le (A : Finset P) (f : P → G) (k : G) :
    (∑ u ∈ A.image f, population A f (u-k) ^ 2) ≤
      ∑ u ∈ A.image f, population A f u ^ 2 := by
  have heq : (∑ u ∈ A.image f, population A f (u-k) ^ 2) =
      ∑ v ∈ (A.image f).image (fun u => u-k), population A f v ^ 2 := by
    symm
    exact Finset.sum_image (fun _a _ha _b _hb hab => by simpa only [sub_add_cancel] using congrArg (fun x => x+k) hab)
  rw [heq]
  apply Finset.sum_le_sum_of_ne_zero
  intro u _hu hn
  by_contra hnot
  simp only [population_zero A f hnot, zero_pow (by decide : 2 ≠ 0)] at hn
  exact hn rfl

/-- Cauchy bounds every actual shifted label correlation by the zero-shift
energy, even when the two label supports do not coincide. -/
theorem shifted_pairs_le_zero_energy (A : Finset P) (f : P → G) (k : G) :
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


/-- A finite discrepancy menu bounds the original near-pair count in every
additive label group. The application constructs this menu geometrically. -/
theorem pair_set_le_menu_energy (A : Finset P) (f : P → G)
    (E : Finset (P × P)) (D : Finset G)
    (hE : E ⊆ A.product A)
    (hD : ∀ p∈E, f p.1-f p.2 ∈ D) :
    E.card ≤ D.card*(collisions A f).card := by
  classical
  have hsub : E ⊆ D.biUnion (shiftedPairs A f) := by
    intro p hp
    exact Finset.mem_biUnion.mpr ⟨f p.1-f p.2,hD p hp,
      Finset.mem_filter.mpr ⟨hE hp,rfl⟩⟩
  calc
    _ ≤ (D.biUnion (shiftedPairs A f)).card := Finset.card_le_card hsub
    _ ≤ ∑ k∈D, (shiftedPairs A f k).card := Finset.card_biUnion_le
    _ ≤ ∑ _k∈D, (collisions A f).card :=
      Finset.sum_le_sum (fun k _ => shifted_pairs_le_zero_energy A f k)
    _ = _ := by simp
end
end AbelianShiftedLabelEnergy
