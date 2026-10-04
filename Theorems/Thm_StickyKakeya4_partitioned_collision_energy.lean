import Theorems.Thm_StickyKakeya4_two_tube_path_collision_count
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped BigOperators
noncomputable section

namespace PartitionedCollisionEnergy
open TwoTubePathCollisionCount

def piece {P : Type*} (W : Finset P) (c : P → ℕ) (j : ℕ) : Finset P :=
  W.filter (fun p => c p=j)

/-- The actual output histogram is the sum of the original partition histograms. -/
theorem histogram_partition {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (W : Finset P) (g : P → Q) (c : P → ℕ) (L : ℕ)
    (hc : ∀ p∈W, c p<L) (u : Q) :
    (W.filter (fun p => g p=u)).card =
      ∑ j∈Finset.range L, ((piece W c j).filter (fun p => g p=u)).card := by
  have heq (j : ℕ) : (piece W c j).filter (fun p => g p=u) =
      (W.filter (fun p => g p=u)).filter (fun p => c p=j) := by
    ext p
    simp only [piece, Finset.mem_filter, and_left_comm, and_comm]
  simp_rw [heq]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  symm
  apply Finset.filter_eq_self.mpr
  intro p hp
  exact Finset.mem_range.mpr (hc p (Finset.mem_filter.mp hp).1)

/-- Sum a restricted histogram over the full original output menu. -/
theorem collision_energy_on_original_menu
    {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (W V : Finset P) (g : P → Q) (hV : V⊆W) :
    ∑ u∈W.image g, (V.filter (fun p => g p=u)).card^2 = (collisions V g).card := by
  rw [card_collisions_eq_sum_fiber_sq]
  symm
  apply Finset.sum_subset (Finset.image_subset_image hV)
  intro u _hu hnot
  have hempty : V.filter (fun p => g p=u)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp heq
    exact hnot (Finset.mem_image.mpr ⟨p,hp,heq⟩)
  simp only [hempty, Finset.card_empty, zero_pow (by decide : 2≠0)]

/-- Finite Cauchy derives the energy decomposition from the actual labelled
histograms. The partition and output menu are both built from original data. -/
theorem partition_collision_energy
    {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (W : Finset P) (g : P → Q) (c : P → ℕ) (L : ℕ)
    (hc : ∀ p∈W, c p<L) :
    (collisions W g).card ≤ L * ∑ j∈Finset.range L, (collisions (piece W c j) g).card := by
  rw [card_collisions_eq_sum_fiber_sq]
  calc
    _ ≤ ∑ u∈W.image g, L * ∑ j∈Finset.range L,
        ((piece W c j).filter (fun p => g p=u)).card^2 := by
      apply Finset.sum_le_sum
      intro u _
      rw [histogram_partition W g c L hc u]
      simpa only [Finset.card_range] using nat_sum_sq_le_card_mul_sum_sq
        (Finset.range L) (fun j => ((piece W c j).filter (fun p => g p=u)).card)
    _ = L * ∑ j∈Finset.range L, ∑ u∈W.image g,
        ((piece W c j).filter (fun p => g p=u)).card^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact collision_energy_on_original_menu W (piece W c j) g (Finset.filter_subset _ _)

/-- Each original pair-label pair and first A point determines at most one
second A point. This proves the histogram energy cap by an actual injection. -/
theorem translated_pair_energy_cap
    {G P : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq P]
    (A : Finset G) (W : Finset P) (f : P → G) :
    (collisions (A.product W) (fun p => p.1+f p.2)).card ≤ A.card*W.card^2 := by
  classical
  have hcap : (collisions (A.product W) (fun p => p.1+f p.2)).card ≤
      ((W.product W).product A).card := by
    apply Finset.card_le_card_of_injOn
      (fun z : (G × P) × (G × P) => ((z.1.2,z.2.2),z.1.1))
    · intro z hz
      obtain ⟨h1,h2,_⟩ := (mem_collisions _ _ z).mp hz
      obtain ⟨ha,hp⟩ := Finset.mem_product.mp h1
      obtain ⟨_hb,hq⟩ := Finset.mem_product.mp h2
      exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hp,hq⟩,ha⟩
    · rintro ⟨⟨a,p⟩,⟨b,q⟩⟩ hz ⟨⟨a',p'⟩,⟨b',q'⟩⟩ hz' hh
      have hpp := congrArg (fun z => z.1.1) hh
      have hqq := congrArg (fun z => z.1.2) hh
      have haa := congrArg Prod.snd hh
      dsimp at hpp hqq haa
      subst p'
      subst q'
      subst a'
      have he := (mem_collisions _ _ _).mp hz |>.2.2
      have he' := (mem_collisions _ _ _).mp hz' |>.2.2
      have hbb : b=b' := add_right_cancel (he.symm.trans he')
      subst b'
      rfl
  simpa only [Finset.product_eq_sprod, Finset.card_product, pow_two, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using hcap

end PartitionedCollisionEnergy
