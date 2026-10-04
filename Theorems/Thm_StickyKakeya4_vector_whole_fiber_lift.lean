import Theorems.Thm_StickyKakeya4_dyadic_original_fiber_selection
import Theorems.Thm_StickyKakeya4_original_fiber_energy_collapse

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open Finset
open scoped BigOperators
noncomputable section
open Classical

namespace VectorWholeFiberLift
open DyadicOriginalFiberSelection

/-- Keep every original pair in the selected coupled value fibers. -/
def selectedPairs {W K : Type*} [DecidableEq K] (P : Finset W) (f : W → K) (j : ℕ) (U : Finset K) : Finset W :=
  (bin P f j).filter (fun p => f p ∈ U)

lemma selectedPairs_subset {W K : Type*} [DecidableEq K] (P : Finset W) (f : W → K) (j : ℕ) (U : Finset K) :
    selectedPairs P f j U ⊆ P := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

lemma selectedPairs_image {W K : Type*} [DecidableEq K] (P : Finset W) (f : W → K) (j : ℕ) (U : Finset K)
    (hU : U ⊆ (bin P f j).image f) : (selectedPairs P f j U).image f = U := by
  ext s
  constructor
  · intro hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
    exact (Finset.mem_filter.mp hp).2
  · intro hs
    obtain ⟨p, hp, hps⟩ := Finset.mem_image.mp (hU hs)
    exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hps ▸ hs⟩, hps⟩

lemma selectedPairs_whole_fiber {W K : Type*} [DecidableEq K] (P : Finset W) (f : W → K) (j : ℕ) (U : Finset K)
    {p q : W} (hp : p ∈ selectedPairs P f j U) (hq : q ∈ P) (heq : f q = f p) :
    q ∈ selectedPairs P f j U := by
  obtain ⟨hpbin, hpf⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨bin_saturated P f j hpbin hq heq, heq ▸ hpf⟩

/-- Sum the actual original fiber populations, rather than replacing pair
weights by the number of selected value labels. -/
lemma selectedPairs_fiber_sum {W K : Type*} [DecidableEq K] (P : Finset W) (f : W → K) (j : ℕ) (U : Finset K) :
    ∑ s ∈ U, (fiber (bin P f j) f s).card = (selectedPairs P f j U).card := by
  unfold fiber selectedPairs
  exact Finset.sum_card_fiberwise_eq_card_filter (bin P f j) U f

/-- Uniform dyadic fibers transfer selected label mass to ORIGINAL pair mass
with only a factor two. This is valid for a coupled vector-valued label map. -/
theorem selectedPairs_weighted_mass {W K : Type*} [DecidableEq K]
    (P : Finset W) (f : W → K) (j : ℕ) (U : Finset K)
    (hU : U ⊆ (bin P f j).image f) :
    (bin P f j).card * U.card ≤
      2 * ((bin P f j).image f).card * (selectedPairs P f j U).card := by
  calc
    _ = ∑ _s ∈ U, (bin P f j).card := by simp [mul_comm]
    _ ≤ ∑ s ∈ U, 2 * ((bin P f j).image f).card * (fiber (bin P f j) f s).card :=
      Finset.sum_le_sum (fun s hs => bin_half_average P f j (hU hs))
    _ = 2 * ((bin P f j).image f).card * (∑ s ∈ U, (fiber (bin P f j) f s).card) :=
      (Finset.mul_sum ..).symm
    _ = _ := by rw [selectedPairs_fiber_sum]

lemma selectedPairs_relative_mass {W K : Type*} [DecidableEq K]
    (P : Finset W) (f : W → K) (j : ℕ) (U : Finset K) {r : ℝ}
    (hbin : (bin P f j).Nonempty) (hU : U ⊆ (bin P f j).image f)
    (hret : r * (((bin P f j).image f).card : ℝ) ≤ U.card) :
    r * (bin P f j).card ≤ 2 * (selectedPairs P f j U).card := by
  have hSc : 0 < (((bin P f j).image f).card : ℝ) := by exact_mod_cast (hbin.image f).card_pos
  have hw : ((bin P f j).card : ℝ) * U.card ≤
      2 * (((bin P f j).image f).card : ℝ) * (selectedPairs P f j U).card := by
    exact_mod_cast selectedPairs_weighted_mass P f j U hU
  have hr := mul_le_mul_of_nonneg_left hret (show 0 ≤ ((bin P f j).card : ℝ) by positivity)
  apply (mul_le_mul_iff_left₀ hSc).mp
  nlinarith only [hr, hw]

/-- Combine the derived original energy-bin weight with a selected BSG label
fraction; every selected original pair is retained with its original weight. -/
theorem selectedPairs_original_mass {W K : Type*} [DecidableEq K]
    (P : Finset W) (f : W → K) (j : ℕ) (U : Finset K) {nu r : ℝ}
    (hr : 0 ≤ r) (hbin : (bin P f j).Nonempty) (hU : U ⊆ (bin P f j).image f)
    (hret : r * (((bin P f j).image f).card : ℝ) ≤ U.card)
    (hmass : nu * P.card ≤ 98 * (levelCount P : ℝ) * (bin P f j).card) :
    (r * nu / (196 * (levelCount P : ℝ))) * P.card ≤ (selectedPairs P f j U).card := by
  have hL : 0 < (levelCount P : ℝ) := by
    exact_mod_cast Nat.zero_lt_succ (Nat.log 2 P.card)
  have hF := selectedPairs_relative_mass P f j U hbin hU hret
  have h1 := mul_le_mul_of_nonneg_left hmass hr
  have h2 := mul_le_mul_of_nonneg_left hF (show 0 ≤ 98 * (levelCount P : ℝ) by positivity)
  calc
    _ = (r * nu * P.card) / (196 * (levelCount P : ℝ)) := by ring
    _ ≤ _ := (div_le_iff₀ (show 0 < 196 * (levelCount P : ℝ) by positivity)).mpr (by nlinarith only [h1, h2])

end VectorWholeFiberLift
