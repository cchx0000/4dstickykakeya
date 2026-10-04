import Theorems.Thm_StickyKakeya4_heavy_energy_bin_selection
import Theorems.Thm_StickyKakeya4_original_fiber_energy_collapse

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
open Finset
open scoped BigOperators
noncomputable section
open Classical

namespace GraphWeightedOriginalFiberBin
open TwoTubePathCollisionCount DyadicOriginalFiberSelection PartitionedCollisionEnergy

def graphPiece {X W V : Type*} [DecidableEq V] (E : Finset (X × W)) (P : Finset W) (f : W → V) (j : ℕ) :
    Finset (X × W) := E.filter (fun e => level P f e.2 = j)

lemma graphPiece_product {X W V : Type*} [DecidableEq V] (A : Finset X) (P : Finset W) (f : W → V)
    (E : Finset (X × W)) (j : ℕ) (hE : E ⊆ A ×ˢ P) :
    graphPiece E P f j ⊆ A ×ˢ bin P f j := by
  intro e he
  obtain ⟨heE, heLevel⟩ := Finset.mem_filter.mp he
  obtain ⟨heA, heP⟩ := Finset.mem_product.mp (hE heE)
  exact Finset.mem_product.mpr ⟨heA, Finset.mem_filter.mpr ⟨heP, heLevel⟩⟩

lemma collisions_mono {X Y : Type*} [DecidableEq X] [DecidableEq Y] (E F : Finset X) (g : X → Y) (hEF : E ⊆ F) :
    collisions E g ⊆ collisions F g := by
  intro ee hee
  obtain ⟨h1, h2, hs⟩ := (mem_collisions _ _ ee).mp hee
  exact (mem_collisions _ _ ee).mpr ⟨hEF h1, hEF h2, hs⟩

/-- Select by ACTUAL graph collision histograms while retaining whole ORIGINAL
value fibers. No full-source high-energy bin is substituted for the graph bin. -/
theorem exists_graph_weighted_energy_bin {G W : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq W]
    (A : Finset G) (P : Finset W) (f : W → G) (E : Finset (G × W))
    (hA : A.Nonempty) (hP : P.Nonempty) (hE : E ⊆ A ×ˢ P) {nu : ℝ} (hnu : 0 < nu)
    (he : nu * A.card * (P.card : ℝ) ^ 2 ≤ ((collisions E (fun e => e.1 + f e.2)).card : ℝ)) :
    ∃ j < levelCount P, (bin P f j).Nonempty ∧ (graphPiece E P f j).Nonempty ∧
      nu * P.card ≤ 2 * (levelCount P : ℝ) * (bin P f j).card ∧
      nu * A.card * (P.card : ℝ) ^ 2 ≤
        2 * (levelCount P : ℝ) ^ 2 * (collisions (graphPiece E P f j) (fun e => e.1 + f e.2)).card ∧
      nu * A.card * (((bin P f j).image f).card : ℝ) ^ 2 ≤
        8 * (levelCount P : ℝ) ^ 2 * (Finset.addEnergy A ((bin P f j).image f) : ℝ) := by
  have hAc : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hPc : 0 < (P.card : ℝ) := by exact_mod_cast hP.card_pos
  have hLc : 0 < (levelCount P : ℝ) := by exact_mod_cast Nat.zero_lt_succ (Nat.log 2 P.card)
  have hsplit := partition_collision_energy E (fun e => e.1 + f e.2)
    (fun e => level P f e.2) (levelCount P) (fun e _ => level_lt P f e.2)
  have hsplitR : ((collisions E (fun e => e.1 + f e.2)).card : ℝ) ≤
      (levelCount P : ℝ) * ∑ j ∈ Finset.range (levelCount P),
        ((collisions (graphPiece E P f j) (fun e => e.1 + f e.2)).card : ℝ) := by
    have hpiece (j : ℕ) : piece E (fun e => level P f e.2) j = graphPiece E P f j := by
      ext e
      simp only [piece, graphPiece, Finset.mem_filter]
    simp_rw [hpiece] at hsplit
    exact_mod_cast hsplit
  have hcap : ∀ j ∈ Finset.range (levelCount P),
      ((collisions (graphPiece E P f j) (fun e => e.1 + f e.2)).card : ℝ) ≤
        (A.card : ℝ) * ((bin P f j).card : ℝ) ^ 2 := by
    intro j _hj
    have hfull := translated_pair_energy_cap A (bin P f j) f
    simp only [Finset.product_eq_sprod] at hfull
    have hc := (Finset.card_le_card (collisions_mono _ _ (fun e => e.1 + f e.2)
      (graphPiece_product A P f E j hE))).trans hfull
    exact_mod_cast hc
  obtain ⟨j, hj, hm, henergy⟩ := HeavyEnergyBinSelection.exists_heavy_energy_index
    (levelCount P) (Nat.zero_lt_succ _)
    (fun j => ((bin P f j).card : ℝ))
    (fun j => ((collisions (graphPiece E P f j) (fun e => e.1 + f e.2)).card : ℝ))
    P.card A.card nu hPc hAc hnu (fun _ _ => Nat.cast_nonneg _)
    (by exact_mod_cast bin_card_sum P f) hcap (he.trans hsplitR)
  have hbinpos : 0 < ((bin P f j).card : ℝ) := by nlinarith only [hm, mul_pos hnu hPc, hLc]
  have hbin : (bin P f j).Nonempty := Finset.card_pos.mp (by exact_mod_cast hbinpos)
  have hgraph : (graphPiece E P f j).Nonempty := by
    apply Finset.card_pos.mp
    by_contra hzero
    have hc : (graphPiece E P f j).card = 0 := by omega
    have hempty := Finset.card_eq_zero.mp hc
    have hpos : 0 < nu * A.card * (P.card : ℝ) ^ 2 := by positivity
    simp [hempty, collisions] at henergy
    exact (not_le_of_gt hpos) henergy
  have hf : ∀ s ∈ (bin P f j).image f, (fiber (bin P f j) f s).card ≤ 2 ^ (j + 1) :=
    fun s hs => (bin_fiber_bounds P f j hs).2.le
  have hfullCollapse := OriginalFiberEnergyCollapse.labelled_sum_energy_le A (bin P f j) f (2 ^ (j + 1)) hf
  simp only [Finset.product_eq_sprod] at hfullCollapse
  have hcollapse := (Finset.card_le_card (collisions_mono _ _ (fun e => e.1 + f e.2)
    (graphPiece_product A P f E j hE))).trans hfullCollapse
  have hcollapseR : ((collisions (graphPiece E P f j) (fun e => e.1 + f e.2)).card : ℝ) ≤
      4 * ((2 : ℝ) ^ j) ^ 2 * (Finset.addEnergy A ((bin P f j).image f) : ℝ) := by
    have hh : ((collisions (graphPiece E P f j) (fun e => e.1 + f e.2)).card : ℝ) ≤
        ((2 : ℝ) ^ (j + 1)) ^ 2 * (Finset.addEnergy A ((bin P f j).image f) : ℝ) := by
      exact_mod_cast hcollapse
    calc
      _ ≤ _ := hh
      _ = _ := by rw [pow_succ]; ring
  have hmass : 2 ^ j * ((bin P f j).image f).card ≤ (bin P f j).card := by
    rw [← fiber_sum (bin P f j) f]
    have hh := Finset.sum_le_sum (fun s (hs : s ∈ (bin P f j).image f) => (bin_fiber_bounds P f j hs).1)
    simpa only [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm] using hh
  have hmassP : (2 : ℝ) ^ j * (((bin P f j).image f).card : ℝ) ≤ P.card := by
    exact_mod_cast hmass.trans (Finset.card_le_card (Finset.filter_subset _ _))
  have hsquare := pow_le_pow_left₀ (show 0 ≤ (2 : ℝ) ^ j * (((bin P f j).image f).card : ℝ) by positivity) hmassP 2
  have hlow := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ nu * A.card by positivity)
  have hhigh := mul_le_mul_of_nonneg_left hcollapseR (show 0 ≤ 2 * (levelCount P : ℝ) ^ 2 by positivity)
  have hcombined := hlow.trans (henergy.trans hhigh)
  refine ⟨j, Finset.mem_range.mp hj, hbin, hgraph, hm, henergy, ?_⟩
  apply (mul_le_mul_iff_left₀ (show 0 < ((2 : ℝ) ^ j) ^ 2 by positivity)).mp
  nlinarith only [hcombined]

end GraphWeightedOriginalFiberBin
