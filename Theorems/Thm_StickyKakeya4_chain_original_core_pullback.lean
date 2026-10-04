import Theorems.Thm_StickyKakeya4_symmetry_difference_growth_chain
import Theorems.Thm_StickyKakeya4_iterated_difference_translate_pullback

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped Pointwise BigOperators
noncomputable section

namespace ChainOriginalCorePullback
open SymmetryDifferenceGrowthChain OriginalDifferenceTranslatePullback

/-- An actual subset at any positive symmetry-chain stage pulls back to actual
original X labels in one translate of its own difference set. -/
theorem pullback_original_subset
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (Y X : Finset G) {a : ℝ} (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2*a*(Y.card : ℝ)*(X.card : ℝ)^2 ≤ (Finset.addEnergy Y X : ℝ))
    (j : ℕ) (C : Finset G) (hC : C.Nonempty) (hCB : C ⊆ chainSet Y X a j)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsize : beta * ((chainSet Y X a j).card : ℝ) ≤ C.card) :
    ∃ x0 : G, ∃ X' : Finset G, X' ⊆ X ∧ X' ⊆ (C-C)+{x0} ∧
      beta * (∏ i ∈ Finset.range j, density Y X a i / 2) * (X.card : ℝ) ≤ X'.card := by
  classical
  obtain ⟨c0, hc0⟩ := hC
  let H := C-C
  have hcapture : beta * ((chainSet Y X a j).card : ℝ) ≤
      (translatedSource (chainSet Y X a j) H c0).card := by
    apply hsize.trans
    exact_mod_cast Finset.card_le_card (show C ⊆ translatedSource (chainSet Y X a j) H c0 from by
      intro c hc
      exact Finset.mem_filter.mpr ⟨hCB hc, Finset.sub_mem_sub hc hc0⟩)
  let L := fun i => density Y X a i * ((chainSet Y X a i).card : ℝ)^2 /
      (2*((chainSet Y X a (i+1)).card : ℝ))
  obtain ⟨x0, hx0⟩ := IteratedDifferenceTranslatePullback.pullback_chain j
    (chainSet Y X a) (chainEdges Y X a) L (fun i => density Y X a i / 2) H
    (fun i _ => chain_nonempty Y X ha hY hX he i)
    (fun i _ => (chain_steps Y X ha hY hX he i).subset)
    (fun _ _ => rfl)
    (fun i _ => by
      dsimp [L]
      exact div_nonneg (mul_nonneg (density_pos ha i).le (sq_nonneg _)) (by positivity))
    (fun i _ => (div_pos (density_pos ha i) (by norm_num)).le)
    (fun i _ d hd => chain_fiber_lower Y X ha hY hX he i hd)
    (fun i _ => by
      have hn : (0 : ℝ) < (chainSet Y X a (i+1)).card :=
        Nat.cast_pos.mpr (chain_nonempty Y X ha hY hX he (i+1)).card_pos
      dsimp [L]
      apply le_of_eq
      field_simp)
    beta hbeta c0 hcapture
  refine ⟨x0, translatedSource X H x0, Finset.filter_subset _ _, ?_, hx0⟩
  intro x hx
  have hh := (Finset.mem_filter.mp hx).2
  apply Finset.mem_add.mpr
  exact ⟨x-x0, hh, x0, Finset.mem_singleton_self _, sub_add_cancel _ _⟩

end ChainOriginalCorePullback
