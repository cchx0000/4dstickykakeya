import Theorems.Thm_StickyKakeya4_symmetry_difference_growth_chain
import Theorems.Thm_StickyKakeya4_balanced_bsg_iteration_core
import Theorems.Thm_StickyKakeya4_two_tube_path_collision_count

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped Pointwise BigOperators
noncomputable section

namespace SlowSymmetryBalancedCore
open SymmetryDifferenceGrowthChain

/-- Actual equal-difference pairs inject into the original additive-energy
quadruples by exchanging the second endpoints. -/
theorem difference_collisions_le_energy
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (B : Finset G) (E : Finset (G × G)) (hE : E ⊆ B.product B) :
    (TwoTubePathCollisionCount.collisions E difference).card ≤ Finset.addEnergy B B := by
  classical
  unfold Finset.addEnergy
  apply Finset.card_le_card_of_injOn (fun z : (G × G) × (G × G) =>
    ((z.1.1, z.2.1), (z.2.2, z.1.2)))
  · intro z hz
    obtain ⟨h1, h2, hd⟩ := (TwoTubePathCollisionCount.mem_collisions E difference z).mp hz
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp (hE h1)
    obtain ⟨hc, hd'⟩ := Finset.mem_product.mp (hE h2)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha, hc⟩,
      Finset.mem_product.mpr ⟨hd', hb⟩⟩, ?_⟩
    dsimp [difference] at hd ⊢
    exact sub_eq_sub_iff_add_eq_add.mp hd
  · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ _ ⟨⟨a',b'⟩,⟨c',d'⟩⟩ _ h
    simpa only [Prod.mk.injEq, and_assoc, and_left_comm, and_comm] using h

/-- Cauchy on the actual difference image, without a fiber or energy certificate. -/
theorem original_difference_graph_energy
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (B : Finset G) (E : Finset (G × G)) (hE : E ⊆ B.product B) :
    (E.card : ℝ)^2 ≤ ((E.image difference).card : ℝ) * (Finset.addEnergy B B : ℝ) := by
  have h := (TwoTubePathCollisionCount.square_card_le_image_mul_collisions E difference).trans
    (Nat.mul_le_mul_left _ (difference_collisions_le_energy B E hE))
  exact_mod_cast h

/-- A small actual next-stage ratio yields the balanced energy needed by BSG. -/
theorem energy_of_slow_ratio
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (B : Finset G) (E : Finset (G × G)) (hB : B.Nonempty)
    (hE : E ⊆ B.product B) (sigma Q : ℝ) (hs : 0 ≤ sigma) (hQ : 0 < Q)
    (hdensity : sigma * (B.card : ℝ)^2 ≤ E.card)
    (hratio : ((E.image difference).card : ℝ) / B.card ≤ Q) :
    (sigma^2 / Q) * (B.card : ℝ)^3 ≤ (Finset.addEnergy B B : ℝ) := by
  have hn : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hr := (div_le_iff₀ hn).mp hratio
  have hc := original_difference_graph_energy B E hE
  have he0 : 0 ≤ (Finset.addEnergy B B : ℝ) := Nat.cast_nonneg _
  have he1 := mul_le_mul_of_nonneg_right hr he0
  have hsquare := pow_le_pow_left₀ (mul_nonneg hs (sq_nonneg _)) hdensity 2
  have htotal : sigma^2 * (B.card : ℝ)^4 ≤ Q * B.card * (Finset.addEnergy B B : ℝ) := by
    nlinarith only [hsquare.trans (hc.trans he1)]
  have hcancel : sigma^2 * (B.card : ℝ)^3 ≤ Q * (Finset.addEnergy B B : ℝ) := by
    apply (mul_le_mul_iff_left₀ hn).mp
    nlinarith only [htotal]
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hQ).mpr (by simpa only [mul_comm] using hcancel)

/-- The balanced core is selected at an actual slow stage of the original
asymmetric symmetry chain. -/
theorem exists_balanced_chain_core
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (Y X : Finset G) {a : ℝ} (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2*a*(Y.card : ℝ)*(X.card : ℝ)^2 ≤ (Finset.addEnergy Y X : ℝ))
    {J : ℕ} (hJ : 0 < J) :
    ∃ j C, 1 ≤ j ∧ j ≤ J ∧ C ⊆ chainSet Y X a j ∧ C.Nonempty ∧
      let eta := (density Y X a j)^2 / slowFactor Y X a J
      0 < eta ∧ eta ≤ 1 ∧
      (eta/16) * ((chainSet Y X a j).card : ℝ) ≤ C.card ∧
      ((C-C).card : ℝ) ≤ BalancedBSGIterationCore.growthConstant eta * C.card ∧
      ∀ m n : ℕ, (((m • C)-(n • C)).card : ℝ) ≤
        (BalancedBSGIterationCore.growthConstant eta)^(m+n) * C.card := by
  obtain ⟨j, hj1, hjJ, hratio⟩ := exists_slow_stage Y X ha hY hX he hJ
  let eta := (density Y X a j)^2 / slowFactor Y X a J
  have hs := density_pos (Y := Y) (X := X) ha j
  have hs1 := density_le_one Y X ha hY hX he j
  have hQ1 := one_le_slowFactor Y X ha hY hX he J
  have hQ : 0 < slowFactor Y X a J := lt_of_lt_of_le zero_lt_one hQ1
  have heta : 0 < eta := div_pos (sq_pos_of_pos hs) hQ
  have heta1 : eta ≤ 1 := by
    apply (div_le_iff₀ hQ).mpr
    nlinarith only [sq_nonneg (density Y X a j), hs, hs1, hQ1]
  have henergy := energy_of_slow_ratio (chainSet Y X a j) (chainEdges Y X a j)
    (chain_nonempty Y X ha hY hX he j) (chain_steps Y X ha hY hX he j).subset
    (density Y X a j) (slowFactor Y X a J) hs.le hQ
    (chain_edge_density Y X ha hY hX he j) hratio
  obtain ⟨C, hCB, hC, hsize, hsmall, hiter⟩ := BalancedBSGIterationCore.balanced_energy_core
    (chainSet Y X a j) (chain_nonempty Y X ha hY hX he j) eta heta heta1 henergy
  exact ⟨j, C, hj1, hjJ, hCB, hC, heta, heta1, hsize, hsmall, hiter⟩

end SlowSymmetryBalancedCore
