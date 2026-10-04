import Theorems.Thm_StickyKakeya4_symmetry_difference_growth_chain
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace SymmetryChainUniformDensity
open SymmetryDifferenceGrowthChain SymmetrySetDifferenceStep DyadicOriginalFiberSelection
noncomputable section
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem threshold_antitone (Y X : Finset G) {a : ℝ}
    (ha : 0<a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2*a*(Y.card : ℝ)*(X.card : ℝ)^2 ≤ (Finset.addEnergy Y X : ℝ)) :
    Antitone (threshold a) := by
  apply antitone_nat_of_succ_le
  intro i
  have hp := threshold_pos ha i
  have hu := threshold_le_one_of_energy Y X ha hY hX he i
  change (threshold a i)^2/2 ≤ threshold a i
  nlinarith

/-- A budget on original cardinalities bounds every constructed chain stage. -/
theorem chain_card_budget (Y X : Finset G) {a : ℝ}
    (ha : 0<a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2*a*(Y.card : ℝ)*(X.card : ℝ)^2 ≤ (Finset.addEnergy Y X : ℝ))
    (J R : ℕ) (hXB : X.card ≤ 2^R)
    (hYB : (Y.card : ℝ)/threshold a J ≤ (2:ℝ)^R)
    (i : ℕ) (hi : i ≤ J) : (chainSet Y X a i).card ≤ 2^R := by
  cases i with
  | zero => exact hXB
  | succ i =>
    have h1 := chain_card_upper Y X ha hY hX he i
    have ht := threshold_antitone Y X ha hY hX he (show i ≤ J by omega)
    have h2 : (Y.card : ℝ)/threshold a i ≤ (Y.card : ℝ)/threshold a J :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (threshold_pos ha J) ht
    have hh := h1.trans (h2.trans hYB)
    exact_mod_cast hh

theorem good_pairs_card_budget (Y X : Finset G) {a : ℝ}
    (ha : 0<a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2*a*(Y.card : ℝ)*(X.card : ℝ)^2 ≤ (Finset.addEnergy Y X : ℝ))
    (J R : ℕ) (hXB : X.card ≤ 2^R)
    (hYB : (Y.card : ℝ)/threshold a J ≤ (2:ℝ)^R)
    (i : ℕ) (hi : i ≤ J) :
    (goodPairs Y (chainSet Y X a i) (threshold a i)).card ≤ 2^(2*R) := by
  classical
  have hn := chain_card_budget Y X ha hY hX he J R hXB hYB i hi
  have hc : (goodPairs Y (chainSet Y X a i) (threshold a i)).card ≤
      ((chainSet Y X a i).product (chainSet Y X a i)).card := by
    apply Finset.card_le_card
    intro p hp
    have hp' : p ∈ (chainSet Y X a i).product (chainSet Y X a i) ∧
        p.1-p.2 ∈ symmetrySet Y (threshold a i) := by
      simpa only [goodPairs, Finset.mem_filter] using hp
    exact hp'.1
  simp only [Finset.product_eq_sprod, Finset.card_product] at hc
  calc
    _ ≤ (chainSet Y X a i).card * (chainSet Y X a i).card := hc
    _ ≤ (2^R)*(2^R) := Nat.mul_le_mul hn hn
    _ = 2^(2*R) := by rw [← pow_add, two_mul]

theorem chain_level_count_budget (Y X : Finset G) {a : ℝ}
    (ha : 0<a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2*a*(Y.card : ℝ)*(X.card : ℝ)^2 ≤ (Finset.addEnergy Y X : ℝ))
    (J R : ℕ) (hXB : X.card ≤ 2^R)
    (hYB : (Y.card : ℝ)/threshold a J ≤ (2:ℝ)^R)
    (i : ℕ) (hi : i ≤ J) :
    levelCount (goodPairs Y (chainSet Y X a i) (threshold a i)) ≤ 2*R+1 := by
  have h := Nat.log_mono_right (b := 2) (good_pairs_card_budget Y X ha hY hX he J R hXB hYB i hi)
  rw [Nat.log_pow (by norm_num : 1<2)] at h
  exact Nat.add_le_add_right h 1

/-- The lower density is derived from actual stage sizes and actual dyadic
whole-fiber menu lengths. It is uniform over the fixed original chain depth. -/
theorem common_density_lower (Y X : Finset G) {a : ℝ}
    (ha : 0<a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2*a*(Y.card : ℝ)*(X.card : ℝ)^2 ≤ (Finset.addEnergy Y X : ℝ))
    (J R : ℕ) (hXB : X.card ≤ 2^R)
    (hYB : (Y.card : ℝ)/threshold a J ≤ (2:ℝ)^R)
    (i : ℕ) (hi : i ≤ J) :
    threshold a J / (2*(R:ℝ)+1) ≤ density Y X a i := by
  have hmenu := chain_level_count_budget Y X ha hY hX he J R hXB hYB i hi
  have hmenuR : (levelCount (goodPairs Y (chainSet Y X a i) (threshold a i)) : ℝ) ≤
      2*(R:ℝ)+1 := by exact_mod_cast hmenu
  have hmpos : (0:ℝ) < levelCount (goodPairs Y (chainSet Y X a i) (threshold a i)) := by
    exact Nat.cast_pos.mpr (Nat.zero_lt_succ _)
  have hp : 0 < 2*(R:ℝ)+1 := by positivity
  unfold density
  apply (div_le_div_iff₀ hp hmpos).mpr
  calc
    _ ≤ threshold a J * (2*(R:ℝ)+1) :=
      mul_le_mul_of_nonneg_left hmenuR (threshold_pos ha J).le
    _ ≤ _ := mul_le_mul_of_nonneg_right (threshold_antitone Y X ha hY hX he hi) hp.le

theorem common_threshold_range (Y X : Finset G) {a : ℝ}
    (ha : 0<a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2*a*(Y.card : ℝ)*(X.card : ℝ)^2 ≤ (Finset.addEnergy Y X : ℝ))
    (J R : ℕ) :
    0 < threshold a J/(2*(R:ℝ)+1) ∧
    threshold a J/(2*(R:ℝ)+1) ≤ 1 ∧
    ∀ i ≤ J, threshold a J/(2*(R:ℝ)+1) ≤ threshold a i := by
  have hd : 0 < 2*(R:ℝ)+1 := by positivity
  have hd1 : 1 ≤ 2*(R:ℝ)+1 := by
    have hr : 0 ≤ (R:ℝ) := Nat.cast_nonneg _
    linarith
  have hp : threshold a J/(2*(R:ℝ)+1) ≤ threshold a J := by
    apply (div_le_iff₀ hd).mpr
    nlinarith only [hd1, threshold_pos ha J]
  exact ⟨div_pos (threshold_pos ha J) hd,
    hp.trans (threshold_le_one_of_energy Y X ha hY hX he J),
    fun i hi => hp.trans (threshold_antitone Y X ha hY hX he hi)⟩

/-- A concrete binary budget constructed from the original input sizes. -/
def sourceBudget (Y X : Finset G) (a : ℝ) (J : ℕ) : ℕ :=
  max X.card ⌈(Y.card : ℝ)/threshold a J⌉₊

def sourceExponent (Y X : Finset G) (a : ℝ) (J : ℕ) : ℕ :=
  Nat.log 2 (sourceBudget Y X a J)+1

omit [AddCommGroup G] [DecidableEq G] in
theorem source_budget_bounds (Y X : Finset G) (a : ℝ) (J : ℕ) :
    X.card ≤ 2^(sourceExponent Y X a J) ∧
    (Y.card : ℝ)/threshold a J ≤ (2:ℝ)^(sourceExponent Y X a J) := by
  have hp : sourceBudget Y X a J ≤ 2^(sourceExponent Y X a J) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1<2) (sourceBudget Y X a J)).le
  refine ⟨(le_max_left _ _).trans hp, ?_⟩
  have hy : (Y.card : ℝ)/threshold a J ≤ (sourceBudget Y X a J : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  exact hy.trans (by exact_mod_cast hp)

/-- No chosen scale budget enters this final uniform density caller: its
binary exponent is constructed from original cardinalities and the threshold. -/
theorem constructed_common_density (Y X : Finset G) {a : ℝ}
    (ha : 0<a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2*a*(Y.card : ℝ)*(X.card : ℝ)^2 ≤ (Finset.addEnergy Y X : ℝ))
    (J : ℕ) :
    let R := sourceExponent Y X a J
    let p := threshold a J/(2*(R:ℝ)+1)
    0 < p ∧ p ≤ 1 ∧ ∀ i ≤ J, p ≤ threshold a i ∧ p ≤ density Y X a i := by
  have hb := source_budget_bounds Y X a J
  have hr := common_threshold_range Y X ha hY hX he J (sourceExponent Y X a J)
  exact ⟨hr.1,hr.2.1,fun i hi => ⟨hr.2.2 i hi,
    common_density_lower Y X ha hY hX he J (sourceExponent Y X a J) hb.1 hb.2 i hi⟩⟩

end
end SymmetryChainUniformDensity
