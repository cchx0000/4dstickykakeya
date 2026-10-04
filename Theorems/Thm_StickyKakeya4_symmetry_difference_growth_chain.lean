import Theorems.Thm_StickyKakeya4_dyadic_original_fiber_selection
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace SymmetryDifferenceGrowthChain

open scoped BigOperators
open SymmetrySetDifferenceStep DyadicOriginalFiberSelection

noncomputable section

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def difference (p : G × G) : G := p.1 - p.2

/-- Threshold for the graph E_i, whose image is B_(i+1). -/
def threshold (a : ℝ) : ℕ → ℝ
  | 0 => a
  | i + 1 => threshold a i ^ 2 / 2

lemma threshold_pos {a : ℝ} (ha : 0 < a) (i : ℕ) : 0 < threshold a i := by
  induction i with
  | zero => exact ha
  | succ i ih => dsimp [threshold]; positivity

/-- Every threshold is an explicit fixed-depth power of the original density. -/
theorem threshold_formula (a : ℝ) (i : ℕ) :
    threshold a i = 2 * (a / 2) ^ (2 ^ i) := by
  induction i with
  | zero => simp only [threshold, pow_zero, pow_one]; ring
  | succ i ih =>
    rw [threshold, ih, show (2 : ℕ) ^ (i + 1) = 2 ^ i * 2 by rw [pow_succ], pow_mul]
    ring

/-- A derived step records its actual original pairs and actual difference image. -/
structure StepSpec (Y S : Finset G) (b : ℝ) (E : Finset (G × G)) : Prop where
  subset : E ⊆ S.product S
  nonempty : E.Nonempty
  mass : b * (S.card : ℝ) ^ 2 ≤
    (levelCount (goodPairs Y S b) : ℝ) * (E.card : ℝ)
  symmetry : E.image difference ⊆ symmetrySet Y b
  saturated : ∀ p ∈ E, ∀ q ∈ S.product S, difference q = difference p → q ∈ E
  full_fiber : ∀ y ∈ E.image difference,
    fiber E difference y = fiber (S.product S) difference y
  lower_fiber : ∀ y ∈ E.image difference,
    (E.card : ℝ) / (2 * ((E.image difference).card : ℝ)) ≤ (fiber E difference y).card

lemma exists_step_of_energy (Y S : Finset G) {b : ℝ}
    (hb : 0 < b) (hY : Y.Nonempty) (hS : S.Nonempty)
    (he : 2 * b * (Y.card : ℝ) * (S.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y S : ℝ)) :
    ∃ E, StepSpec Y S b E := by
  obtain ⟨E, hsub, hne, hm, hsat, hf⟩ := exists_refined_pairs_of_addEnergy Y S hb hY hS he
  refine ⟨E, hsub, hne, hm, ?_, hsat, ?_, ?_⟩
  · intro y hy
    exact (hf y hy).1
  · intro y hy
    exact (hf y hy).2.1
  · intro y hy
    exact (hf y hy).2.2

lemma exists_step_of_symmetry (Y S : Finset G) {b : ℝ}
    (hb : 0 < b) (hY : Y.Nonempty) (hS : S.Nonempty) (hSym : S ⊆ symmetrySet Y b) :
    ∃ E, StepSpec Y S (b ^ 2 / 2) E := by
  obtain ⟨E, hsub, hne, hm, hsat, hf⟩ := exists_refined_symmetry_pairs Y S hb hY hS hSym
  refine ⟨E, hsub, hne, hm, ?_, hsat, ?_, ?_⟩
  · intro y hy
    exact (hf y hy).1
  · intro y hy
    exact (hf y hy).2.1
  · intro y hy
    exact (hf y hy).2.2

/-- A fixed choice of actual original pairs whenever a step exists. -/
def selectedEdges (Y S : Finset G) (b : ℝ) : Finset (G × G) := by
  classical
  exact if h : ∃ E, StepSpec Y S b E then Classical.choose h else ∅

lemma selectedEdges_spec (Y S : Finset G) (b : ℝ)
    (h : ∃ E, StepSpec Y S b E) : StepSpec Y S b (selectedEdges Y S b) := by
  unfold selectedEdges
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The next set is literally the actual selected difference image. -/
def chainSet (Y X : Finset G) (a : ℝ) : ℕ → Finset G
  | 0 => X
  | i + 1 => (selectedEdges Y (chainSet Y X a i) (threshold a i)).image difference

def chainEdges (Y X : Finset G) (a : ℝ) (i : ℕ) : Finset (G × G) :=
  selectedEdges Y (chainSet Y X a i) (threshold a i)

def density (Y X : Finset G) (a : ℝ) (i : ℕ) : ℝ :=
  threshold a i / (levelCount (goodPairs Y (chainSet Y X a i) (threshold a i)) : ℝ)

lemma chainSet_zero (Y X : Finset G) (a : ℝ) : chainSet Y X a 0 = X := rfl

lemma chainSet_succ (Y X : Finset G) (a : ℝ) (i : ℕ) :
    chainSet Y X a (i + 1) = (chainEdges Y X a i).image difference := rfl

/-- The chain is constructed from the original energy, with no chosen-graph,
set-growth, or nested-set premise. -/
theorem chain_steps (Y X : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2 * a * (Y.card : ℝ) * (X.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y X : ℝ))
    (i : ℕ) : StepSpec Y (chainSet Y X a i) (threshold a i) (chainEdges Y X a i) := by
  induction i with
  | zero => exact selectedEdges_spec Y X a (exists_step_of_energy Y X ha hY hX he)
  | succ i ih =>
    apply selectedEdges_spec
    exact exists_step_of_symmetry Y (chainSet Y X a (i + 1)) (threshold_pos ha i) hY
      (ih.nonempty.image difference) ih.symmetry

theorem chain_nonempty (Y X : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2 * a * (Y.card : ℝ) * (X.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y X : ℝ))
    (i : ℕ) : (chainSet Y X a i).Nonempty := by
  cases i with
  | zero => exact hX
  | succ i => exact (chain_steps Y X ha hY hX he i).nonempty.image difference

lemma density_pos {Y X : Finset G} {a : ℝ} (ha : 0 < a) (i : ℕ) :
    0 < density Y X a i := by
  have hl : (0 : ℝ) < levelCount (goodPairs Y (chainSet Y X a i) (threshold a i)) := by
    exact Nat.cast_pos.mpr (Nat.zero_lt_succ _)
  exact div_pos (threshold_pos ha i) hl

/-- Original pair mass gives the exact derived density schedule. -/
theorem chain_edge_density (Y X : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2 * a * (Y.card : ℝ) * (X.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y X : ℝ))
    (i : ℕ) : density Y X a i * ((chainSet Y X a i).card : ℝ) ^ 2 ≤
      ((chainEdges Y X a i).card : ℝ) := by
  have h := (chain_steps Y X ha hY hX he i).mass
  have hl : (0 : ℝ) < levelCount (goodPairs Y (chainSet Y X a i) (threshold a i)) := by
    exact Nat.cast_pos.mpr (Nat.zero_lt_succ _)
  unfold density
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hl).mpr (by nlinarith only [h])

/-- Each actual difference fiber has at most one pair per first endpoint. -/
theorem difference_fiber_card_le (S : Finset G) (E : Finset (G × G))
    (hsub : E ⊆ S.product S) (y : G) : (fiber E difference y).card ≤ S.card := by
  apply Finset.card_le_card_of_injOn (fun p => p.1)
  · intro p hp
    exact (Finset.mem_product.mp (hsub (Finset.mem_filter.mp hp).1)).1
  · intro p hp q hq hpq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    dsimp at hpq
    apply Prod.ext hpq
    dsimp [difference] at hp' hq'
    rw [hpq] at hp'
    have hh := hp'.trans hq'.symm
    simpa only [sub_right_inj] using hh

/-- Counting all original fibers derives growth of the next literal image. -/
theorem edge_card_le_image_mul (S : Finset G) (E : Finset (G × G))
    (hsub : E ⊆ S.product S) : E.card ≤ (E.image difference).card * S.card := by
  calc
    E.card = ∑ y ∈ E.image difference, (fiber E difference y).card := (fiber_sum E difference).symm
    _ ≤ ∑ _y ∈ E.image difference, S.card :=
      Finset.sum_le_sum (fun y _ => difference_fiber_card_le S E hsub y)
    _ = _ := by simp

/-- The lower growth ratio is a consequence of the actual original edge count. -/
theorem chain_growth_lower (Y X : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2 * a * (Y.card : ℝ) * (X.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y X : ℝ))
    (i : ℕ) : density Y X a i * ((chainSet Y X a i).card : ℝ) ≤
      ((chainSet Y X a (i + 1)).card : ℝ) := by
  have hmass := chain_edge_density Y X ha hY hX he i
  have hcap : ((chainEdges Y X a i).card : ℝ) ≤
      ((chainSet Y X a (i + 1)).card : ℝ) * ((chainSet Y X a i).card : ℝ) := by
    exact_mod_cast edge_card_le_image_mul _ _ (chain_steps Y X ha hY hX he i).subset
  have hn : (0 : ℝ) < (chainSet Y X a i).card :=
    Nat.cast_pos.mpr (chain_nonempty Y X ha hY hX he i).card_pos
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith only [hmass.trans hcap]

theorem density_le_one (Y X : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2 * a * (Y.card : ℝ) * (X.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y X : ℝ))
    (i : ℕ) : density Y X a i ≤ 1 := by
  have hmass := chain_edge_density Y X ha hY hX he i
  have hcap : ((chainEdges Y X a i).card : ℝ) ≤ ((chainSet Y X a i).card : ℝ) ^ 2 := by
    have hc := Finset.card_le_card (chain_steps Y X ha hY hX he i).subset
    simpa only [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul, pow_two] using
      (Nat.cast_le.mpr hc : ((chainEdges Y X a i).card : ℝ) ≤ _)
  have hn : (0 : ℝ) < (chainSet Y X a i).card :=
    Nat.cast_pos.mpr (chain_nonempty Y X ha hY hX he i).card_pos
  have hsq : (0 : ℝ) < ((chainSet Y X a i).card : ℝ) ^ 2 := by positivity
  exact (mul_le_mul_iff_left₀ hsq).mp (by simpa only [one_mul] using hmass.trans hcap)

/-- The source symmetry-card bound controls every later set. -/
theorem chain_card_upper (Y X : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2 * a * (Y.card : ℝ) * (X.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y X : ℝ))
    (i : ℕ) : ((chainSet Y X a (i + 1)).card : ℝ) ≤ (Y.card : ℝ) / threshold a i := by
  have hc := Finset.card_le_card (chain_steps Y X ha hY hX he i).symmetry
  exact (Nat.cast_le.mpr hc).trans (symmetrySet_card_bound Y (threshold_pos ha i) hY)

/-- Actual original fibers satisfy the scheduled lower count. -/
theorem chain_fiber_lower (Y X : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2 * a * (Y.card : ℝ) * (X.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y X : ℝ))
    (i : ℕ) {y : G} (hy : y ∈ chainSet Y X a (i + 1)) :
    density Y X a i * ((chainSet Y X a i).card : ℝ) ^ 2 /
        (2 * ((chainSet Y X a (i + 1)).card : ℝ)) ≤
      (fiber (chainEdges Y X a i) difference y).card := by
  have hn : (0 : ℝ) < (chainSet Y X a (i + 1)).card :=
    Nat.cast_pos.mpr (chain_nonempty Y X ha hY hX he (i + 1)).card_pos
  exact (div_le_div_of_nonneg_right (chain_edge_density Y X ha hY hX he i)
    (by positivity)).trans ((chain_steps Y X ha hY hX he i).lower_fiber y hy)


/-- Nonempty actual symmetry stages force their thresholds to be at most one. -/
theorem threshold_le_one_of_energy (Y X : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2 * a * (Y.card : ℝ) * (X.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y X : ℝ))
    (i : ℕ) : threshold a i ≤ 1 := by
  obtain ⟨y, hy⟩ := chain_nonempty Y X ha hY hX he (i + 1)
  have hs := (chain_steps Y X ha hY hX he i).symmetry hy
  have hov := (mem_symmetrySet_iff (threshold_pos ha i) hY y).mp hs
  have hcap : ((overlap Y y).card : ℝ) ≤ (Y.card : ℝ) := Nat.cast_le.mpr (overlap_card_le Y y)
  have hypos : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
  exact (mul_le_mul_iff_left₀ hypos).mp (by simpa only [one_mul] using hov.trans hcap)

/-- The exact density is an original-density power divided by a literal
finite dyadic-class count, before any asymptotic absorption. -/
theorem density_formula (Y X : Finset G) (a : ℝ) (i : ℕ) :
    density Y X a i = (2 * (a / 2) ^ (2 ^ i)) /
      (levelCount (goodPairs Y (chainSet Y X a i) (threshold a i)) : ℝ) := by
  unfold density
  rw [threshold_formula a i]

/-- Exact telescoping for a positive sequence; there is no monotonicity premise. -/
theorem positive_ratio_product (n : ℕ → ℝ) (hn : ∀ i, 0 < n i) (J : ℕ) :
    (∏ i ∈ Finset.range J, n (i + 2) / n (i + 1)) = n (J + 1) / n 1 := by
  induction J with
  | zero => simp only [Finset.range_zero, Finset.prod_empty, zero_add, div_self (hn 1).ne']
  | succ J ih =>
    rw [Finset.prod_range_succ, ih]
    have h1 := (hn 1).ne'
    have hj := (hn (J + 1)).ne'
    field_simp

def sizeRatio (Y X : Finset G) : ℝ := max 1 ((Y.card : ℝ) / (X.card : ℝ))

def terminalBound (Y X : Finset G) (a : ℝ) (J : ℕ) : ℝ :=
  sizeRatio Y X / (threshold a J * density Y X a 0)

def slowFactor (Y X : Finset G) (a : ℝ) (J : ℕ) : ℝ :=
  terminalBound Y X a J ^ ((J : ℝ)⁻¹)

lemma terminalBound_pos (Y X : Finset G) {a : ℝ} (ha : 0 < a) (J : ℕ) :
    0 < terminalBound Y X a J := by
  exact div_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (mul_pos (threshold_pos ha J) (density_pos ha 0))

/-- The actual initial growth and terminal symmetry bound control the
whole telescoped ratio. -/
theorem terminal_ratio_bound (Y X : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2 * a * (Y.card : ℝ) * (X.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y X : ℝ))
    (J : ℕ) : ((chainSet Y X a (J + 1)).card : ℝ) /
      ((chainSet Y X a 1).card : ℝ) ≤ terminalBound Y X a J := by
  have hT := threshold_pos ha J
  have hσ := density_pos (Y := Y) (X := X) ha 0
  have hx : (0 : ℝ) < X.card := Nat.cast_pos.mpr hX.card_pos
  have hn : (0 : ℝ) < (chainSet Y X a 1).card :=
    Nat.cast_pos.mpr (chain_nonempty Y X ha hY hX he 1).card_pos
  have hu := (le_div_iff₀ hT).mp (chain_card_upper Y X ha hY hX he J)
  have hl : density Y X a 0 * (X.card : ℝ) ≤ ((chainSet Y X a 1).card : ℝ) :=
    chain_growth_lower Y X ha hY hX he 0
  have hL : (Y.card : ℝ) ≤ sizeRatio Y X * (X.card : ℝ) :=
    (div_le_iff₀ hx).mp (le_max_right _ _)
  have hLn : 0 ≤ sizeRatio Y X := (zero_le_one.trans (le_max_left _ _))
  unfold terminalBound
  apply (div_le_div_iff₀ hn (mul_pos hT hσ)).mpr
  have h1 := mul_le_mul_of_nonneg_right hu hσ.le
  have h2 := mul_le_mul_of_nonneg_right hL hσ.le
  have h3 := mul_le_mul_of_nonneg_left hl hLn
  nlinarith only [h1, h2, h3]

/-- Exact telescope on the constructed chain. -/
theorem chain_ratio_product (Y X : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2 * a * (Y.card : ℝ) * (X.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y X : ℝ))
    (J : ℕ) :
    (∏ i ∈ Finset.range J, ((chainSet Y X a (i + 2)).card : ℝ) /
      ((chainSet Y X a (i + 1)).card : ℝ)) =
      ((chainSet Y X a (J + 1)).card : ℝ) / ((chainSet Y X a 1).card : ℝ) := by
  apply positive_ratio_product (fun i => ((chainSet Y X a i).card : ℝ)) _ J
  intro i
  exact Nat.cast_pos.mpr (chain_nonempty Y X ha hY hX he i).card_pos

/-- A product bound gives one actual adjacent ratio at most the J-th root. -/
theorem exists_adjacent_ratio_le_root (n : ℕ → ℝ) (hn : ∀ i, 0 < n i)
    {J : ℕ} (hJ : 0 < J) {K : ℝ} (hK : 0 < K)
    (hcap : n (J + 1) / n 1 ≤ K) :
    ∃ j, 1 ≤ j ∧ j ≤ J ∧ n (j + 1) / n j ≤ K ^ ((J : ℝ)⁻¹) := by
  let Q := K ^ ((J : ℝ)⁻¹)
  have hQ : 0 < Q := Real.rpow_pos_of_pos hK _
  have hQpow : Q ^ J = K := Real.rpow_inv_natCast_pow hK.le (Nat.ne_of_gt hJ)
  by_contra! hnone
  have hall (i : ℕ) (hi : i ∈ Finset.range J) : Q < n (i + 2) / n (i + 1) := by
    have hi' := Finset.mem_range.mp hi
    exact hnone (i + 1) (by omega) (by omega)
  have hrange : (Finset.range J).Nonempty := ⟨0, Finset.mem_range.mpr hJ⟩
  have hp := Finset.prod_lt_prod_of_nonempty (fun _ (_hi : _ ∈ Finset.range J) => hQ) hall hrange
  have hh : K < n (J + 1) / n 1 := by
    simpa only [Finset.prod_const, Finset.card_range, hQpow, positive_ratio_product n hn J] using hp
  exact (not_lt_of_ge hcap) hh

/-- The desired slow stage is chosen only after the entire original-data
chain is constructed. B_j are not assumed nested or monotone in size. -/
theorem exists_slow_stage (Y X : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2 * a * (Y.card : ℝ) * (X.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y X : ℝ))
    {J : ℕ} (hJ : 0 < J) :
    ∃ j, 1 ≤ j ∧ j ≤ J ∧
      ((chainSet Y X a (j + 1)).card : ℝ) / ((chainSet Y X a j).card : ℝ) ≤
        slowFactor Y X a J := by
  apply exists_adjacent_ratio_le_root (fun i => ((chainSet Y X a i).card : ℝ))
    (fun i => Nat.cast_pos.mpr (chain_nonempty Y X ha hY hX he i).card_pos)
    hJ (terminalBound_pos Y X ha J)
  exact terminal_ratio_bound Y X ha hY hX he J

/-- The slow factor is at least one, as required for balanced-stage constants. -/
theorem one_le_slowFactor (Y X : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2 * a * (Y.card : ℝ) * (X.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y X : ℝ))
    (J : ℕ) : 1 ≤ slowFactor Y X a J := by
  have hp : 0 < threshold a J * density Y X a 0 :=
    mul_pos (threshold_pos ha J) (density_pos ha 0)
  have hprod : threshold a J * density Y X a 0 ≤ 1 := by
    have h1 := threshold_le_one_of_energy Y X ha hY hX he J
    have h2 := density_le_one Y X ha hY hX he 0
    exact (mul_le_mul h1 h2 (density_pos ha 0).le zero_le_one).trans_eq (one_mul 1)
  have hbound : 1 ≤ terminalBound Y X a J := by
    unfold terminalBound
    apply (le_div_iff₀ hp).mpr
    simpa only [one_mul, sizeRatio] using hprod.trans (le_max_left 1 ((Y.card : ℝ) / (X.card : ℝ)))
  exact Real.one_le_rpow hbound (by positivity)

end

end SymmetryDifferenceGrowthChain
