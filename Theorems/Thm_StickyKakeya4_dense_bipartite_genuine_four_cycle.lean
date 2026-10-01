import LeanFormalizations.Combinatorics.Additive.BalogSzemerediGowers

open Set

noncomputable section

namespace StickyKakeya4

/-- Common right neighbours of two left vertices in a finite bipartite
relation. -/
def bipartiteCommonNeighbors {G : Type*} [DecidableEq G]
    (Y : Finset G) (E : Finset (G × G)) (a₀ a₁ : G) : Finset G :=
  Y.filter fun b => (a₀, b) ∈ E ∧ (a₁, b) ∈ E

/-- Four pairwise-side-distinct vertices carrying all four edges of a
genuine bipartite four-cycle. -/
structure GenuineBipartiteFourCycle {G : Type*} [DecidableEq G]
    (X Y : Finset G) (E : Finset (G × G)) where
  left₀ : G
  left₁ : G
  right₀ : G
  right₁ : G
  left₀_mem : left₀ ∈ X
  left₁_mem : left₁ ∈ X
  right₀_mem : right₀ ∈ Y
  right₁_mem : right₁ ∈ Y
  left_ne : left₀ ≠ left₁
  right_ne : right₀ ≠ right₁
  edge₀₀ : (left₀, right₀) ∈ E
  edge₀₁ : (left₀, right₁) ∈ E
  edge₁₀ : (left₁, right₀) ∈ E
  edge₁₁ : (left₁, right₁) ∈ E

/-- If at most one quarter of the ordered pairs in a finite set have
codegree below `threshold`, a set with at least two elements contains a
distinct pair whose codegree reaches the threshold. -/
theorem exists_distinct_codegree_pair_of_bad_quarter
    {G : Type*} [DecidableEq G]
    (U Y : Finset G) (E : Finset (G × G)) (threshold : ℝ)
    (hUtwo : 2 ≤ U.card)
    (hbad :
      ((((U ×ˢ U).filter fun p : G × G =>
          ((bipartiteCommonNeighbors Y E p.1 p.2).card : ℝ) < threshold).card : ℝ) ≤
        (1 / 4 : ℝ) * (U.card : ℝ) ^ 2)) :
    ∃ a₀ ∈ U, ∃ a₁ ∈ U, a₀ ≠ a₁ ∧
      threshold ≤ ((bipartiteCommonNeighbors Y E a₀ a₁).card : ℝ) := by
  classical
  let Bad : Finset (G × G) :=
    (U ×ˢ U).filter fun p : G × G =>
      ((bipartiteCommonNeighbors Y E p.1 p.2).card : ℝ) < threshold
  by_contra hnone
  have hoff_subset : U.offDiag ⊆ Bad := by
    intro p hp
    have hp' := Finset.mem_offDiag.mp hp
    have hsmall :
        ((bipartiteCommonNeighbors Y E p.1 p.2).card : ℝ) < threshold := by
      by_contra hnot
      have hlarge :
          threshold ≤ ((bipartiteCommonNeighbors Y E p.1 p.2).card : ℝ) :=
        le_of_not_gt hnot
      exact hnone ⟨p.1, hp'.1, p.2, hp'.2.1, hp'.2.2, hlarge⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hp'.1, hp'.2.1⟩, hsmall⟩
  have hcard_nat : U.card * U.card - U.card ≤ Bad.card := by
    rw [← Finset.offDiag_card U]
    exact Finset.card_le_card hoff_subset
  have hmul : U.card ≤ U.card * U.card := by
    calc
      U.card = U.card * 1 := by simp
      _ ≤ U.card * U.card :=
        Nat.mul_le_mul_left U.card (by omega)
  have hcard_real :
      (U.card : ℝ) ^ 2 - (U.card : ℝ) ≤ (Bad.card : ℝ) := by
    have hcast :
        (((U.card * U.card - U.card : ℕ) : ℝ)) ≤ (Bad.card : ℝ) := by
      exact_mod_cast hcard_nat
    rw [Nat.cast_sub hmul] at hcast
    push_cast at hcast
    nlinarith
  have hbad' :
      (Bad.card : ℝ) ≤ (1 / 4 : ℝ) * (U.card : ℝ) ^ 2 := by
    simpa [Bad] using hbad
  have hUtwo_real : (2 : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hUtwo
  nlinarith

/-- Fox--Sudakov pair dependent random choice, followed by removal of the
diagonal on both sides, produces an actual `K_{2,2}`.  The two quantitative
size hypotheses are exactly what rules out the degenerate paths admitted by
the path-rich rectangle formulation. -/
theorem dense_bipartite_has_genuine_four_cycle
    {G : Type*} [DecidableEq G]
    (X Y : Finset G) (hX : X.Nonempty) (hY : Y.Nonempty)
    (E : Finset (G × G)) (hE_sub : E ⊆ X ×ˢ Y)
    (c : ℝ) (hc_pos : 0 < c) (hc_le : c ≤ 1)
    (hE_dense : c * (X.card : ℝ) * (Y.card : ℝ) ≤ (E.card : ℝ))
    (hX_large : 4 ≤ c * (X.card : ℝ))
    (hY_large : 8 < c ^ 2 * (Y.card : ℝ)) :
    Nonempty (GenuineBipartiteFourCycle X Y E) := by
  classical
  obtain ⟨U, hU_sub, hU_card, hbad⟩ :=
    Finset.graph_pair_dependentRandomChoice X Y hX hY E hE_sub
      c hc_pos hc_le hE_dense (1 / 4 : ℝ) (by norm_num) (by norm_num)
  have hUtwo_real : (2 : ℝ) ≤ (U.card : ℝ) := by
    calc
      (2 : ℝ) ≤ (c / 2) * (X.card : ℝ) := by nlinarith
      _ ≤ (U.card : ℝ) := hU_card
  have hUtwo : 2 ≤ U.card := by exact_mod_cast hUtwo_real
  let threshold : ℝ := ((1 / 4 : ℝ) * c ^ 2 / 2) * (Y.card : ℝ)
  have hcommon_eq : ∀ p : G × G,
      (Y.filter (fun y => (p.1, y) ∈ E)) ∩
          (Y.filter (fun y => (p.2, y) ∈ E)) =
        bipartiteCommonNeighbors Y E p.1 p.2 := by
    intro p
    ext y
    simp only [Finset.mem_inter, Finset.mem_filter, bipartiteCommonNeighbors]
    tauto
  obtain ⟨a₀, ha₀U, a₁, ha₁U, ha_ne, hcodeg⟩ :=
    exists_distinct_codegree_pair_of_bad_quarter U Y E threshold hUtwo (by
      simpa only [hcommon_eq, threshold] using hbad)
  have hthreshold : 1 < threshold := by
    dsimp [threshold]
    nlinarith
  have hcommon_real :
      (1 : ℝ) < ((bipartiteCommonNeighbors Y E a₀ a₁).card : ℝ) :=
    lt_of_lt_of_le hthreshold hcodeg
  have hcommon_one_lt :
      1 < (bipartiteCommonNeighbors Y E a₀ a₁).card := by
    exact_mod_cast hcommon_real
  obtain ⟨b₀, hb₀, b₁, hb₁, hb_ne⟩ :=
    Finset.one_lt_card.mp hcommon_one_lt
  have hb₀' := Finset.mem_filter.mp hb₀
  have hb₁' := Finset.mem_filter.mp hb₁
  exact ⟨{
    left₀ := a₀
    left₁ := a₁
    right₀ := b₀
    right₁ := b₁
    left₀_mem := hU_sub ha₀U
    left₁_mem := hU_sub ha₁U
    right₀_mem := hb₀'.1
    right₁_mem := hb₁'.1
    left_ne := ha_ne
    right_ne := hb_ne
    edge₀₀ := hb₀'.2.1
    edge₀₁ := hb₁'.2.1
    edge₁₀ := hb₀'.2.2
    edge₁₁ := hb₁'.2.2
  }⟩

end StickyKakeya4
