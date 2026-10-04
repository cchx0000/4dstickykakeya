import Theorems.Thm_StickyKakeya4_slow_symmetry_balanced_core
import Theorems.Thm_StickyKakeya4_chain_original_core_pullback
import Theorems.Thm_StickyKakeya4_difference_core_iterated_cover
import Theorems.Thm_StickyKakeya4_disjoint_rich_translate_cover
import Theorems.Thm_StickyKakeya4_rich_symmetry_translate_centers
import Theorems.Thm_StickyKakeya4_balanced_bsg_polynomial_loss

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open scoped Pointwise BigOperators
noncomputable section

namespace AsymmetricOriginalSubsetAssembly
open SymmetryDifferenceGrowthChain

/-- The original large set and original small set are both retained, from an
actual core at an actual symmetry-chain stage. -/
theorem original_subsets_from_chain_core
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (Y X : Finset G) {a : ℝ} (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2*a*(Y.card : ℝ)*(X.card : ℝ)^2 ≤ (Finset.addEnergy Y X : ℝ))
    (j : ℕ) (hj : 1 ≤ j) (C : Finset G) (hC : C.Nonempty)
    (hCB : C ⊆ chainSet Y X a j) (beta K : ℝ) (hbeta : 0 ≤ beta)
    (hsize : beta * ((chainSet Y X a j).card : ℝ) ≤ C.card)
    (hsmall : ((C-C).card : ℝ) ≤ K*C.card) :
    ∃ X' Y' : Finset G, X' ⊆ X ∧ Y' ⊆ Y ∧
      beta * (∏ i ∈ Finset.range j, density Y X a i / 2) * (X.card : ℝ) ≤ X'.card ∧
      let theta := threshold a (j-1) / (2*K)
      1 ≤ K ∧ 0 < theta ∧ (theta^2 / K^4) * (Y.card : ℝ) ≤ Y'.card ∧
      ∀ n m : ℕ, ((Y' + n • X' - m • X').card : ℝ) ≤
        (K^(2*(n+m+1)) / theta) * Y.card := by
  classical
  let H := C-C
  have hH : H.Nonempty := Finset.sub_nonempty.mpr ⟨hC,hC⟩
  have hn : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hHC : (C.card : ℝ) ≤ H.card := by exact_mod_cast Finset.card_le_card_sub_right hC
  have hK1 : 1 ≤ K := by nlinarith only [hsmall, hHC, hn]
  have hK : 0 < K := zero_lt_one.trans_le hK1
  let c0 := hC.choose
  have hc0 : c0 ∈ C := hC.choose_spec
  have hContain : C ⊆ H+{c0} := by
    intro c hc
    exact Finset.mem_add.mpr ⟨c-c0, Finset.sub_mem_sub hc hc0, c0,
      Finset.mem_singleton_self _, sub_add_cancel _ _⟩
  have hidx : j-1+1=j := by omega
  have hSym : C ⊆ SymmetrySetDifferenceStep.symmetrySet Y (threshold a (j-1)) := by
    have hs := (chain_steps Y X ha hY hX he (j-1)).symmetry
    change chainSet Y X a (j-1+1) ⊆ _ at hs
    rw [hidx] at hs
    exact hCB.trans hs
  obtain ⟨Centers, _hCenters, _hCentersNE, hCentersSize, hRich⟩ :=
    RichSymmetryTranslateCenters.exists_rich_centers_translate Y C H c0
      (threshold_pos ha (j-1)) hK hY hC hSym hContain hsmall
  let theta := threshold a (j-1)/(2*K)
  have htheta : 0 < theta := div_pos (threshold_pos ha (j-1)) (mul_pos (by norm_num) hK)
  have hgrowth : ((H-H).card : ℝ) ≤ K^4*H.card :=
    DifferenceCoreIteratedCover.difference_core_difference_growth C hC K hsmall
  obtain ⟨F,Y',_hFC,hYY,hYcover,hFsize,hYsize⟩ :=
    DisjointRichTranslateCover.exists_rich_translate_selection_quantitative
      Y Centers H theta theta (K^4) hH htheta (pow_pos hK _)
      hCentersSize hRich hgrowth
  obtain ⟨x0,X',hXX,hXcover,hXsize⟩ := ChainOriginalCorePullback.pullback_original_subset
    Y X ha hY hX he j C hC hCB beta hbeta hsize
  refine ⟨X',Y',hXX,hYY,hXsize,hK1,htheta,?_,?_⟩
  · simpa only [pow_two] using hYsize
  · intro n m
    have hc := DifferenceCoreIteratedCover.covered_iterated_sum_difference C X' Y' F hC K
      hsmall x0 hXcover hYcover n m
    have hHp : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
    calc
      _ ≤ (F.card : ℝ)*(K^(2*(n+m+1))*H.card) := hc
      _ ≤ ((Y.card : ℝ)/(theta*H.card))*(K^(2*(n+m+1))*H.card) :=
        mul_le_mul_of_nonneg_right hFsize (by positivity)
      _ = _ := by
        change ((Y.card : ℝ)/(theta*H.card))*(K^(2*(n+m+1))*H.card) =
          (K^(2*(n+m+1))/theta)*Y.card
        field_simp [ne_of_gt htheta, ne_of_gt hHp]

/-- Closed finite asymmetric BSG construction from the ORIGINAL additive
energy. The slow stage, balanced core, both original subsets, and all iterated
sumsets are constructed; no growth, overlap, or refinement certificate enters. -/
theorem finite_asymmetric_original_subsets
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (Y X : Finset G) {a : ℝ} (ha : 0 < a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2*a*(Y.card : ℝ)*(X.card : ℝ)^2 ≤ (Finset.addEnergy Y X : ℝ))
    {J : ℕ} (hJ : 0 < J) :
    ∃ j X' Y', 1 ≤ j ∧ j ≤ J ∧ X' ⊆ X ∧ Y' ⊆ Y ∧
      let kappa := (density Y X a j)^2 / slowFactor Y X a J
      let K := BalancedBSGIterationCore.growthConstant kappa
      let theta := threshold a (j-1)/(2*K)
      0 < kappa ∧ kappa ≤ 1 ∧ 1 ≤ K ∧ 0 < theta ∧
      K*kappa^58 ≤ 2^192 ∧
      (kappa/16) * (∏ i ∈ Finset.range j, density Y X a i / 2) *
        (X.card : ℝ) ≤ X'.card ∧
      (theta^2/K^4) * (Y.card : ℝ) ≤ Y'.card ∧
      ∀ n m : ℕ, ((Y' + n • X' - m • X').card : ℝ) ≤
        (K^(2*(n+m+1))/theta) * Y.card := by
  obtain ⟨j,C,hj1,hjJ,hCB,hC,hkap,hkap1,hsize,hsmall,_hiter⟩ :=
    SlowSymmetryBalancedCore.exists_balanced_chain_core Y X ha hY hX he hJ
  obtain ⟨X',Y',hXX,hYY,hXsize,hK1,htheta,hYsize,hsums⟩ :=
    original_subsets_from_chain_core Y X ha hY hX he j hj1 C hC hCB _ _
      (div_pos hkap (by norm_num)).le hsize hsmall
  exact ⟨j,X',Y',hj1,hjJ,hXX,hYY,hkap,hkap1,hK1,htheta,
    BalancedBSGPolynomialLoss.growth_constant_polynomial hkap hkap1,hXsize,hYsize,hsums⟩

end AsymmetricOriginalSubsetAssembly
