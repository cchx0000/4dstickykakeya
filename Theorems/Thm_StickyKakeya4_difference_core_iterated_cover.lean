import Theorems.Thm_StickyKakeya4_balanced_bsg_iteration_core

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped Pointwise
noncomputable section

namespace DifferenceCoreIteratedCover

theorem difference_core_neg
    {G : Type*} [AddCommGroup G] [DecidableEq G] (C : Finset G) :
    -(C-C) = C-C := by
  simp only [sub_eq_add_neg, neg_add, neg_neg]
  exact add_comm _ _

theorem difference_core_growth
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (C : Finset G) (hC : C.Nonempty) (K : ℝ)
    (hsmall : ((C-C).card : ℝ) ≤ K * C.card) (n : ℕ) :
    ((n • (C-C)).card : ℝ) ≤ K^(2*n) * (C-C).card := by
  have h := BalancedBSGIterationCore.iterated_differences_of_small_difference C hC K hsmall n n
  rw [← nsmul_sub] at h
  have hc : (C.card : ℝ) ≤ (C-C).card := by exact_mod_cast Finset.card_le_card_sub_right hC
  have hK : 0 ≤ K := by
    have hn : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
    have hd : 0 ≤ ((C-C).card : ℝ) := Nat.cast_nonneg _
    nlinarith only [hsmall, hn, hd]
  calc
    _ ≤ K^(n+n) * C.card := h
    _ ≤ K^(n+n) * (C-C).card := mul_le_mul_of_nonneg_left hc (pow_nonneg hK _)
    _ = _ := by rw [two_mul]

theorem difference_core_difference_growth
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (C : Finset G) (hC : C.Nonempty) (K : ℝ)
    (hsmall : ((C-C).card : ℝ) ≤ K * C.card) :
    (((C-C)-(C-C)).card : ℝ) ≤ K^4 * (C-C).card := by
  have h := difference_core_growth C hC K hsmall 2
  have heq : (C-C)-(C-C) = 2 • (C-C) := by
    rw [sub_eq_add_neg, difference_core_neg, two_nsmul]
  simpa only [heq] using h

/-- The actual original subsets contained in the constructed translates have
all iterated sum-difference bounds. No approximate-group premise is used. -/
theorem covered_iterated_sum_difference
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (C X Y F : Finset G) (hC : C.Nonempty) (K : ℝ)
    (hsmall : ((C-C).card : ℝ) ≤ K * C.card) (x : G)
    (hX : X ⊆ (C-C)+{x}) (hY : Y ⊆ F+(C-C)) (n m : ℕ) :
    ((Y + n • X - m • X).card : ℝ) ≤
      (F.card : ℝ) * (K^(2*(n+m+1)) * (C-C).card) := by
  let H := C-C
  have hneg : -H = H := difference_core_neg C
  have hn : n • X ⊆ n • (H+{x}) := by gcongr
  have hm : m • X ⊆ m • (H+{x}) := by gcongr
  have hsub : Y+n•X-m•X ⊆ (F+H)+n•(H+{x})-m•(H+{x}) :=
    Finset.sub_subset_sub (Finset.add_subset_add hY hn) hm
  have heq : (F+H)+n•(H+{x})-m•(H+{x}) =
      (F + (n+m+1)•H) + {n•x-m•x} := by
    simp only [sub_eq_add_neg, nsmul_add, Finset.nsmul_singleton, neg_add,
      ← neg_nsmul, hneg, Finset.neg_singleton, add_nsmul, one_nsmul]
    rw [← Finset.singleton_add_singleton]
    ac_rfl
  have hc : (Y+n•X-m•X).card ≤ F.card * ((n+m+1)•H).card := by
    calc
      _ ≤ (((F+H)+n•(H+{x})-m•(H+{x}))).card := Finset.card_le_card hsub
      _ = (F+(n+m+1)•H).card := by rw [heq, Finset.card_add_singleton]
      _ ≤ _ := Finset.card_add_le
  have hcR : ((Y+n•X-m•X).card : ℝ) ≤
      (F.card : ℝ) * (((n+m+1)•H).card : ℝ) := by exact_mod_cast hc
  exact hcR.trans (mul_le_mul_of_nonneg_left
    (difference_core_growth C hC K hsmall (n+m+1)) (Nat.cast_nonneg _))

end DifferenceCoreIteratedCover
