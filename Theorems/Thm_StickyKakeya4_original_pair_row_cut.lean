import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open scoped BigOperators
noncomputable section
namespace OriginalPairRowCut

/-- Construct actual original good pairs after bad starting rows, the actual
diagonal, and controlled rich-partner rows are removed. -/
theorem exists_good_pairs
    {P : Type*} [DecidableEq P] (Pts Bad : Finset P) (R : P → P → Prop) [DecidableRel R]
    (eta : ℝ) (heta : 0≤eta)
    (hrows : ∀ p∈Pts, p∉Bad → ((Pts.filter (fun q => R p q)).card : ℝ)≤eta*Pts.card) :
    ∃ G : Finset (P × P), G⊆Pts.product Pts ∧
      (∀ z∈G, z.1∉Bad ∧ z.1≠z.2 ∧ ¬R z.1 z.2) ∧
      (Pts.card : ℝ)^2 ≤ G.card+(Bad.card : ℝ)*Pts.card+Pts.card+eta*(Pts.card : ℝ)^2 := by
  classical
  let G := (Pts.product Pts).filter (fun z => z.1∉Bad ∧ z.1≠z.2 ∧ ¬R z.1 z.2)
  let Rows := (Pts.filter (fun p => p∈Bad)).product Pts
  let Diag := Pts.image (fun p => (p,p))
  let Rich := (Pts.product Pts).filter (fun z => z.1∉Bad ∧ R z.1 z.2)
  have hcover : Pts.product Pts⊆((G∪Rows)∪Diag)∪Rich := by
    intro z hz
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hz
    by_cases hbad : z.1∈Bad
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hp,hbad⟩,hq⟩
    · by_cases heq : z.1=z.2
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        right
        exact Finset.mem_image.mpr ⟨z.1,hp,Prod.ext rfl heq⟩
      · by_cases hr : R z.1 z.2
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hp,hq⟩,hbad,hr⟩))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
            (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨hp,hq⟩,hbad,heq,hr⟩))))))
  have hcovercard : (Pts.card : ℝ)^2≤(G.card : ℝ)+Rows.card+Diag.card+Rich.card := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le ((G∪Rows)∪Diag) Rich
    have h3 := Finset.card_union_le (G∪Rows) Diag
    have h4 := Finset.card_union_le G Rows
    have hh : Pts.card^2≤G.card+Rows.card+Diag.card+Rich.card := by
      simp only [Finset.product_eq_sprod,Finset.card_product] at h1
      nlinarith only [h1,h2,h3,h4]
    exact_mod_cast hh
  have hRows : (Rows.card : ℝ)≤(Bad.card : ℝ)*Pts.card := by
    have hs : Pts.filter (fun p => p∈Bad)⊆Bad := fun p hp => (Finset.mem_filter.mp hp).2
    have h := Nat.mul_le_mul_right Pts.card (Finset.card_le_card hs)
    dsimp [Rows]
    simp only [Finset.card_product]
    exact_mod_cast h
  have hDiag : (Diag.card : ℝ)≤Pts.card := by exact_mod_cast Finset.card_image_le
  have hRichEq : Rich.card=∑ p∈Pts, (Pts.filter (fun q => p∉Bad ∧ R p q)).card := by
    simp only [Rich,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  have hRich : (Rich.card : ℝ)≤eta*(Pts.card : ℝ)^2 := by
    have hEq : (Rich.card : ℝ)=∑ p∈Pts, ((Pts.filter (fun q => p∉Bad ∧ R p q)).card : ℝ) := by
      exact_mod_cast hRichEq
    rw [hEq]
    calc
      _ ≤ ∑ _p∈Pts, eta*(Pts.card : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        by_cases hbad : p∈Bad
        · simp only [hbad,not_true_eq_false,false_and,Finset.filter_false,Finset.card_empty,Nat.cast_zero]
          exact mul_nonneg heta (Nat.cast_nonneg _)
        · simpa only [hbad,not_false_eq_true,true_and] using hrows p hp hbad
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  refine ⟨G,Finset.filter_subset _ _,?_,?_⟩
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · nlinarith only [hcovercard,hRows,hDiag,hRich]

end OriginalPairRowCut
