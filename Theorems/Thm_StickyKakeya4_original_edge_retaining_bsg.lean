/-
The Markov-refinement proof adapts:
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the LeanFormalizations LICENSE.
Authors of the installed source: Adam McKenna.
The retained-edge construction and explicit conclusions below are new adaptations.
-/
import LeanFormalizations.Combinatorics.Additive.BalogSzemerediGowers

/- Source component: OriginalGraphBSGPruning -/

/- The Markov proof below adapts the installed Apache-2.0 BSG source by Adam McKenna.
The new public pruning and mass conclusions are used on literal original edges. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
noncomputable section
open scoped BigOperators Pointwise
namespace OriginalGraphBSGPruning
open Classical Finset

variable {G : Type*} [DecidableEq G]

lemma original_rectangle_card_columns (U B : Finset G) (E : Finset (G × G)) :
    ((E ∩ (U ×ˢ B)).card : ℝ)=∑ b∈B,((U.filter (fun a => (a,b)∈E)).card : ℝ) := by
  have he : E ∩ (U ×ˢ B)=(U ×ˢ B).filter (fun e => e∈E) := by
    ext e
    simp only [mem_inter,mem_filter]
    exact and_comm
  have hn : (E ∩ (U ×ˢ B)).card=∑ b∈B,(U.filter (fun a => (a,b)∈E)).card := by
    rw [he,card_eq_sum_ones,sum_filter,sum_product_right]
    simp only [card_eq_sum_ones,sum_filter]
  exact_mod_cast hn

lemma original_rectangle_card_rows (U B : Finset G) (E : Finset (G × G)) :
    ((E ∩ (U ×ˢ B)).card : ℝ)=∑ a∈U,((B.filter (fun b => (a,b)∈E)).card : ℝ) := by
  have he : E ∩ (U ×ˢ B)=(U ×ˢ B).filter (fun e => e∈E) := by
    ext e
    simp only [mem_inter,mem_filter]
    exact and_comm
  have hn : (E ∩ (U ×ˢ B)).card=∑ a∈U,(B.filter (fun b => (a,b)∈E)).card := by
    rw [he,card_eq_sum_ones,sum_filter,sum_product]
    simp only [card_eq_sum_ones,sum_filter]
  exact_mod_cast hn

theorem original_markov_half {G : Type*} [DecidableEq G]
    (B U : Finset G) (E : Finset (G × G)) (τ : ℝ) (κ : ℝ)
    (hκ_pos : 0 < κ) (hUpos : (0 : ℝ) < (U.card : ℝ))
    (hbadCount : (((U ×ˢ U).filter fun p : G × G ↦
        ((B.filter fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
      ≤ κ * (U.card : ℝ) ^ 2) :
    ∃ A' : Finset G, A' ⊆ U ∧
      (1 - 1 / 2) * (U.card : ℝ) ≤ (A'.card : ℝ) ∧
      (∀ a ∈ A',
        ((U.filter fun a₁ ↦
          ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
          ≤ 2 * κ * (U.card : ℝ)) := by
  classical
  -- Bad partners of `a` in U.
  set badPartner : G → Finset G := fun a ↦
    U.filter (fun a₁ ↦
      ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) < τ)
    with hbadPartner_def
  set A' : Finset G := U.filter (fun a ↦
    ((badPartner a).card : ℝ) ≤ 2 * κ * (U.card : ℝ)) with hA'_def
  have hA'_sub : A' ⊆ U := Finset.filter_subset _ _
  -- Sum of bad-partner cards equals bad-pair count (fiber over first coord).
  set badPairs : Finset (G × G) := (U ×ˢ U).filter (fun p : G × G ↦
    ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ)
    with hbadPairs_def
  have hbadSum : (badPairs.card : ℝ) = ∑ a ∈ U, ((badPartner a).card : ℝ) := by
    have hN : badPairs.card = ∑ a ∈ U, (badPartner a).card := by
      rw [hbadPairs_def, hbadPartner_def]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hcast : ((∑ a ∈ U, (badPartner a).card : ℕ) : ℝ) = (badPairs.card : ℝ) := by
      exact_mod_cast hN.symm
    push_cast at hcast; linarith
  -- Markov lower bound on Σ over U \ A'.
  have hsum_split :
      ∑ a ∈ U, ((badPartner a).card : ℝ) =
        (∑ a ∈ A', ((badPartner a).card : ℝ)) +
        ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := by
    rw [← Finset.sum_sdiff hA'_sub]; ring
  have hsum_diff_ge :
      ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) ≤
        ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := by
    rw [show ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) =
            ∑ _a ∈ U \ A', (2 * κ * (U.card : ℝ)) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a ha ↦ ?_
    rw [Finset.mem_sdiff, hA'_def, Finset.mem_filter] at ha
    have hnot := ha.2
    by_contra hge
    push Not at hge
    exact hnot ⟨ha.1, le_of_lt hge⟩
  have hpartner_nn : ∀ a, 0 ≤ ((badPartner a).card : ℝ) := fun a ↦ Nat.cast_nonneg _
  have hsum_A'_nn : 0 ≤ ∑ a ∈ A', ((badPartner a).card : ℝ) :=
    Finset.sum_nonneg fun a _ ↦ hpartner_nn a
  -- Combine: |U\A'| · 2κ|U| ≤ Σ over U ≤ |badPairs| ≤ κ|U|².  Hence |U\A'| ≤ |U|/2.
  have hdiff_card_le : ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) ≤
      κ * (U.card : ℝ) ^ 2 := by
    calc ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ))
        ≤ ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := hsum_diff_ge
      _ ≤ ∑ a ∈ U, ((badPartner a).card : ℝ) := by linarith
      _ = (badPairs.card : ℝ) := hbadSum.symm
      _ ≤ κ * (U.card : ℝ) ^ 2 := hbadCount
  have hcoeff_pos : 0 < 2 * κ * (U.card : ℝ) := by positivity
  have hdiff_le_half : ((U \ A').card : ℝ) ≤ (U.card : ℝ) / 2 := by
    have heq : κ * (U.card : ℝ) ^ 2 = ((U.card : ℝ) / 2) * (2 * κ * (U.card : ℝ)) := by ring
    rw [heq] at hdiff_card_le
    exact le_of_mul_le_mul_right hdiff_card_le hcoeff_pos
  have hA'_card_real : ((U \ A').card : ℝ) + (A'.card : ℝ) = (U.card : ℝ) := by
    have h : (U \ A').card + A'.card = U.card := Finset.card_sdiff_add_card_eq_card hA'_sub
    exact_mod_cast h
  have hA'_lb : (U.card : ℝ) / 2 ≤ (A'.card : ℝ) := by linarith
  refine ⟨A', hA'_sub, ?_, ?_⟩
  · linarith
  · intro a ha
    rw [hA'_def, Finset.mem_filter] at ha
    exact ha.2


/-- Popular columns are chosen against the actual retained left core.
The conclusion keeps the original edge mass on that exact rectangle. -/
theorem original_popular_columns_with_edges (U B : Finset G) (E : Finset (G × G))
    (rho : ℝ) (hrho : 0 < rho) (hU : 0 < (U.card : ℝ))
    (hrow : ∀ a∈U,rho*B.card ≤ ((B.filter (fun b => (a,b)∈E)).card : ℝ)) :
    ∃ B' : Finset G,B'⊆B ∧
      (rho/2)*B.card ≤ (B'.card : ℝ) ∧
      (rho/2)*U.card*B.card ≤ ((E ∩ (U ×ˢ B')).card : ℝ) ∧
      ∀ b∈B',(rho/2)*U.card ≤ ((U.filter (fun a => (a,b)∈E)).card : ℝ) := by
  let f := fun b => ((U.filter (fun a => (a,b)∈E)).card : ℝ)
  let B' := B.filter (fun b => (rho/2)*U.card ≤ f b)
  have hsub : B'⊆B := filter_subset _ _
  have htotal : rho*U.card*B.card ≤ ∑ b∈B,f b := by
    have hs := sum_le_sum hrow
    rw [← original_rectangle_card_rows U B E,original_rectangle_card_columns U B E] at hs
    simpa only [sum_const,nsmul_eq_mul,mul_left_comm,mul_comm,mul_assoc] using hs
  have hrare : (∑ b∈B\B',f b) ≤ (B.card : ℝ)*((rho/2)*U.card) := by
    calc
      _ ≤ ∑ _b∈B\B',(rho/2)*U.card := by
        apply sum_le_sum
        intro b hb
        obtain ⟨hbB,hbn⟩ := mem_sdiff.mp hb
        exact (lt_of_not_ge (fun hh => hbn (mem_filter.mpr ⟨hbB,hh⟩))).le
      _ = ((B\B').card : ℝ)*((rho/2)*U.card) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (card_le_card sdiff_subset)) (by positivity)
  have hsplit : (∑ b∈B',f b)+(∑ b∈B\B',f b)=∑ b∈B,f b := by
    rw [← sum_sdiff hsub]
    ring
  have hmass : (rho/2)*U.card*B.card ≤ ∑ b∈B',f b := by
    nlinarith only [htotal,hrare,hsplit]
  have hupper : (∑ b∈B',f b) ≤ (B'.card : ℝ)*U.card := by
    calc
      _ ≤ ∑ _b∈B',(U.card : ℝ) := sum_le_sum (fun _b _hb => Nat.cast_le.mpr (card_le_card (filter_subset _ _)))
      _ = _ := by simp
  have hcard : (rho/2)*B.card ≤ (B'.card : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right hU).mp
    nlinarith only [hmass,hupper]
  refine ⟨B',hsub,hcard,?_,?_⟩
  · rw [original_rectangle_card_columns]
    exact hmass
  · intro b hb
    exact (mem_filter.mp hb).2

end OriginalGraphBSGPruning

/- Source component: OriginalGraphBSGPaths -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators Pointwise
namespace OriginalGraphBSGPaths
open Classical Finset OriginalGraphBSGPruning
variable {G : Type*} [DecidableEq G]

def originalPaths (A B : Finset G) (E : Finset (G × G)) (a b : G) : Finset (G × G) :=
  (B ×ˢ A).filter (fun q => (a,q.1)∈E ∧ (q.2,q.1)∈E ∧ (q.2,b)∈E)

/-- Each good original middle vertex supplies its actual original common
neighbors, so their full path populations add without collisions. -/
theorem original_good_neighbor_path_count (A B U : Finset G) (E : Finset (G × G))
    (a b : G) (tau low high : ℝ) (htau : 0 ≤ tau) (hUA : U⊆A)
    (hbad : ((U.filter (fun u => ((B.filter (fun v => (a,v)∈E ∧ (u,v)∈E)).card : ℝ)<tau)).card : ℝ) ≤ low)
    (hpop : high ≤ ((U.filter (fun u => (u,b)∈E)).card : ℝ)) :
    (high-low)*tau ≤ ((originalPaths A B E a b).card : ℝ) := by
  let N := U.filter (fun u => (u,b)∈E)
  let Bad := U.filter (fun u => ((B.filter (fun v => (a,v)∈E ∧ (u,v)∈E)).card : ℝ)<tau)
  let Good := N\Bad
  have hGoodA : Good⊆A := (sdiff_subset.trans (filter_subset _ _)).trans hUA
  have hcover : N⊆Good∪Bad := by
    intro u hu
    by_cases hb : u∈Bad
    · exact mem_union_right _ hb
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hu,hb⟩)
  have hsumcard : (N.card : ℝ) ≤ (Good.card : ℝ)+Bad.card := by
    exact_mod_cast (card_le_card hcover).trans (card_union_le _ _)
  have hgood : high-low ≤ (Good.card : ℝ) := by
    linarith only [hsumcard,hbad,hpop]
  let f := fun u => ((B.filter (fun v => (a,v)∈E ∧ (u,v)∈E ∧ (u,b)∈E)).card : ℝ)
  have hf (u : G) (hu : u∈Good) : tau ≤ f u := by
    obtain ⟨huN,huBad⟩ := mem_sdiff.mp hu
    obtain ⟨huU,hub⟩ := mem_filter.mp huN
    have hcodeg : tau ≤ ((B.filter (fun v => (a,v)∈E ∧ (u,v)∈E)).card : ℝ) := by
      by_contra hn
      exact huBad (mem_filter.mpr ⟨huU,lt_of_not_ge hn⟩)
    have he : B.filter (fun v => (a,v)∈E ∧ (u,v)∈E ∧ (u,b)∈E)=
        B.filter (fun v => (a,v)∈E ∧ (u,v)∈E) := by
      ext v
      simp only [mem_filter,hub,and_true]
    change tau ≤ ((B.filter (fun v => (a,v)∈E ∧ (u,v)∈E ∧ (u,b)∈E)).card : ℝ)
    rw [he]
    exact hcodeg
  have hpaths : ((originalPaths A B E a b).card : ℝ)=∑ u∈A,f u := by
    have hn : (originalPaths A B E a b).card=
        ∑ u∈A,(B.filter (fun v => (a,v)∈E ∧ (u,v)∈E ∧ (u,b)∈E)).card := by
      rw [originalPaths,card_eq_sum_ones,sum_filter,sum_product_right]
      simp only [card_eq_sum_ones,sum_filter]
    dsimp only [f]
    exact_mod_cast hn
  calc
    _ ≤ (Good.card : ℝ)*tau := mul_le_mul_of_nonneg_right hgood htau
    _ = ∑ _u∈Good,tau := by simp
    _ ≤ ∑ u∈Good,f u := sum_le_sum hf
    _ ≤ ∑ u∈A,f u := sum_le_sum_of_subset_of_nonneg hGoodA (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := hpaths.symm

/-- DRC is followed by popular-column selection on the RETAINED half-core.
Consequently the rectangle keeps polynomially many ORIGINAL edges as well
as a pointwise population of original length-three paths. -/
theorem exists_original_edge_retaining_path_rectangle
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card=B.card)
    (E : Finset (G × G)) (hE : E⊆A ×ˢ B)
    (hdense : rho*(A.card : ℝ)^2 ≤ E.card) :
    ∃ A' B' : Finset G,A'⊆A ∧ B'⊆B ∧
      (rho^2/16)*A.card ≤ (A'.card : ℝ) ∧
      (rho/4)*A.card ≤ (B'.card : ℝ) ∧
      (rho^3/64)*(A.card : ℝ)^2 ≤ ((E∩(A' ×ˢ B')).card : ℝ) ∧
      ∀ a∈A',∀ b∈B',(rho^6/65536)*(A.card : ℝ)^2 ≤
        ((originalPaths A B E a b).card : ℝ) := by
  have hAn : 0 < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hBA : (B.card : ℝ)=(A.card : ℝ) := by exact_mod_cast hAB.symm
  have hB : B.Nonempty := card_pos.mp (by simpa only [← hAB] using hA.card_pos)
  have hdense' : rho*(A.card : ℝ)*B.card ≤ E.card := by
    rw [hBA]
    nlinarith only [hdense]
  obtain ⟨hA1,hE1⟩ := graph_high_degree_subset_lb rho hrho hrho1 A B hA hAB E hE hdense'
  let A1 := A.filter (fun a => (rho/2)*B.card ≤ ((B.filter (fun b => (a,b)∈E)).card : ℝ))
  let E1 := E.filter (fun p => (rho/2)*B.card ≤ ((B.filter (fun b => (p.1,b)∈E)).card : ℝ))
  have hA1A : A1⊆A := filter_subset _ _
  have hE1E : E1⊆E := filter_subset _ _
  have hA1pos : 0 < (A1.card : ℝ) := (by positivity : 0 < (rho/2)*(A.card : ℝ)).trans_le hA1
  have hA1ne : A1.Nonempty := card_pos.mp (Nat.cast_pos.mp hA1pos)
  have hE1sub : E1⊆A1 ×ˢ B := by
    intro p hp
    obtain ⟨hpE,hpop⟩ := mem_filter.mp hp
    obtain ⟨hpA,hpB⟩ := mem_product.mp (hE hpE)
    exact mem_product.mpr ⟨mem_filter.mpr ⟨hpA,hpop⟩,hpB⟩
  have hA1card : (A1.card : ℝ) ≤ A.card := Nat.cast_le.mpr (card_le_card hA1A)
  have hE1dense : (rho/2)*(A1.card : ℝ)*B.card ≤ E1.card := by
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA1card (by positivity : 0 ≤ rho/2))
      (Nat.cast_nonneg B.card)
    exact hm.trans hE1
  obtain ⟨U,hUA1,hUcard,hbadDRC⟩ := graph_pair_dependentRandomChoice A1 B hA1ne hB E1 hE1sub
    (rho/2) (by positivity) (by linarith only [hrho1]) hE1dense
    (rho/64) (by positivity) (by linarith only [hrho1])
  have hUA : U⊆A := hUA1.trans hA1A
  have hUlower : (rho^2/8)*A.card ≤ (U.card : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hA1 (show 0 ≤ rho/4 by positivity)
    nlinarith only [hm,hUcard]
  have hUpos : 0 < (U.card : ℝ) := (by positivity : 0 < (rho^2/8)*(A.card : ℝ)).trans_le hUlower
  let tau : ℝ := (rho^3/512)*B.card
  have htau : 0 ≤ tau := by dsimp [tau]; positivity
  have htau_eq : tau=((rho/64)*(rho/2)^2/2)*B.card := by dsimp [tau]; ring
  have hbad : (((U ×ˢ U).filter (fun p : G × G =>
      ((B.filter (fun b => (p.1,b)∈E ∧ (p.2,b)∈E)).card : ℝ)<tau)).card : ℝ) ≤
      (rho/64)*(U.card : ℝ)^2 := by
    have hsub : (U ×ˢ U).filter (fun p : G × G =>
        ((B.filter (fun b => (p.1,b)∈E ∧ (p.2,b)∈E)).card : ℝ)<tau) ⊆
        (U ×ˢ U).filter (fun p : G × G =>
        (((B.filter (fun b => (p.1,b)∈E1))∩(B.filter (fun b => (p.2,b)∈E1))).card : ℝ)<tau) := by
      intro p hp
      obtain ⟨hpU,hplt⟩ := mem_filter.mp hp
      have hs : (B.filter (fun b => (p.1,b)∈E1))∩(B.filter (fun b => (p.2,b)∈E1)) ⊆
          B.filter (fun b => (p.1,b)∈E ∧ (p.2,b)∈E) := by
        intro b hb
        obtain ⟨hb1,hb2⟩ := mem_inter.mp hb
        exact mem_filter.mpr ⟨(mem_filter.mp hb1).1,hE1E (mem_filter.mp hb1).2,hE1E (mem_filter.mp hb2).2⟩
      exact mem_filter.mpr ⟨hpU,(Nat.cast_le.mpr (card_le_card hs)).trans_lt hplt⟩
    have hh : (_ : ℝ) ≤ _ := Nat.cast_le.mpr (card_le_card hsub)
    apply hh.trans
    simpa only [htau_eq] using hbadDRC
  obtain ⟨A',hA'U,hA'half,hbadPartner⟩ := original_markov_half B U E tau (rho/64)
    (by positivity) hUpos hbad
  have hA'lower : (rho^2/16)*A.card ≤ (A'.card : ℝ) := by
    linarith only [hA'half,hUlower]
  have hA'pos : 0 < (A'.card : ℝ) := (by positivity : 0 < (rho^2/16)*(A.card : ℝ)).trans_le hA'lower
  have hrow (a : G) (ha : a∈A') :
      (rho/2)*B.card ≤ ((B.filter (fun b => (a,b)∈E)).card : ℝ) :=
    (mem_filter.mp (hUA1 (hA'U ha))).2
  obtain ⟨B',hB'B,hB'lower,hretained,hpopular⟩ := original_popular_columns_with_edges A' B E
    (rho/2) (by positivity) hA'pos hrow
  have hB'bound : (rho/4)*A.card ≤ (B'.card : ℝ) := by
    rw [hBA] at hB'lower
    linarith only [hB'lower]
  have hedges : (rho^3/64)*(A.card : ℝ)^2 ≤ ((E∩(A' ×ˢ B')).card : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hA'lower (show 0 ≤ rho/4 by positivity)) (Nat.cast_nonneg A.card)
    rw [hBA] at hretained
    nlinarith only [hm,hretained]
  refine ⟨A',B',hA'U.trans hUA,hB'B,hA'lower,hB'bound,hedges,?_⟩
  intro a ha b hb
  have hbadclean : ((U.filter (fun u =>
      ((B.filter (fun v => (a,v)∈E ∧ (u,v)∈E)).card : ℝ)<tau)).card : ℝ) ≤
      (rho/16)*U.card := by
    have hh := hbadPartner a ha
    have hnn : 0 ≤ rho*(U.card : ℝ) := by positivity
    nlinarith only [hh,hnn]
  have hpopclean : (rho/8)*U.card ≤ ((U.filter (fun u => (u,b)∈E)).card : ℝ) := by
    have hs : A'.filter (fun u => (u,b)∈E)⊆U.filter (fun u => (u,b)∈E) :=
      filter_subset_filter _ hA'U
    have hc : ((A'.filter (fun u => (u,b)∈E)).card : ℝ) ≤ (U.filter (fun u => (u,b)∈E)).card :=
      Nat.cast_le.mpr (card_le_card hs)
    have hm := mul_le_mul_of_nonneg_left hA'half (show 0 ≤ rho/4 by positivity)
    have hh := hpopular b hb
    nlinarith only [hm,hh,hc]
  have hp := original_good_neighbor_path_count A B U E a b tau ((rho/16)*U.card)
    ((rho/8)*U.card) htau hUA hbadclean hpopclean
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hUlower (show 0 ≤ rho/16 by positivity)) htau
  have hid : (rho/16)*((rho^2/8)*A.card)*tau=(rho^6/65536)*(A.card : ℝ)^2 := by
    dsimp [tau]
    rw [hBA]
    ring
  rw [hid] at hm
  nlinarith only [hm,hp]

end OriginalGraphBSGPaths

/- Source component: OriginalEdgeRetainingBSG -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
noncomputable section
open scoped BigOperators Pointwise
namespace OriginalEdgeRetainingBSG
open Classical Finset OriginalGraphBSGPaths
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Real path multiplicity is summed over distinct actual sums, avoiding
any floor loss at small source cardinalities. -/
theorem original_real_triple_multiplicity (A B S : Finset G) (M : ℝ)
    (hrep : ∀ a∈A,∀ b∈B,M ≤
      (((S ×ˢ S ×ˢ S).filter (fun p : G × G × G => p.1-p.2.1+p.2.2=a+b)).card : ℝ)) :
    M*(A+B).card ≤ (S.card : ℝ)^3 := by
  let F := S ×ˢ S ×ˢ S
  let f := fun p : G × G × G => p.1-p.2.1+p.2.2
  have hpoint (z : G) (hz : z∈A+B) : M ≤ ((F.filter (fun p => f p=z)).card : ℝ) := by
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hz
    exact hrep a ha b hb
  have hsum : (∑ z∈A+B,((F.filter (fun p => f p=z)).card : ℝ)) ≤ (F.card : ℝ) := by
    have hn : (∑ z∈A+B,(F.filter (fun p => f p=z)).card) ≤ F.card := by
      rw [sum_card_fiberwise_eq_card_filter]
      exact card_le_card (filter_subset _ _)
    exact_mod_cast hn
  calc
    _ = ∑ _z∈A+B,M := by simp [mul_comm]
    _ ≤ ∑ z∈A+B,((F.filter (fun p => f p=z)).card : ℝ) := sum_le_sum hpoint
    _ ≤ (F.card : ℝ) := hsum
    _ = _ := by dsimp [F]; simp only [card_product,Nat.cast_mul]; ring

/-- Equal-cardinality graph BSG retaining polynomially many ORIGINAL
edges. The selected alphabets, path witnesses, restricted sums and retained
edge set all come from the supplied graph; no edge-retention certificate is
assumed. This theorem applies in particular to the literal integer grids. -/
theorem exists_original_edge_retaining_bsg (rho K : ℝ) (hrho : 0 < rho) (_hK : 0 < K)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card=B.card)
    (E : Finset (G × G)) (hE : E⊆A ×ˢ B)
    (hdense : rho*(A.card : ℝ)^2 ≤ E.card)
    (hsums : ((E.image (fun p => p.1+p.2)).card : ℝ) ≤ K*A.card) :
    ∃ A' B' : Finset G,A'⊆A ∧ B'⊆B ∧
      (rho^2/16)*A.card ≤ (A'.card : ℝ) ∧
      (rho/4)*A.card ≤ (B'.card : ℝ) ∧
      (rho^3/64)*(A.card : ℝ)^2 ≤ ((E∩(A' ×ˢ B')).card : ℝ) ∧
      ((A'+B').card : ℝ) ≤ (65536*K^3/rho^6)*A.card := by
  have hAn : 0 < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hEcard : (E.card : ℝ) ≤ (A.card : ℝ)^2 := by
    have hh := (card_le_card hE).trans_eq (card_product A B)
    rw [← hAB] at hh
    have hhR : (E.card : ℝ) ≤ (A.card : ℝ)*(A.card : ℝ) := by exact_mod_cast hh
    nlinarith only [hhR]
  have hrho1 : rho ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hAn)).mp
    simpa only [one_mul] using hdense.trans hEcard
  obtain ⟨A',B',hA'A,hB'B,hA'lower,hB'lower,hedges,hpaths⟩ :=
    exists_original_edge_retaining_path_rectangle rho hrho hrho1 A B hA hAB E hE hdense
  let S := E.image (fun p => p.1+p.2)
  let M := (rho^6/65536)*(A.card : ℝ)^2
  have hM : 0 < M := by dsimp [M]; positivity
  have hrep (a : G) (ha : a∈A') (b : G) (hb : b∈B') : M ≤
      (((S ×ˢ S ×ˢ S).filter (fun p : G × G × G => p.1-p.2.1+p.2.2=a+b)).card : ℝ) := by
    have hh := path3_count_le_triple_rep_count A B S E
      (fun p hp => mem_image_of_mem _ hp) a b
    exact (hpaths a ha b hb).trans (Nat.cast_le.mpr hh)
  have hmulti := original_real_triple_multiplicity A' B' S M hrep
  have hScube : (S.card : ℝ)^3 ≤ K^3*(A.card : ℝ)^3 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg S.card) hsums 3
    nlinarith only [hh]
  have hbound : ((A'+B').card : ℝ) ≤ (65536*K^3/rho^6)*A.card := by
    apply (mul_le_mul_iff_of_pos_left hM).mp
    have he : M*((65536*K^3/rho^6)*A.card)=K^3*(A.card : ℝ)^3 := by
      dsimp [M]
      field_simp [ne_of_gt hrho]
    rw [he]
    exact hmulti.trans hScube
  exact ⟨A',B',hA'A,hB'B,hA'lower,hB'lower,hedges,hbound⟩

end OriginalEdgeRetainingBSG

/- Source component: OriginalUnequalEdgeRetainingBSG -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open scoped Pointwise
namespace OriginalUnequalEdgeRetainingBSG
open Classical Finset OriginalEdgeRetainingBSG
variable {G : Type*} [DecidableEq G]

/-- Restricting a union-core rectangle back to the two ORIGINAL alphabets
preserves its retained original edges exactly. -/
theorem original_intersected_core_edge_identity (A B U V : Finset G)
    (E : Finset (G × G)) (hE : E⊆A ×ˢ B) :
    E∩((U∩A) ×ˢ (V∩B))=E∩(U ×ˢ V) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpE,hpUV⟩ := mem_inter.mp hp
    obtain ⟨hpUA,hpVB⟩ := mem_product.mp hpUV
    exact mem_inter.mpr ⟨hpE,mem_product.mpr ⟨(mem_inter.mp hpUA).1,(mem_inter.mp hpVB).1⟩⟩
  · intro hp
    obtain ⟨hpE,hpUV⟩ := mem_inter.mp hp
    obtain ⟨hpU,hpV⟩ := mem_product.mp hpUV
    obtain ⟨hpA,hpB⟩ := mem_product.mp (hE hpE)
    exact mem_inter.mpr ⟨hpE,mem_product.mpr ⟨mem_inter.mpr ⟨hpU,hpA⟩,mem_inter.mpr ⟨hpV,hpB⟩⟩⟩

/-- Unequal original alphabets are embedded into their ACTUAL union on
both sides. Returning to the original alphabets keeps the same original
edge set and only shrinks the full sumset. -/
theorem exists_original_unequal_edge_retaining_bsg [AddCommGroup G]
    (rho K : ℝ) (hrho : 0 < rho) (hK : 0 < K)
    (A B : Finset G) (hC : (A∪B).Nonempty)
    (E : Finset (G × G)) (hE : E⊆A ×ˢ B)
    (hdense : rho*((A∪B).card : ℝ)^2 ≤ E.card)
    (hsums : ((E.image (fun p => p.1+p.2)).card : ℝ) ≤ K*(A∪B).card) :
    ∃ A' B' : Finset G,A'⊆A ∧ B'⊆B ∧
      (rho^3/64)*(A∪B).card ≤ (A'.card : ℝ) ∧
      (rho^3/64)*(A∪B).card ≤ (B'.card : ℝ) ∧
      (rho^3/64)*((A∪B).card : ℝ)^2 ≤ ((E∩(A' ×ˢ B')).card : ℝ) ∧
      ((A'+B').card : ℝ) ≤ (65536*K^3/rho^6)*(A∪B).card := by
  let C := A∪B
  have hCC : E⊆C ×ˢ C := by
    intro p hp
    obtain ⟨hpA,hpB⟩ := mem_product.mp (hE hp)
    exact mem_product.mpr ⟨mem_union_left _ hpA,mem_union_right _ hpB⟩
  obtain ⟨U,V,hUC,hVC,_hUcard,_hVcard,hretain,hsum⟩ :=
    exists_original_edge_retaining_bsg rho K hrho hK C C hC rfl E hCC hdense hsums
  let A' := U∩A
  let B' := V∩B
  have hA'C : A'⊆C := inter_subset_left.trans hUC
  have hB'C : B'⊆C := inter_subset_left.trans hVC
  have hidentity : E∩(A' ×ˢ B')=E∩(U ×ˢ V) :=
    original_intersected_core_edge_identity A B U V E hE
  have hedges : (rho^3/64)*(C.card : ℝ)^2 ≤ ((E∩(A' ×ˢ B')).card : ℝ) := by
    rw [hidentity]
    exact hretain
  have hN : 0 < (C.card : ℝ) := Nat.cast_pos.mpr hC.card_pos
  have hAc : (A'.card : ℝ) ≤ C.card := Nat.cast_le.mpr (card_le_card hA'C)
  have hBc : (B'.card : ℝ) ≤ C.card := Nat.cast_le.mpr (card_le_card hB'C)
  have hproduct : ((E∩(A' ×ˢ B')).card : ℝ) ≤ (A'.card : ℝ)*B'.card := by
    exact_mod_cast (card_le_card (inter_subset_right (s₁:=E) (s₂:=A' ×ˢ B'))).trans_eq (card_product A' B')
  have hAcard : (rho^3/64)*C.card ≤ (A'.card : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right hN).mp
    have hh := mul_le_mul_of_nonneg_left hBc (Nat.cast_nonneg A'.card)
    nlinarith only [hedges,hproduct,hh]
  have hBcard : (rho^3/64)*C.card ≤ (B'.card : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right hN).mp
    have hh := mul_le_mul_of_nonneg_right hAc (Nat.cast_nonneg B'.card)
    nlinarith only [hedges,hproduct,hh]
  have hsumsub : A'+B'⊆U+V := add_subset_add inter_subset_left inter_subset_left
  exact ⟨A',B',inter_subset_right,inter_subset_right,hAcard,hBcard,hedges,
    (Nat.cast_le.mpr (card_le_card hsumsub)).trans hsum⟩

/-- The literal source-size normalization used by projection graphs.
Neither equality of the original alphabet sizes nor a separate density
upper bound is assumed; both union normalization and lambda<=1 are derived
from the actual original graph. -/
theorem exists_original_size_normalized_edge_retaining_bsg [AddCommGroup G]
    (lam K M : ℝ) (hlam : 0 < lam) (hK : 0 < K) (hM : 0 < M)
    (A B : Finset G) (hA : (A.card : ℝ) ≤ M) (hB : (B.card : ℝ) ≤ M)
    (E : Finset (G × G)) (hE : E⊆A ×ˢ B)
    (hdense : lam*M^2 ≤ E.card)
    (hsums : ((E.image (fun p => p.1+p.2)).card : ℝ) ≤ K*M) :
    ∃ A' B' : Finset G,A'⊆A ∧ B'⊆B ∧
      (lam^4/4096)*M ≤ (A'.card : ℝ) ∧
      (lam^4/4096)*M ≤ (B'.card : ℝ) ∧
      (lam^4/4096)*M^2 ≤ ((E∩(A' ×ˢ B')).card : ℝ) ∧
      ((A'+B').card : ℝ) ≤ (536870912*K^3/lam^9)*M := by
  let C := A∪B
  have hEprod : (E.card : ℝ) ≤ (A.card : ℝ)*B.card := by
    exact_mod_cast (card_le_card hE).trans_eq (card_product A B)
  have hprod : (A.card : ℝ)*B.card ≤ M^2 := by
    have hh := mul_le_mul hA hB (Nat.cast_nonneg B.card) hM.le
    nlinarith only [hh]
  have hlam1 : lam ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hM)).mp
    simpa only [one_mul] using hdense.trans (hEprod.trans hprod)
  have hEpos : 0 < (E.card : ℝ) := (by positivity : 0 < lam*M^2).trans_le hdense
  have hEne : E.Nonempty := card_pos.mp (Nat.cast_pos.mp hEpos)
  have hC : C.Nonempty := by
    obtain ⟨p,hp⟩ := hEne
    exact ⟨p.1,mem_union_left _ (mem_product.mp (hE hp)).1⟩
  have hN : 0 < (C.card : ℝ) := Nat.cast_pos.mpr hC.card_pos
  have hNupper : (C.card : ℝ) ≤ 2*M := by
    have hh : (C.card : ℝ) ≤ (A.card : ℝ)+B.card := by exact_mod_cast card_union_le A B
    linarith only [hh,hA,hB]
  have hCC : E⊆C ×ˢ C := by
    intro p hp
    obtain ⟨hpA,hpB⟩ := mem_product.mp (hE hp)
    exact mem_product.mpr ⟨mem_union_left _ hpA,mem_union_right _ hpB⟩
  have hEsq : (E.card : ℝ) ≤ (C.card : ℝ)^2 := by
    have hh : (E.card : ℝ) ≤ (C.card : ℝ)*C.card := by
      exact_mod_cast (card_le_card hCC).trans_eq (card_product C C)
    nlinarith only [hh]
  have hNlowerSq : lam*M^2 ≤ (C.card : ℝ)^2 := hdense.trans hEsq
  have hNlower : lam*M ≤ (C.card : ℝ) := by
    have hll : lam^2 ≤ lam := by nlinarith only [hlam,hlam1]
    have hh := mul_le_mul_of_nonneg_right hll (sq_nonneg M)
    have hpos : 0 ≤ lam*M := by positivity
    apply (sq_le_sq₀ hpos hN.le).mp
    nlinarith only [hNlowerSq,hh]
  have hD : (lam/4)*(C.card : ℝ)^2 ≤ E.card := by
    have hsq := pow_le_pow_left₀ hN.le hNupper 2
    have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ lam/4 by positivity)
    nlinarith only [hh,hdense]
  have hS : ((E.image (fun p => p.1+p.2)).card : ℝ) ≤ (K/lam)*C.card := by
    apply hsums.trans
    have hh := mul_le_mul_of_nonneg_left hNlower (show 0 ≤ K/lam by positivity)
    have he : (K/lam)*(lam*M)=K*M := by field_simp
    rwa [he] at hh
  obtain ⟨A',B',hA'A,hB'B,hA'card,hB'card,hedges,hsum⟩ :=
    exists_original_unequal_edge_retaining_bsg (lam/4) (K/lam) (by positivity) (by positivity)
      A B hC E hE hD hS
  have hcoeff : (lam/4)^3/64=lam^3/4096 := by ring
  have hcards : (lam^4/4096)*M ≤ ((lam/4)^3/64)*C.card := by
    rw [hcoeff]
    have hh := mul_le_mul_of_nonneg_left hNlower (show 0 ≤ lam^3/4096 by positivity)
    nlinarith only [hh]
  have hretained : (lam^4/4096)*M^2 ≤ ((E∩(A' ×ˢ B')).card : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hNlowerSq (show 0 ≤ lam^3/4096 by positivity)
    rw [hcoeff] at hedges
    nlinarith only [hh,hedges]
  let F : ℝ := 65536*(K/lam)^3/(lam/4)^6
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hFidentity : F*(2*M)=(536870912*K^3/lam^9)*M := by
    dsimp [F]
    field_simp [ne_of_gt hlam]
    ring
  have hfull : ((A'+B').card : ℝ) ≤ (536870912*K^3/lam^9)*M := by
    calc
      _ ≤ F*C.card := hsum
      _ ≤ F*(2*M) := mul_le_mul_of_nonneg_left hNupper hF
      _ = _ := hFidentity
  exact ⟨A',B',hA'A,hB'B,hcards.trans hA'card,hcards.trans hB'card,hretained,hfull⟩

end OriginalUnequalEdgeRetainingBSG
