import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Finset
open scoped BigOperators Pointwise

noncomputable section

namespace OriginalDifferenceTranslatePullback

def difference {G : Type*} [AddCommGroup G] (p : G × G) : G := p.1 - p.2

def captured {G : Type*} [AddCommGroup G] [DecidableEq G]
    (D H : Finset G) (x : G) : Finset G := D.filter (fun d => d - x ∈ H)

def translatedSource {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S H : Finset G) (x : G) : Finset G := S.filter (fun s => s - x ∈ H)

/-- The lower bound is transported through ORIGINAL difference fibers and one
actual second endpoint. No new points or translate-overlap premise are supplied. -/
theorem exists_original_translate_pullback
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (E : Finset (G × G)) (H : Finset G) (x : G) (L : ℝ)
    (hS : S.Nonempty) (hE : E ⊆ S.product S)
    (hfiber : ∀ d ∈ E.image difference,
      L ≤ ((E.filter (fun p => difference p = d)).card : ℝ)) :
    ∃ t ∈ S,
      L * ((captured (E.image difference) H x).card : ℝ) ≤
        (S.card : ℝ) * (translatedSource S H (x + t)).card := by
  classical
  let D := E.image difference
  let C := captured D H x
  let Q := E.filter (fun p => difference p ∈ C)
  have hQE : Q ⊆ E := Finset.filter_subset _ _
  have hQS : Q ⊆ S.product S := hQE.trans hE
  have htotal : (Q.card : ℝ) =
      ∑ d ∈ C, ((E.filter (fun p => difference p = d)).card : ℝ) := by
    exact_mod_cast (Finset.sum_card_fiberwise_eq_card_filter
      (s := E) (t := C) (g := difference)).symm
  have hlower : L * (C.card : ℝ) ≤ (Q.card : ℝ) := by
    calc
      _ = ∑ _d ∈ C, L := by simp [mul_comm]
      _ ≤ ∑ d ∈ C, ((E.filter (fun p => difference p = d)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact hfiber d (Finset.mem_filter.mp hd).1
      _ = _ := htotal.symm
  have hsndmem : ∀ p ∈ Q, p.2 ∈ S := by
    intro p hp
    exact (Finset.mem_product.mp (hQS hp)).2
  have hpartition : (Q.card : ℝ) =
      ∑ t ∈ S, ((Q.filter (fun p => p.2 = t)).card : ℝ) := by
    have hfilter : Q.filter (fun p => p.2 ∈ S) = Q :=
      Finset.filter_eq_self.mpr hsndmem
    have hh := Finset.sum_card_fiberwise_eq_card_filter (s := Q) (t := S) (g := Prod.snd)
    rw [hfilter] at hh
    exact_mod_cast hh.symm
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image S
    (fun t => (Q.filter (fun p => p.2 = t)).card) hS
  have hmaxsum : (Q.card : ℝ) ≤
      (S.card : ℝ) * ((Q.filter (fun p => p.2 = t)).card : ℝ) := by
    rw [hpartition]
    calc
      _ ≤ ∑ _u ∈ S, ((Q.filter (fun p => p.2 = t)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        exact_mod_cast hmax u hu
      _ = _ := by simp
  have hrow : (Q.filter (fun p => p.2 = t)).card ≤
      (translatedSource S H (x + t)).card := by
    apply Finset.card_le_card_of_injOn (fun p : G × G => p.1)
    · intro p hp
      obtain ⟨hpQ, hpt⟩ := Finset.mem_filter.mp hp
      have hpS := (Finset.mem_product.mp (hQS hpQ)).1
      have hpC : difference p ∈ C := (Finset.mem_filter.mp hpQ).2
      have hcap : difference p - x ∈ H := (Finset.mem_filter.mp hpC).2
      have heq : difference p - x = p.1 - (x + t) := by
        dsimp [difference]
        rw [hpt]
        abel
      exact Finset.mem_filter.mpr ⟨hpS, heq ▸ hcap⟩
    · intro p hp q hq hpq
      have hpt := (Finset.mem_filter.mp hp).2
      have hqt := (Finset.mem_filter.mp hq).2
      exact Prod.ext hpq (hpt.trans hqt.symm)
  refine ⟨t, ht, ?_⟩
  exact hlower.trans (hmaxsum.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hrow) (Nat.cast_nonneg _)))

/-- Density form used to go backward through one constructed symmetry layer. -/
theorem exists_original_translate_pullback_density
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (E : Finset (G × G)) (H : Finset G) (x : G)
    (L beta sigma : ℝ)
    (hS : S.Nonempty) (hE : E ⊆ S.product S) (hL : 0 ≤ L) (hbeta : 0 ≤ beta)
    (hfiber : ∀ d ∈ E.image difference,
      L ≤ ((E.filter (fun p => difference p = d)).card : ℝ))
    (hcapture : beta * ((E.image difference).card : ℝ) ≤
      (captured (E.image difference) H x).card)
    (hscale : sigma * (S.card : ℝ) ^ 2 ≤ L * (E.image difference).card) :
    ∃ t ∈ S, beta * sigma * (S.card : ℝ) ≤ (translatedSource S H (x + t)).card := by
  obtain ⟨t, ht, hbound⟩ := exists_original_translate_pullback S E H x L hS hE hfiber
  have hN : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  refine ⟨t, ht, ?_⟩
  apply (mul_le_mul_iff_left₀ hN).mp
  have h1 := mul_le_mul_of_nonneg_left hscale hbeta
  have h2 := mul_le_mul_of_nonneg_left hcapture hL
  nlinarith only [h1, h2, hbound]

end OriginalDifferenceTranslatePullback
