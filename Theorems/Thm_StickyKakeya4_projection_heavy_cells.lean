import Theorems.Thm_StickyKakeya4_projection_pair_slope_interval
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Finset
open scoped BigOperators

noncomputable section

namespace ProjectionHeavyCells

def cell {α β : Type*} [DecidableEq β]
    (P : Finset α) (f : α → β) (p : α) : Finset α :=
  P.filter (fun q => f q = f p)

def heavy {α β : Type*} [DecidableEq β]
    (P : Finset α) (f : α → β) (a : ℝ) : Finset α := by
  classical
  exact P.filter (fun p => a < ((cell P f p).card : ℝ))

theorem heavy_subset {α β : Type*} [DecidableEq β]
    (P : Finset α) (f : α → β) (a : ℝ) : heavy P f a ⊆ P := by
  classical
  exact Finset.filter_subset _ _

theorem heavy_point_far_population
    {α β : Type*} [DecidableEq β]
    (P : Finset α) (f : α → β) (R : α → α → Prop)
    [DecidableRel R] (a b : ℝ)
    (hab : 2 * b ≤ a)
    (hnear : ∀ p ∈ P, ((P.filter (fun q => ¬ R p q)).card : ℝ) ≤ b)
    {p : α} (hp : p ∈ heavy P f a) :
    a / 2 ≤ (((cell P f p).filter (fun q => R p q)).card : ℝ) := by
  classical
  have hpP := (Finset.mem_filter.mp hp).1
  have hmass : a < ((cell P f p).card : ℝ) := (Finset.mem_filter.mp hp).2
  have hsub : (cell P f p).filter (fun q => ¬ R p q) ⊆
      P.filter (fun q => ¬ R p q) := by
    intro q hq
    obtain ⟨hqcell, hqR⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hqcell).1, hqR⟩
  have hn : (((cell P f p).filter (fun q => ¬ R p q)).card : ℝ) ≤ b := by
    have hc : (((cell P f p).filter (fun q => ¬ R p q)).card : ℝ) ≤
        ((P.filter (fun q => ¬ R p q)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hc.trans (hnear p hpP)
  have hc : (((cell P f p).filter (fun q => R p q)).card : ℝ) +
      (((cell P f p).filter (fun q => ¬ R p q)).card : ℝ) =
      ((cell P f p).card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not
      (s := cell P f p) (fun q => R p q))
  linarith

theorem heavy_mass_le_far_pairs
    {α β : Type*} [DecidableEq β]
    (P : Finset α) (f : α → β) (R S : α → α → Prop)
    [DecidableRel R] [DecidableRel S] (a b : ℝ)
    (hab : 2 * b ≤ a)
    (hnear : ∀ p ∈ P, ((P.filter (fun q => ¬ R p q)).card : ℝ) ≤ b)
    (hcell : ∀ p ∈ P, ∀ q ∈ P, f q = f p → S p q) :
    (a / 2) * ((heavy P f a).card : ℝ) ≤
      ∑ p ∈ P, ((P.filter (fun q => R p q ∧ S p q)).card : ℝ) := by
  classical
  have hpoint : ∀ p ∈ heavy P f a, a / 2 ≤
      ((P.filter (fun q => R p q ∧ S p q)).card : ℝ) := by
    intro p hp
    have hpP := heavy_subset P f a hp
    have hsub : (cell P f p).filter (fun q => R p q) ⊆
        P.filter (fun q => R p q ∧ S p q) := by
      intro q hq
      obtain ⟨hqcell, hqR⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqP, hqf⟩ := Finset.mem_filter.mp hqcell
      exact Finset.mem_filter.mpr ⟨hqP, hqR, hcell p hpP q hqP hqf⟩
    exact (heavy_point_far_population P f R a b hab hnear hp).trans
      (by exact_mod_cast Finset.card_le_card hsub)
  calc
    (a / 2) * ((heavy P f a).card : ℝ) = ∑ _p ∈ heavy P f a, a / 2 := by
      simp [mul_comm]
    _ ≤ ∑ p ∈ heavy P f a,
        ((P.filter (fun q => R p q ∧ S p q)).card : ℝ) := Finset.sum_le_sum hpoint
    _ ≤ ∑ p ∈ P, ((P.filter (fun q => R p q ∧ S p q)).card : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (heavy_subset P f a)
        (fun _ _ _ => Nat.cast_nonneg _)

theorem card_far_pairs_eq_sum
    {α : Type*} (P : Finset α) (R : α → α → Prop) [DecidableRel R] :
    (((P.product P).filter (fun pq => R pq.1 pq.2)).card : ℝ) =
      ∑ p ∈ P, ((P.filter (fun q => R p q)).card : ℝ) := by
  classical
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]

theorem same_floor_difference {r y z : ℝ} (hr : 0 < r)
    (hcell : ⌊y / r⌋ = ⌊z / r⌋) : |y - z| < r := by
  have hylo := (le_div_iff₀ hr).mp (Int.floor_le (y / r))
  have hyhi := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one (y / r))
  have hzlo := (le_div_iff₀ hr).mp (Int.floor_le (z / r))
  have hzhi := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one (z / r))
  rw [hcell] at hylo hyhi
  exact abs_lt.mpr ⟨by nlinarith, by nlinarith⟩

def projection (lam : ℝ) (p : ℝ × ℝ) : ℝ := p.1 - lam * p.2

def distance (p q : ℝ × ℝ) : ℝ :=
  ProjectionPairSlopeInterval.pairDistance (p.1 - q.1) (p.2 - q.2)

def projectionCell (lam r : ℝ) (p : ℝ × ℝ) : ℤ := ⌊projection lam p / r⌋

def farPairs (P : Finset (ℝ × ℝ)) (lam r : ℝ) : Finset ((ℝ × ℝ) × (ℝ × ℝ)) := by
  classical
  exact (P.product P).filter (fun pq =>
    4 * r ≤ distance pq.1 pq.2 ∧ |projection lam pq.1 - projection lam pq.2| ≤ r)

theorem projection_heavy_mass_le_far_pairs
    (P : Finset (ℝ × ℝ)) (lam r a b : ℝ) (hr : 0 < r)
    (hab : 2 * b ≤ a)
    (hnear : ∀ p ∈ P, ((P.filter (fun q => distance p q < 4 * r)).card : ℝ) ≤ b) :
    (a / 2) * ((heavy P (projectionCell lam r) a).card : ℝ) ≤
      ((farPairs P lam r).card : ℝ) := by
  classical
  have hn : ∀ p ∈ P, ((P.filter (fun q => ¬ 4 * r ≤ distance p q)).card : ℝ) ≤ b := by
    simpa only [not_le] using hnear
  have hc : ∀ p ∈ P, ∀ q ∈ P, projectionCell lam r q = projectionCell lam r p →
      |projection lam p - projection lam q| ≤ r := by
    intro p _hp q _hq heq
    exact (same_floor_difference hr heq.symm).le
  have h := heavy_mass_le_far_pairs P (projectionCell lam r)
    (fun p q => 4 * r ≤ distance p q)
    (fun p q => |projection lam p - projection lam q| ≤ r) a b hab hn hc
  exact h.trans_eq (card_far_pairs_eq_sum P
    (fun p q => 4 * r ≤ distance p q ∧ |projection lam p - projection lam q| ≤ r)).symm

def badUnion (P : Finset (ℝ × ℝ)) (scales : Finset ℝ) (lam A t : ℝ) :
    Finset (ℝ × ℝ) := by
  classical
  exact scales.biUnion (fun r => heavy P (projectionCell lam r) (A * r ^ t * P.card))

def retained (P : Finset (ℝ × ℝ)) (scales : Finset ℝ) (lam A t : ℝ) :
    Finset (ℝ × ℝ) := by
  classical
  exact P \ badUnion P scales lam A t

theorem badUnion_subset (P : Finset (ℝ × ℝ)) (scales : Finset ℝ) (lam A t : ℝ) :
    badUnion P scales lam A t ⊆ P := by
  classical
  intro p hp
  obtain ⟨r, _hr, hp⟩ := Finset.mem_biUnion.mp hp
  exact heavy_subset P _ _ hp

theorem retained_subset (P : Finset (ℝ × ℝ)) (scales : Finset ℝ) (lam A t : ℝ) :
    retained P scales lam A t ⊆ P := by
  classical
  exact Finset.sdiff_subset

theorem badUnion_card_le_sum (P : Finset (ℝ × ℝ)) (scales : Finset ℝ) (lam A t : ℝ) :
    ((badUnion P scales lam A t).card : ℝ) ≤
      ∑ r ∈ scales, ((heavy P (projectionCell lam r) (A * r ^ t * P.card)).card : ℝ) := by
  classical
  exact_mod_cast (Finset.card_biUnion_le (s := scales)
    (t := fun r => heavy P (projectionCell lam r) (A * r ^ t * P.card)))

theorem retained_original_cell_bound
    (P : Finset (ℝ × ℝ)) (scales : Finset ℝ) (lam A t : ℝ)
    {r : ℝ} (hr : r ∈ scales) {p : ℝ × ℝ}
    (hp : p ∈ retained P scales lam A t) :
    ((cell P (projectionCell lam r) p).card : ℝ) ≤ A * r ^ t * P.card := by
  classical
  obtain ⟨hpP, hpnot⟩ := Finset.mem_sdiff.mp hp
  by_contra h
  have hh : p ∈ heavy P (projectionCell lam r) (A * r ^ t * P.card) := by
    exact Finset.mem_filter.mpr ⟨hpP, lt_of_not_ge h⟩
  exact hpnot (Finset.mem_biUnion.mpr ⟨r, hr, hh⟩)

theorem good_slopes_of_bad_budget
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (Lambda : Finset β) (bad : β → Finset α) (q : ℝ)
    (hP : P.Nonempty) (hq : 0 < q)
    (hbudget : (∑ lam ∈ Lambda, ((bad lam).card : ℝ)) ≤
      q ^ 2 * (P.card : ℝ) * (Lambda.card : ℝ)) :
    (1 - q) * (Lambda.card : ℝ) ≤
      ((Lambda.filter (fun lam => ((bad lam).card : ℝ) ≤ q * P.card)).card : ℝ) := by
  classical
  let Bad := Lambda.filter (fun lam => q * (P.card : ℝ) < ((bad lam).card : ℝ))
  let Good := Lambda.filter (fun lam => ((bad lam).card : ℝ) ≤ q * P.card)
  have hN : 0 < (P.card : ℝ) := by exact_mod_cast hP.card_pos
  have hparts : (Bad.card : ℝ) + (Good.card : ℝ) = (Lambda.card : ℝ) := by
    have hh := Finset.card_filter_add_card_filter_not (s := Lambda)
      (fun lam => q * (P.card : ℝ) < ((bad lam).card : ℝ))
    simp only [not_lt] at hh
    exact_mod_cast hh
  have hsum : q * (P.card : ℝ) * (Bad.card : ℝ) ≤
      ∑ lam ∈ Lambda, ((bad lam).card : ℝ) := by
    calc
      q * (P.card : ℝ) * (Bad.card : ℝ) = ∑ _lam ∈ Bad, q * (P.card : ℝ) := by
        simp [mul_comm]
      _ ≤ ∑ lam ∈ Bad, ((bad lam).card : ℝ) := by
        exact Finset.sum_le_sum (fun lam hlam => (Finset.mem_filter.mp hlam).2.le)
      _ ≤ ∑ lam ∈ Lambda, ((bad lam).card : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Nat.cast_nonneg _)
  have hbad : (Bad.card : ℝ) ≤ q * (Lambda.card : ℝ) := by
    apply (mul_le_mul_iff_right₀ (mul_pos hq hN)).mp
    calc
      (q * (P.card : ℝ)) * (Bad.card : ℝ) ≤
          q ^ 2 * (P.card : ℝ) * (Lambda.card : ℝ) := hsum.trans hbudget
      _ = (q * (P.card : ℝ)) * (q * (Lambda.card : ℝ)) := by ring
  change (1 - q) * (Lambda.card : ℝ) ≤ (Good.card : ℝ)
  nlinarith

theorem retained_card_of_good
    (P : Finset (ℝ × ℝ)) (scales : Finset ℝ) (lam A t q : ℝ)
    (hgood : ((badUnion P scales lam A t).card : ℝ) ≤ q * P.card) :
    (1 - q) * (P.card : ℝ) ≤ (retained P scales lam A t).card := by
  classical
  have hc : ((retained P scales lam A t).card : ℝ) +
      ((badUnion P scales lam A t).card : ℝ) = (P.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (badUnion_subset P scales lam A t)
  nlinarith

theorem floor_two_interval {u c h : ℝ} (hh : 0 < h) (hu : |u - c| ≤ 2 * h) :
    ⌊u / h⌋ ∈ Finset.Icc (⌊c / h⌋ - 2) (⌊c / h⌋ + 2) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hu
  have hup : u / h ≤ c / h + 2 := by
    apply (div_le_iff₀ hh).2
    have heq : (c / h + 2) * h = c + 2 * h := by field_simp
    rw [heq]
    linarith
  have hdown : c / h ≤ u / h + 2 := by
    apply (div_le_iff₀ hh).2
    have heq : (u / h + 2) * h = u + 2 * h := by field_simp
    rw [heq]
    linarith
  have huInt : ⌊u / h⌋ ≤ ⌊c / h⌋ + 2 := by simpa using Int.floor_mono hup
  have hlInt : ⌊c / h⌋ ≤ ⌊u / h⌋ + 2 := by simpa using Int.floor_mono hdown
  exact Finset.mem_Icc.mpr ⟨by omega, huInt⟩

theorem retained_interval_bound
    (P Q : Finset (ℝ × ℝ)) (scales : Finset ℝ) (lam A t c r h : ℝ)
    (hA : 0 ≤ A) (hh : 0 < h) (hhmem : h ∈ scales) (hrh : r ≤ 2 * h)
    (hQ : Q ⊆ retained P scales lam A t) :
    ((Q.filter (fun p => |projection lam p - c| ≤ r)).card : ℝ) ≤
      5 * A * h ^ t * P.card := by
  classical
  let S := Q.filter (fun p => |projection lam p - c| ≤ r)
  let f := projectionCell lam h
  let J := S.image f
  let k0 : ℤ := ⌊c / h⌋
  have hJsub : J ⊆ Finset.Icc (k0 - 2) (k0 + 2) := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    have hpc : |projection lam p - c| ≤ r := (Finset.mem_filter.mp hp).2
    exact floor_two_interval hh (hpc.trans hrh)
  have hJcard : J.card ≤ 5 := by
    have hI : (Finset.Icc (k0 - 2) (k0 + 2)).card = 5 := by
      rw [Int.card_Icc]
      have heq : k0 + 2 + 1 - (k0 - 2) = (5 : ℤ) := by ring
      rw [heq]
      rfl
    exact (Finset.card_le_card hJsub).trans_eq hI
  have hfiber : ∀ k ∈ J, ((S.filter (fun p => f p = k)).card : ℝ) ≤ A * h ^ t * P.card := by
    intro k hk
    obtain ⟨p, hpS, hpk⟩ := Finset.mem_image.mp hk
    have hpQ := (Finset.mem_filter.mp hpS).1
    have hpRet := hQ hpQ
    have hsub : S.filter (fun q => f q = k) ⊆ cell P f p := by
      intro q hq
      obtain ⟨hqS, hqk⟩ := Finset.mem_filter.mp hq
      have hqQ := (Finset.mem_filter.mp hqS).1
      have hqP := retained_subset P scales lam A t (hQ hqQ)
      exact Finset.mem_filter.mpr ⟨hqP, hqk.trans hpk.symm⟩
    have hc : ((S.filter (fun q => f q = k)).card : ℝ) ≤ ((cell P f p).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hc.trans (retained_original_cell_bound P scales lam A t hhmem hpRet)
  have ha : 0 ≤ A * h ^ t * (P.card : ℝ) := by positivity
  calc
    ((Q.filter (fun p => |projection lam p - c| ≤ r)).card : ℝ) =
        ∑ k ∈ J, ((S.filter (fun p => f p = k)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image f S
    _ ≤ ∑ _k ∈ J, A * h ^ t * (P.card : ℝ) := Finset.sum_le_sum hfiber
    _ = (J.card : ℝ) * (A * h ^ t * (P.card : ℝ)) := by simp
    _ ≤ 5 * (A * h ^ t * (P.card : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ ha
      exact_mod_cast hJcard
    _ = _ := by ring

end ProjectionHeavyCells
