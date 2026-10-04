import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

namespace SymmetrySetDifferenceStep

open scoped BigOperators

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- The original points witnessing translation by `g`. -/
def overlap (Y : Finset G) (g : G) : Finset G := by
  classical
  exact Y.filter (fun y => y - g ∈ Y)

/-- All actual differences, with no ambient finiteness assumption. -/
def differences (Y : Finset G) : Finset G := by
  classical
  exact (Y.product Y).image (fun p => p.1 - p.2)

/-- Positive-density symmetry set, supported on actual differences. -/
def symmetrySet (Y : Finset G) (a : ℝ) : Finset G := by
  classical
  exact (differences Y).filter (fun g => a * (Y.card : ℝ) ≤ (overlap Y g).card)

def incidenceFiber (Y S : Finset G) (y : G) : Finset G := by
  classical
  exact S.filter (fun s => y - s ∈ Y)

def commonWitnesses (Y : Finset G) (s t : G) : Finset G := by
  classical
  exact Y.filter (fun y => y - s ∈ Y ∧ y - t ∈ Y)

def differenceEnergy (Y S : Finset G) : ℝ :=
  ∑ p ∈ S.product S, ((overlap Y (p.1 - p.2)).card : ℝ)

/-- This keeps the original ordered pairs, including diagonal pairs. -/
def goodPairs (Y S : Finset G) (a : ℝ) : Finset (G × G) := by
  classical
  exact (S.product S).filter (fun p => p.1 - p.2 ∈ symmetrySet Y a)

lemma overlap_subset (Y : Finset G) (g : G) : overlap Y g ⊆ Y := by
  classical
  exact Finset.filter_subset _ _

lemma overlap_card_le (Y : Finset G) (g : G) :
    (overlap Y g).card ≤ Y.card := Finset.card_le_card (overlap_subset Y g)

lemma mem_symmetrySet_iff {Y : Finset G} {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (g : G) :
    g ∈ symmetrySet Y a ↔ a * (Y.card : ℝ) ≤ (overlap Y g).card := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    have hypos : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
    have hcpos : (0 : ℝ) < (overlap Y g).card := (mul_pos ha hypos).trans_le h
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (Nat.cast_pos.mp hcpos)
    obtain ⟨hyY, hyg⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    apply Finset.mem_image.mpr
    refine ⟨(y, y - g), Finset.mem_product.mpr ⟨hyY, hyg⟩, ?_⟩
    simp

/-- Count the actual incidences in both orders. -/
theorem incidence_sum (Y S : Finset G) :
    (∑ y ∈ Y, (incidenceFiber Y S y).card) = ∑ s ∈ S, (overlap Y s).card := by
  classical
  simp only [incidenceFiber, overlap, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- The incidence second moment counts original triples `(y,s,t)`. -/
theorem incidence_second_moment (Y S : Finset G) :
    (∑ y ∈ Y, (incidenceFiber Y S y).card ^ 2) =
      ∑ s ∈ S, ∑ t ∈ S, (commonWitnesses Y s t).card := by
  classical
  have hf (y : G) : (incidenceFiber Y S y).card ^ 2 =
      ∑ s ∈ S, ∑ t ∈ S, if y - s ∈ Y ∧ y - t ∈ Y then (1 : ℕ) else 0 := by
    rw [pow_two, ← Finset.card_product]
    simp only [incidenceFiber, Finset.card_eq_sum_ones, Finset.sum_product,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : y - s ∈ Y <;> simp [hs]
  simp_rw [hf, commonWitnesses, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  exact Finset.sum_comm

/-- Subtracting `t` injects actual common witnesses into the difference overlap. -/
theorem common_witnesses_card_le (Y : Finset G) (s t : G) :
    (commonWitnesses Y s t).card ≤ (overlap Y (s - t)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun y => y - t)
  · intro y hy
    obtain ⟨_, hys, hyt⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨hyt, ?_⟩
    have heq : y - t - (s - t) = y - s := by abel
    simpa only [heq] using hys
  · intro y _ z _ h
    simpa only [sub_add_cancel] using congrArg (fun u => u + t) h

/-- The original incidence second moment is bounded by the actual difference energy. -/
theorem second_moment_le_energy (Y S : Finset G) :
    (∑ y ∈ Y, ((incidenceFiber Y S y).card : ℝ) ^ 2) ≤ differenceEnergy Y S := by
  classical
  have heq : (∑ y ∈ Y, ((incidenceFiber Y S y).card : ℝ) ^ 2) =
      ∑ s ∈ S, ∑ t ∈ S, ((commonWitnesses Y s t).card : ℝ) := by
    exact_mod_cast incidence_second_moment Y S
  rw [heq, differenceEnergy, Finset.product_eq_sprod, Finset.sum_product]
  exact Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun t _ =>
    Nat.cast_le.mpr (common_witnesses_card_le Y s t)))

/-- Cauchy-Schwarz applied to actual incidences, without an energy premise. -/
theorem difference_energy_lower (Y S : Finset G) {a : ℝ}
    (ha : 0 ≤ a) (hY : Y.Nonempty)
    (hS : ∀ s ∈ S, a * (Y.card : ℝ) ≤ (overlap Y s).card) :
    a ^ 2 * (Y.card : ℝ) * (S.card : ℝ) ^ 2 ≤ differenceEnergy Y S := by
  classical
  have hypos : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
  have hsum : a * (Y.card : ℝ) * (S.card : ℝ) ≤
      ∑ y ∈ Y, ((incidenceFiber Y S y).card : ℝ) := by
    have heq : (∑ y ∈ Y, ((incidenceFiber Y S y).card : ℝ)) =
        ∑ s ∈ S, ((overlap Y s).card : ℝ) := by exact_mod_cast incidence_sum Y S
    rw [heq]
    calc
      _ = ∑ _s ∈ S, a * (Y.card : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum hS
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Y (fun _ => (1 : ℝ))
    (fun y => ((incidenceFiber Y S y).card : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ a * (Y.card : ℝ) * (S.card : ℝ)) hsum 2
  have he := mul_le_mul_of_nonneg_left (second_moment_le_energy Y S) hypos.le
  have htotal : (a * (Y.card : ℝ) * (S.card : ℝ)) ^ 2 ≤
      (Y.card : ℝ) * differenceEnergy Y S := hsq.trans (hcs.trans he)
  have hdiv : (Y.card : ℝ) * (a ^ 2 * (Y.card : ℝ) * (S.card : ℝ) ^ 2) ≤
      (Y.card : ℝ) * differenceEnergy Y S := by nlinarith only [htotal]
  exact (mul_le_mul_iff_right₀ hypos).mp hdiv

/-- Every finite family of shifts has at most `|Y|²` actual incidences. -/
theorem overlap_sum_le_square (Y S : Finset G) :
    (∑ s ∈ S, (overlap Y s).card) ≤ Y.card ^ 2 := by
  classical
  let I := (Y.product S).filter (fun p => p.1 - p.2 ∈ Y)
  have heq : I.card = ∑ s ∈ S, (overlap Y s).card := by
    simp only [I, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product,
      Finset.product_eq_sprod, overlap]
    exact Finset.sum_comm
  rw [← heq, pow_two, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun p => (p.1, p.1 - p.2))
  · intro p hp
    obtain ⟨hprod, hdiff⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hprod).1, hdiff⟩
  · intro p _ q _ h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    dsimp at hfst hsnd
    apply Prod.ext hfst
    rw [hfst] at hsnd
    simpa only [sub_right_inj] using hsnd

/-- Cardinal bound for any actual positive-density family of symmetries. -/
theorem symmetry_family_card_bound (Y S : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty)
    (hS : ∀ s ∈ S, a * (Y.card : ℝ) ≤ (overlap Y s).card) :
    (S.card : ℝ) ≤ (Y.card : ℝ) / a := by
  classical
  have hypos : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
  have hlow := Finset.sum_le_sum hS
  have hupp : (∑ s ∈ S, ((overlap Y s).card : ℝ)) ≤ (Y.card : ℝ) ^ 2 := by
    exact_mod_cast overlap_sum_le_square Y S
  simp only [Finset.sum_const, nsmul_eq_mul] at hlow
  apply (le_div_iff₀ ha).mpr
  have hprod : (Y.card : ℝ) * ((S.card : ℝ) * a) ≤ (Y.card : ℝ) * (Y.card : ℝ) := by
    nlinarith only [hlow.trans hupp]
  exact (mul_le_mul_iff_right₀ hypos).mp hprod

/-- The symmetry set is constructed from actual original differences. -/
theorem symmetrySet_card_bound (Y : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) :
    ((symmetrySet Y a).card : ℝ) ≤ (Y.card : ℝ) / a := by
  apply symmetry_family_card_bound Y (symmetrySet Y a) ha hY
  intro s hs
  exact (mem_symmetrySet_iff ha hY s).mp hs

/-- Bound energy by the actual good-pair population and the bad threshold. -/
theorem difference_energy_upper (Y S : Finset G) {b : ℝ}
    (hb : 0 < b) (hY : Y.Nonempty) :
    differenceEnergy Y S ≤ (Y.card : ℝ) * ((goodPairs Y S b).card : ℝ) +
      b * (Y.card : ℝ) * (S.card : ℝ) ^ 2 := by
  classical
  have hpoint (p : G × G) : ((overlap Y (p.1 - p.2)).card : ℝ) ≤
      (if p.1 - p.2 ∈ symmetrySet Y b then (Y.card : ℝ) else 0) + b * (Y.card : ℝ) := by
    by_cases hp : p.1 - p.2 ∈ symmetrySet Y b
    · simp only [hp, if_true]
      exact (Nat.cast_le.mpr (overlap_card_le Y _)).trans (le_add_of_nonneg_right (mul_nonneg hb.le (Nat.cast_nonneg _)))
    · simp only [hp, if_false, zero_add]
      exact le_of_lt (lt_of_not_ge (fun h => hp ((mem_symmetrySet_iff hb hY _).mpr h)))
  have hsum := Finset.sum_le_sum (fun p (_hp : p ∈ S.product S) => hpoint p)
  have heq : (∑ p ∈ S.product S,
      if p.1 - p.2 ∈ symmetrySet Y b then (Y.card : ℝ) else 0) =
      (Y.card : ℝ) * ((goodPairs Y S b).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [goodPairs, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [Finset.sum_add_distrib, heq] at hsum
  simpa only [differenceEnergy, Finset.sum_const, nsmul_eq_mul, Finset.product_eq_sprod, Finset.card_product,
    Nat.cast_mul, pow_two, mul_assoc, mul_comm, mul_left_comm] using hsum

/-- A positive proportion of the ORIGINAL ordered pairs have a denser symmetry
as their difference. No regularity, filled interval, or energy input is assumed. -/
theorem good_pairs_lower (Y S : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (hS : S ⊆ symmetrySet Y a) :
    (a ^ 2 / 2) * (S.card : ℝ) ^ 2 ≤ ((goodPairs Y S (a ^ 2 / 2)).card : ℝ) := by
  have hlow := difference_energy_lower Y S ha.le hY
    (fun s hs => (mem_symmetrySet_iff ha hY s).mp (hS hs))
  have hb : 0 < a ^ 2 / 2 := by positivity
  have hupp := difference_energy_upper Y S hb hY
  have hypos : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
  have hprod : (Y.card : ℝ) * ((a ^ 2 / 2) * (S.card : ℝ) ^ 2) ≤
      (Y.card : ℝ) * ((goodPairs Y S (a ^ 2 / 2)).card : ℝ) := by
    nlinarith only [hlow.trans hupp]
  exact (mul_le_mul_iff_right₀ hypos).mp hprod


/-- The image consists of actual symmetry differences of the retained pairs. -/
theorem good_pairs_difference_image_subset [DecidableEq G] (Y S : Finset G) (b : ℝ) :
    (goodPairs Y S b).image (fun p => p.1 - p.2) ⊆ symmetrySet Y b := by
  classical
  intro g hg
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hg
  exact (show p ∈ S.product S ∧ p.1 - p.2 ∈ symmetrySet Y b from by
    simpa only [goodPairs, Finset.mem_filter] using hp).2

/-- Cross-multiplied form avoids dividing by the symmetry density in callers. -/
theorem symmetrySet_card_mul_bound (Y : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) :
    a * ((symmetrySet Y a).card : ℝ) ≤ (Y.card : ℝ) := by
  have h := (le_div_iff₀ ha).mp (symmetrySet_card_bound Y ha hY)
  simpa only [mul_comm] using h

/-- A general threshold consequence of the actual overlap energy. -/
theorem good_pairs_lower_of_energy (Y S : Finset G) {b : ℝ}
    (hb : 0 < b) (hY : Y.Nonempty)
    (henergy : 2 * b * (Y.card : ℝ) * (S.card : ℝ) ^ 2 ≤ differenceEnergy Y S) :
    b * (S.card : ℝ) ^ 2 ≤ ((goodPairs Y S b).card : ℝ) := by
  have hupp := difference_energy_upper Y S hb hY
  have hypos : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
  have hprod : (Y.card : ℝ) * (b * (S.card : ℝ) ^ 2) ≤
      (Y.card : ℝ) * ((goodPairs Y S b).card : ℝ) := by
    nlinarith only [henergy.trans hupp]
  exact (mul_le_mul_iff_right₀ hypos).mp hprod

/-- Exact identification of an additive-energy fiber with the original overlap. -/
theorem additive_fiber_card [DecidableEq G] (Y : Finset G) (s t : G) :
    ((Y.product Y).filter (fun p : G × G => p.1 + s = p.2 + t)).card =
      (overlap Y (t - s)).card := by
  classical
  have heq (p : G × G) (hp : p.1 + s = p.2 + t) : p.1 - (t - s) = p.2 := by
    apply add_right_cancel (b := t)
    calc
      p.1 - (t - s) + t = p.1 + s := by abel
      _ = p.2 + t := hp
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    obtain ⟨hpp, he⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpp
    simp only [overlap, Finset.mem_filter]
    exact ⟨hp1, (heq p he).symm ▸ hp2⟩
  · intro p hp q hq h
    obtain ⟨_, hp⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hq⟩ := Finset.mem_filter.mp hq
    apply Prod.ext h
    rw [← heq p hp, ← heq q hq, h]
  · intro y hy
    have hyy : y ∈ Y ∧ y - (t - s) ∈ Y := by
      simpa only [overlap, Finset.mem_filter] using hy
    obtain ⟨hy, hyd⟩ := hyy
    refine ⟨(y, y - (t - s)), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hy, hyd⟩, ?_⟩
    dsimp
    abel

/-- The energy used here is precisely Mathlib's additive energy, not a new
hypothesis-bearing surrogate. -/
theorem differenceEnergy_eq_addEnergy [DecidableEq G] (Y S : Finset G) :
    differenceEnergy Y S = (Finset.addEnergy Y S : ℝ) := by
  classical
  have hn : Finset.addEnergy Y S = ∑ p ∈ S.product S, (overlap Y (p.1 - p.2)).card := by
    unfold Finset.addEnergy
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
    have hf (p : G × G) : (∑ yy ∈ Y.product Y,
        if yy.1 + p.1 = yy.2 + p.2 then (1 : ℕ) else 0) =
        (overlap Y (p.2 - p.1)).card := by
      rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
      exact additive_fiber_card Y p.1 p.2
    change (∑ p ∈ S.product S, ∑ yy ∈ Y.product Y,
      if yy.1 + p.1 = yy.2 + p.2 then (1 : ℕ) else 0) = _
    simp_rw [hf]
    simp only [Finset.product_eq_sprod, Finset.sum_product]
    exact Finset.sum_comm
  dsimp [differenceEnergy]
  exact_mod_cast hn.symm

/-- Direct caller for an original Mathlib additive-energy lower bound. -/
theorem good_pairs_lower_of_addEnergy [DecidableEq G] (Y S : Finset G) {b : ℝ}
    (hb : 0 < b) (hY : Y.Nonempty)
    (henergy : 2 * b * (Y.card : ℝ) * (S.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y S : ℝ)) :
    b * (S.card : ℝ) ^ 2 ≤ ((goodPairs Y S b).card : ℝ) := by
  apply good_pairs_lower_of_energy Y S hb hY
  rwa [differenceEnergy_eq_addEnergy]

end

end SymmetrySetDifferenceStep
