import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

/-!
# Four distinct sources with one inherited source fixed

The fresh source indices have the actual three-fold product law of a finite
probability vector. The inherited source index is a fixed parameter, never a
fourth random draw. A union bound over the six possible equalities loses at
most six times the largest atom. No conclusion is packaged as a hypothesis.
-/

namespace StickyKakeya4.FourDistinctSources

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

/-- All six inequalities among the inherited source and three fresh sources. -/
def FourDistinct (i j k l : ι) : Prop :=
  i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l

/-- Expectation for three independent fresh sources with common law `p`.
The inherited source is not one of the coordinates being sampled. -/
noncomputable def tripleExpectation (p : ι → ℝ) (f : ι → ι → ι → ℝ) : ℝ :=
  ∑ j, ∑ k, ∑ l, p j * p k * p l * f j k l

/-- The genuine finite product-law probability of any event on the fresh triple. -/
noncomputable def tripleProbability (p : ι → ℝ) (E : ι → ι → ι → Prop) : ℝ :=
  tripleExpectation p (fun j k l => if E j k l then 1 else 0)

/-- Success probability with inherited `i` fixed throughout. -/
noncomputable def fourDistinctProbability (p : ι → ℝ) (i : ι) : ℝ :=
  tripleProbability p (FourDistinct i)

theorem tripleExpectation_one (p : ι → ℝ) (hp : ∑ j, p j = 1) :
    tripleExpectation p (fun _ _ _ => 1) = 1 := by
  simp only [tripleExpectation, mul_one]
  simp_rw [← Finset.mul_sum]
  simp [hp, ← Finset.mul_sum]

theorem tripleExpectation_add (p : ι → ℝ) (f g : ι → ι → ι → ℝ) :
    tripleExpectation p (fun j k l => f j k l + g j k l) =
      tripleExpectation p f + tripleExpectation p g := by
  simp [tripleExpectation, mul_add, Finset.sum_add_distrib]

theorem tripleExpectation_mono (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (f g : ι → ι → ι → ℝ) (h : ∀ j k l, f j k l ≤ g j k l) :
    tripleExpectation p f ≤ tripleExpectation p g := by
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro l _
  exact mul_le_mul_of_nonneg_left (h j k l) (mul_nonneg (mul_nonneg (hp j) (hp k)) (hp l))

/-- A rectangle has the product of its three marginal probabilities. -/
theorem tripleProbability_rectangle (p : ι → ℝ) (A B C : ι → Prop) :
    tripleProbability p (fun j k l => A j ∧ B k ∧ C l) =
      (∑ j, if A j then p j else 0) *
      (∑ k, if B k then p k else 0) *
      (∑ l, if C l then p l else 0) := by
  classical
  simp only [tripleProbability, tripleExpectation]
  calc
    _ = ∑ j, ∑ k, ∑ l,
        (if A j then p j else 0) * (if B k then p k else 0) *
          (if C l then p l else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      by_cases hA : A j <;> by_cases hB : B k <;> by_cases hC : C l <;>
        simp [hA, hB, hC]
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]

omit [Fintype ι] in
private theorem six_equalities_cover (i j k l : ι) :
    (1 : ℝ) ≤ (if FourDistinct i j k l then 1 else 0) +
      (if i = j then 1 else 0) + (if i = k then 1 else 0) +
      (if i = l then 1 else 0) + (if j = k then 1 else 0) +
      (if j = l then 1 else 0) + (if k = l then 1 else 0) := by
  classical
  by_cases hij : i = j <;> by_cases hik : i = k <;>
    by_cases hil : i = l <;> by_cases hjk : j = k <;>
    by_cases hjl : j = l <;> by_cases hkl : k = l <;>
    simp_all [FourDistinct]
  all_goals norm_num

/-- Collision of the first fresh source with the fixed inherited source. -/
theorem inherited_collision_first (p : ι → ℝ) (hp : ∑ j, p j = 1) (i : ι) :
    tripleProbability p (fun j _ _ => i = j) = p i := by
  classical
  simp [tripleProbability, tripleExpectation, mul_ite, ← Finset.mul_sum, hp]

theorem inherited_collision_second (p : ι → ℝ) (hp : ∑ j, p j = 1) (i : ι) :
    tripleProbability p (fun _ k _ => i = k) = p i := by
  classical
  simp [tripleProbability, tripleExpectation, mul_ite, ← Finset.mul_sum,
    ← Finset.sum_mul, hp]

theorem inherited_collision_third (p : ι → ℝ) (hp : ∑ j, p j = 1) (i : ι) :
    tripleProbability p (fun _ _ l => i = l) = p i := by
  classical
  simp [tripleProbability, tripleExpectation, mul_ite, ← Finset.mul_sum,
    ← Finset.sum_mul, hp]

theorem fresh_collision_first_second (p : ι → ℝ) (hp : ∑ j, p j = 1) :
    tripleProbability p (fun j k _ => j = k) = ∑ j, p j * p j := by
  classical
  simp [tripleProbability, tripleExpectation, mul_ite, ← Finset.mul_sum, hp]

theorem fresh_collision_first_third (p : ι → ℝ) (hp : ∑ j, p j = 1) :
    tripleProbability p (fun j _ l => j = l) = ∑ j, p j * p j := by
  classical
  simp [tripleProbability, tripleExpectation, mul_ite, ← Finset.mul_sum,
    ← Finset.sum_mul, hp]

theorem fresh_collision_second_third (p : ι → ℝ) (hp : ∑ j, p j = 1) :
    tripleProbability p (fun _ k l => k = l) = ∑ j, p j * p j := by
  classical
  simp [tripleProbability, tripleExpectation, mul_ite, ← Finset.mul_sum,
    ← Finset.sum_mul, hp, mul_assoc]

/-- Any event has nonnegative probability under a nonnegative probability vector. -/
theorem tripleProbability_nonneg (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (E : ι → ι → ι → Prop) : 0 ≤ tripleProbability p E := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg (mul_nonneg (mul_nonneg (hp j) (hp k)) (hp l))
    (by dsimp only; split_ifs <;> norm_num)

theorem tripleProbability_le_one (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) (E : ι → ι → ι → Prop) :
    tripleProbability p E ≤ 1 := by
  rw [← tripleExpectation_one p hsum]
  apply tripleExpectation_mono p hp
  intro j k l
  split_ifs <;> norm_num

/-- The collision probability of two independent draws is at most the largest atom. -/
theorem squared_atoms_le (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) (a : ℝ) (hatom : ∀ j, p j ≤ a) :
    (∑ j, p j * p j) ≤ a := by
  calc
    (∑ j, p j * p j) ≤ ∑ j, p j * a := by
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hatom j) (hp j))
    _ = a := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Six-collision union bound for a fixed inherited source and three fresh independent
sources. The left side is a lower bound for an actual finite product probability. -/
theorem four_distinct_probability_ge (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) (a : ℝ) (hatom : ∀ j, p j ≤ a) (i : ι) :
    1 - 6 * a ≤ fourDistinctProbability p i := by
  have h := tripleExpectation_mono p hp (fun _ _ _ => 1)
    (fun j k l => (if FourDistinct i j k l then 1 else 0) +
      (if i = j then 1 else 0) + (if i = k then 1 else 0) +
      (if i = l then 1 else 0) + (if j = k then 1 else 0) +
      (if j = l then 1 else 0) + (if k = l then 1 else 0))
    (six_equalities_cover i)
  rw [tripleExpectation_one p hsum] at h
  simp only [tripleExpectation_add] at h
  change 1 ≤ fourDistinctProbability p i +
    tripleProbability p (fun j _ _ => i = j) +
    tripleProbability p (fun _ k _ => i = k) +
    tripleProbability p (fun _ _ l => i = l) +
    tripleProbability p (fun j k _ => j = k) +
    tripleProbability p (fun j _ l => j = l) +
    tripleProbability p (fun _ k l => k = l) at h
  rw [inherited_collision_first p hsum, inherited_collision_second p hsum,
    inherited_collision_third p hsum, fresh_collision_first_second p hsum,
    fresh_collision_first_third p hsum, fresh_collision_second_third p hsum] at h
  have hs := squared_atoms_le p hp hsum a hatom
  have hi := hatom i
  linarith

/-- Atom size at most `1/12` gives success probability at least one half. -/
theorem four_distinct_probability_ge_half (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) (a : ℝ) (hatom : ∀ j, p j ≤ a)
    (ha : a ≤ 1 / 12) (i : ι) :
    (1 : ℝ) / 2 ≤ fourDistinctProbability p i := by
  have h := four_distinct_probability_ge p hp hsum a hatom i
  linarith

/-- Normalize actual source weights, rather than supplying a probability certificate. -/
noncomputable def normalizedWeights (w : ι → ℝ) (j : ι) : ℝ :=
  w j / ∑ k, w k

theorem normalizedWeights_nonneg (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (j : ι) :
    0 ≤ normalizedWeights w j :=
  div_nonneg (hw j) (Finset.sum_nonneg (fun k _ => hw k))

theorem normalizedWeights_sum (w : ι → ℝ) (hN : 0 < ∑ j, w j) :
    (∑ j, normalizedWeights w j) = 1 := by
  simp only [normalizedWeights, ← Finset.sum_div]
  exact div_self (ne_of_gt hN)

/-- Weights at most one and total weight at least `K>0` give atoms at most `1/K`. -/
theorem normalizedWeights_atom_le (w : ι → ℝ) (hw : ∀ j, w j ≤ 1)
    (K : ℝ) (hK : 0 < K) (hN : K ≤ ∑ j, w j) (j : ι) :
    normalizedWeights w j ≤ 1 / K := by
  have hNpos : 0 < ∑ j, w j := lt_of_lt_of_le hK hN
  calc
    normalizedWeights w j ≤ 1 / (∑ k, w k) :=
      div_le_div_of_nonneg_right (hw j) hNpos.le
    _ ≤ 1 / K := div_le_div_of_nonneg_left (by norm_num) hK hN

/-- Weighted high-multiplicity specialization: the inherited source remains fixed,
while all three fresh source indices use the normalized original source weights. -/
theorem weighted_four_distinct_probability_ge (w : ι → ℝ)
    (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∀ j, w j ≤ 1)
    (K : ℝ) (hK : 0 < K) (hN : K ≤ ∑ j, w j) (i : ι) :
    1 - 6 / K ≤ fourDistinctProbability (normalizedWeights w) i := by
  have h := four_distinct_probability_ge (normalizedWeights w)
    (normalizedWeights_nonneg w hw0)
    (normalizedWeights_sum w (lt_of_lt_of_le hK hN)) (1 / K)
    (normalizedWeights_atom_le w hw1 K hK hN) i
  simpa [div_eq_mul_inv] using h

theorem weighted_four_distinct_probability_ge_half (w : ι → ℝ)
    (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∀ j, w j ≤ 1)
    (K : ℝ) (hK : 12 ≤ K) (hN : K ≤ ∑ j, w j) (i : ι) :
    (1 : ℝ) / 2 ≤ fourDistinctProbability (normalizedWeights w) i := by
  have hKpos : 0 < K := by linarith
  exact four_distinct_probability_ge_half (normalizedWeights w)
    (normalizedWeights_nonneg w hw0)
    (normalizedWeights_sum w (lt_of_lt_of_le hKpos hN)) (1 / K)
    (normalizedWeights_atom_le w hw1 K hKpos hN)
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hK) i

/-- The finite real probability vector agrees exactly with the `toReal` of
normalized extended-nonnegative source weights. -/
theorem normalizedWeights_toReal (w : ι → ℝ≥0∞) (hw : ∀ j, w j ≤ 1) (j : ι) :
    normalizedWeights (fun k => (w k).toReal) j =
      (w j / ∑ k, w k).toReal := by
  have hfin : ∀ k ∈ (Finset.univ : Finset ι), w k ≠ ∞ :=
    fun k _ => ne_top_of_le_ne_top ENNReal.one_ne_top (hw k)
  simp only [normalizedWeights, ENNReal.toReal_div, ENNReal.toReal_sum hfin]

/-- Direct bridge from finite ENNReal incidence weights and high multiplicity
into the actual fresh-triple probability estimate. -/
theorem ennreal_weighted_four_distinct_probability_ge (w : ι → ℝ≥0∞)
    (hw : ∀ j, w j ≤ 1) (K : ℝ) (hK : 0 < K)
    (hN : ENNReal.ofReal K ≤ ∑ j, w j) (i : ι) :
    1 - 6 / K ≤ fourDistinctProbability
      (fun j => (w j / ∑ k, w k).toReal) i := by
  have hfin : ∀ k ∈ (Finset.univ : Finset ι), w k ≠ ∞ :=
    fun k _ => ne_top_of_le_ne_top ENNReal.one_ne_top (hw k)
  have hNreal : K ≤ ∑ k, (w k).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr hfin) hN
    simpa only [ENNReal.toReal_ofReal hK.le, ENNReal.toReal_sum hfin] using h
  have hwreal : ∀ k, (w k).toReal ≤ 1 := by
    intro k
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top (hw k)
  have h := weighted_four_distinct_probability_ge (fun k => (w k).toReal)
    (fun _ => ENNReal.toReal_nonneg) hwreal K hK hNreal i
  simpa only [show normalizedWeights (fun k => (w k).toReal) =
    (fun k => (w k / ∑ j, w j).toReal) from funext (normalizedWeights_toReal w hw)] using h

theorem ennreal_weighted_four_distinct_probability_ge_half (w : ι → ℝ≥0∞)
    (hw : ∀ j, w j ≤ 1) (K : ℝ) (hK : 12 ≤ K)
    (hN : ENNReal.ofReal K ≤ ∑ j, w j) (i : ι) :
    (1 : ℝ) / 2 ≤ fourDistinctProbability
      (fun j => (w j / ∑ k, w k).toReal) i := by
  have hKpos : 0 < K := by linarith
  have h := ennreal_weighted_four_distinct_probability_ge w hw K hKpos hN i
  have hdiv : (6 : ℝ) / K ≤ 1 / 2 := by
    apply (div_le_iff₀ hKpos).mpr
    linarith
  linarith

end StickyKakeya4.FourDistinctSources
