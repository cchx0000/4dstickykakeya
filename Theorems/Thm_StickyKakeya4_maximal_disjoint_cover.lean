import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-!
# Finite maximal disjoint measurable covers

A positive lower bound for the mass of every selected piece bounds the number
of pairwise disjoint pieces in a subprobability space. If every measurable
remainder whose stopping functional is too large admits a further piece, a
maximal-cardinality family therefore has a stopped remainder. No regularity or
monotonicity of the stopping functional is required.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.MaximalDisjointCover

variable {X : Type*} [MeasurableSpace X]

/-- A finite disjoint family of eligible measurable pieces of uniformly positive mass. -/
def Admissible (σ : Measure X) (P : Set X → Prop) (a : ℝ)
    (F : Finset (Set X)) : Prop :=
  (F : Set (Set X)).PairwiseDisjoint id ∧
    ∀ B ∈ F, MeasurableSet B ∧ P B ∧ ENNReal.ofReal a ≤ σ B

/-- The mass budget bounds the cardinality of any admissible family. -/
theorem Admissible.card_mul_le_one {σ : Measure X} {P : Set X → Prop}
    {a : ℝ} {F : Finset (Set X)} (hF : Admissible σ P a F)
    (hσ : σ univ ≤ 1) : (F.card : ℝ) * a ≤ 1 := by
  apply ENNReal.ofReal_le_one.mp
  calc
    ENNReal.ofReal ((F.card : ℝ) * a) =
        (F.card : ℝ≥0∞) * ENNReal.ofReal a := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ = ∑ _B ∈ F, ENNReal.ofReal a := by simp
    _ ≤ ∑ B ∈ F, σ B := Finset.sum_le_sum fun B hB => (hF.2 B hB).2.2
    _ = σ (⋃ B ∈ F, B) := (measure_biUnion_finset hF.1
      (fun B hB => (hF.2 B hB).1)).symm
    _ ≤ σ univ := measure_mono (subset_univ _)
    _ ≤ 1 := hσ

/-- Any measurable remainder above the stopping threshold yields another
eligible positive-mass piece. A maximal-cardinality family stops after at most
`1 / a` pieces. The functional may, for example, be a graph measure on `T × T`. -/
theorem exists_stopped_family (σ : Measure X) (P : Set X → Prop)
    (a : ℝ) (ha : 0 < a) (hσ : σ univ ≤ 1)
    (R : Set X → ℝ≥0∞) (k : ℝ≥0∞)
    (hextract : ∀ T : Set X, MeasurableSet T → k < R T →
      ∃ B : Set X, MeasurableSet B ∧ B ⊆ T ∧ P B ∧ ENNReal.ofReal a ≤ σ B) :
    ∃ F : Finset (Set X), Admissible σ P a F ∧
      (F.card : ℝ) * a ≤ 1 ∧ R (⋃ B ∈ F, B)ᶜ ≤ k := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / a)
  have hbound : ∀ F : Finset (Set X), Admissible σ P a F → F.card ≤ N := by
    intro F hF
    have hcard : (F.card : ℝ) ≤ 1 / a :=
      (le_div_iff₀ ha).mpr (hF.card_mul_le_one hσ)
    exact_mod_cast hcard.trans hN
  let attainable : ℕ → Prop := fun n =>
    ∃ F : Finset (Set X), Admissible σ P a F ∧ F.card = n
  have hzero : attainable 0 := by
    refine ⟨∅, ?_, rfl⟩
    simp [Admissible]
  obtain ⟨F, hF, hcard⟩ := Nat.findGreatest_spec (Nat.zero_le N) hzero
  refine ⟨F, hF, hF.card_mul_le_one hσ, ?_⟩
  by_contra hstop
  have hT : MeasurableSet (⋃ B ∈ F, B)ᶜ :=
    (MeasurableSet.biUnion F.countable_toSet (fun B hB => (hF.2 B hB).1)).compl
  obtain ⟨B, hBm, hBT, hBP, hBmass⟩ := hextract _ hT (lt_of_not_ge hstop)
  have hdis : ∀ C ∈ F, Disjoint B C := by
    intro C hC
    exact disjoint_left.mpr fun x hxB hxC =>
      hBT hxB (mem_iUnion.mpr ⟨C, mem_iUnion.mpr ⟨hC, hxC⟩⟩)
  have hBne : B ≠ ∅ := by
    intro heq
    have hpositive : 0 < ENNReal.ofReal a := ENNReal.ofReal_pos.mpr ha
    simpa [heq] using hpositive.trans_le hBmass
  have hBnot : B ∉ F := by
    intro hBF
    exact hBne (disjoint_self.mp (hdis B hBF))
  have hF' : Admissible σ P a (insert B F) := by
    constructor
    · simpa only [Finset.coe_insert] using hF.1.insert_of_notMem hBnot hdis
    · intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hCF
      · exact ⟨hBm, hBP, hBmass⟩
      · exact hF.2 C hCF
  have hmax : (insert B F).card ≤ Nat.findGreatest attainable N :=
    Nat.le_findGreatest (hbound _ hF') ⟨insert B F, hF', rfl⟩
  rw [Finset.card_insert_of_notMem hBnot, hcard] at hmax
  omega

/-- A reciprocal form of the finite-family cardinality bound. -/
theorem exists_stopped_family_card_le (σ : Measure X) (P : Set X → Prop)
    (a : ℝ) (ha : 0 < a) (hσ : σ univ ≤ 1)
    (R : Set X → ℝ≥0∞) (k : ℝ≥0∞)
    (hextract : ∀ T : Set X, MeasurableSet T → k < R T →
      ∃ B : Set X, MeasurableSet B ∧ B ⊆ T ∧ P B ∧ ENNReal.ofReal a ≤ σ B) :
    ∃ F : Finset (Set X), Admissible σ P a F ∧
      (F.card : ℝ) ≤ 1 / a ∧ R (⋃ B ∈ F, B)ᶜ ≤ k := by
  obtain ⟨F, hF, hcard, hstop⟩ := exists_stopped_family σ P a ha hσ R k hextract
  exact ⟨F, hF, (le_div_iff₀ ha).mpr hcard, hstop⟩

end StickyKakeya4.MaximalDisjointCover
