import Theorems.Thm_StickyKakeya4_finite_mass_conserving_stopping
import Mathlib.Data.Nat.Pairing

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

universe u

/-- Fair countable scan index: the first coordinate of the canonical pairing
schedule.  Every event index occurs at the stages `Nat.pair i k`. -/
def fairCountableStoppingIndex (n : ℕ) : ℕ := (Nat.unpair n).1

theorem fairCountableStoppingIndex_pair (i k : ℕ) :
    fairCountableStoppingIndex (Nat.pair i k) = i := by
  simp [fairCountableStoppingIndex, Nat.unpair_pair]

/-- Every event is revisited after every prescribed stage. -/
theorem exists_fairCountableStoppingIndex_eq_ge (i N : ℕ) :
    ∃ n, N ≤ n ∧ fairCountableStoppingIndex n = i := by
  exact ⟨Nat.pair i N, Nat.right_le_pair i N,
    fairCountableStoppingIndex_pair i N⟩

/-- Remainder measure after a finite prefix of the fair countable scan.  At a
stage whose event violates the relative cap bound, its entire current mass is
removed by restriction to the measurable complement. -/
noncomputable def countableStoppingRemainder
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) : ℕ → Measure X
  | 0 => nu
  | n + 1 =>
      let current := countableStoppingRemainder nu event cost C n
      let i := fairCountableStoppingIndex n
      if C * current Set.univ * cost i < current (event i) then
        current.restrict (event i)ᶜ
      else current

/-- Actual mass removed at one scan stage. -/
noncomputable def countableStoppingRemovedMass
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (n : ℕ) : ENNReal :=
  let current := countableStoppingRemainder nu event cost C n
  let i := fairCountableStoppingIndex n
  if C * current Set.univ * cost i < current (event i) then
    current (event i)
  else 0

/-- Relative cap charge generated at one scan stage. -/
noncomputable def countableStoppingCharge
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (n : ℕ) : ENNReal :=
  let current := countableStoppingRemainder nu event cost C n
  let i := fairCountableStoppingIndex n
  if C * current Set.univ * cost i < current (event i) then
    C * current Set.univ * cost i
  else 0

/-- Measurable carrier set of the finite-stage remainder. -/
noncomputable def countableStoppingRemainderSet
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) : ℕ → Set X
  | 0 => Set.univ
  | n + 1 =>
      let previous := countableStoppingRemainderSet nu event cost C n
      let current := countableStoppingRemainder nu event cost C n
      let i := fairCountableStoppingIndex n
      if C * current Set.univ * cost i < current (event i) then
        (event i)ᶜ ∩ previous
      else previous

theorem measurableSet_countableStoppingRemainderSet
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (eventsMeasurable : ∀ i, MeasurableSet (event i)) :
    ∀ n, MeasurableSet (countableStoppingRemainderSet nu event cost C n) := by
  intro n
  induction n with
  | zero => simp [countableStoppingRemainderSet]
  | succ n ih =>
      let current := countableStoppingRemainder nu event cost C n
      let i := fairCountableStoppingIndex n
      by_cases hlarge : C * current Set.univ * cost i < current (event i)
      · simpa [countableStoppingRemainderSet, current, i, hlarge] using
          (eventsMeasurable i).compl.inter ih
      · simpa [countableStoppingRemainderSet, current, i, hlarge] using ih

/-- The algorithmic remainder measure is exactly the starting measure
restricted to its measurable remainder carrier. -/
theorem countableStoppingRemainder_eq_restrict
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (eventsMeasurable : ∀ i, MeasurableSet (event i)) :
    ∀ n,
      countableStoppingRemainder nu event cost C n =
        nu.restrict (countableStoppingRemainderSet nu event cost C n) := by
  intro n
  induction n with
  | zero => simp [countableStoppingRemainder, countableStoppingRemainderSet]
  | succ n ih =>
      let previous := countableStoppingRemainderSet nu event cost C n
      let current := countableStoppingRemainder nu event cost C n
      let i := fairCountableStoppingIndex n
      by_cases hlarge : C * current Set.univ * cost i < current (event i)
      · simp only [countableStoppingRemainder, countableStoppingRemainderSet,
          previous, current, i, hlarge, if_pos]
        rw [ih, Measure.restrict_restrict (eventsMeasurable i).compl]
      · simp only [countableStoppingRemainder, countableStoppingRemainderSet,
          previous, current, i, hlarge, if_neg]
        exact ih

theorem countableStoppingRemainderSet_succ_subset
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (n : ℕ) :
    countableStoppingRemainderSet nu event cost C (n + 1) ⊆
      countableStoppingRemainderSet nu event cost C n := by
  let current := countableStoppingRemainder nu event cost C n
  let i := fairCountableStoppingIndex n
  by_cases hlarge : C * current Set.univ * cost i < current (event i)
  · simpa [countableStoppingRemainderSet, current, i, hlarge] using
      (Set.inter_subset_right : (event i)ᶜ ∩
        countableStoppingRemainderSet nu event cost C n ⊆
          countableStoppingRemainderSet nu event cost C n)
  · simp [countableStoppingRemainderSet, current, i, hlarge]

theorem antitone_countableStoppingRemainderSet
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) :
    Antitone (countableStoppingRemainderSet nu event cost C) :=
  antitone_nat_of_succ_le
    (countableStoppingRemainderSet_succ_subset nu event cost C)

/-- Infinite retained carrier of the fair scan. -/
noncomputable def countableStoppingLimitSet
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) : Set X :=
  ⋂ n, countableStoppingRemainderSet nu event cost C n

theorem measurableSet_countableStoppingLimitSet
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (eventsMeasurable : ∀ i, MeasurableSet (event i)) :
    MeasurableSet (countableStoppingLimitSet nu event cost C) := by
  exact MeasurableSet.iInter
    (measurableSet_countableStoppingRemainderSet
      nu event cost C eventsMeasurable)

/-- Limit remainder measure, defined by restriction to the decreasing retained
carrier. -/
noncomputable def countableStoppingLimitMeasure
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) : Measure X :=
  nu.restrict (countableStoppingLimitSet nu event cost C)

/-- Continuity from above identifies the limit retained mass with the limit of
the exact finite-prefix remainders. -/
theorem tendsto_countableStoppingRemainder_univ
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (eventsMeasurable : ∀ i, MeasurableSet (event i))
    (hfinite : nu Set.univ ≠ ⊤) :
    Tendsto
      (fun n ↦ countableStoppingRemainder nu event cost C n Set.univ)
      atTop
      (nhds (countableStoppingLimitMeasure nu event cost C Set.univ)) := by
  let retained : ℕ → Set X :=
    countableStoppingRemainderSet nu event cost C
  have hretainedMeasurable : ∀ n, MeasurableSet (retained n) :=
    measurableSet_countableStoppingRemainderSet
      nu event cost C eventsMeasurable
  have hretainedAntitone : Antitone retained :=
    antitone_countableStoppingRemainderSet nu event cost C
  have hretainedFinite : ∃ n, nu (retained n) ≠ ⊤ := by
    refine ⟨0, ?_⟩
    simpa [retained, countableStoppingRemainderSet] using hfinite
  have htendsto := tendsto_measure_iInter_atTop
    (μ := nu) (fun n ↦ (hretainedMeasurable n).nullMeasurableSet)
      hretainedAntitone hretainedFinite
  have hprefix :
      (fun n ↦ countableStoppingRemainder nu event cost C n Set.univ) =
        fun n ↦ nu (retained n) := by
    funext n
    rw [countableStoppingRemainder_eq_restrict
      nu event cost C eventsMeasurable n]
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp only [Set.univ_inter, retained]
  have hlimit :
      countableStoppingLimitMeasure nu event cost C Set.univ =
        nu (⋂ n, retained n) := by
    rw [countableStoppingLimitMeasure,
      Measure.restrict_apply MeasurableSet.univ]
    simp only [Set.univ_inter, countableStoppingLimitSet, retained]
  rw [hprefix, hlimit]
  exact htendsto

/-- Continuity from above also holds on each individual measurable event. -/
theorem tendsto_countableStoppingRemainder_event
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (eventsMeasurable : ∀ i, MeasurableSet (event i))
    (hfinite : nu Set.univ ≠ ⊤) (i : ℕ) :
    Tendsto
      (fun n ↦ countableStoppingRemainder nu event cost C n (event i))
      atTop
      (nhds (countableStoppingLimitMeasure nu event cost C (event i))) := by
  let retained : ℕ → Set X :=
    countableStoppingRemainderSet nu event cost C
  let retainedEvent : ℕ → Set X := fun n ↦ event i ∩ retained n
  have hretainedMeasurable : ∀ n, MeasurableSet (retained n) :=
    measurableSet_countableStoppingRemainderSet
      nu event cost C eventsMeasurable
  have hretainedAntitone : Antitone retained :=
    antitone_countableStoppingRemainderSet nu event cost C
  have hretainedEventMeasurable :
      ∀ n, MeasurableSet (retainedEvent n) := fun n ↦
    (eventsMeasurable i).inter (hretainedMeasurable n)
  have hretainedEventAntitone : Antitone retainedEvent := by
    intro m n hmn
    exact Set.inter_subset_inter_right _ (hretainedAntitone hmn)
  have hretainedEventFinite : ∃ n, nu (retainedEvent n) ≠ ⊤ := by
    refine ⟨0, ne_top_of_le_ne_top hfinite ?_⟩
    exact measure_mono (Set.subset_univ _)
  have htendsto := tendsto_measure_iInter_atTop
    (μ := nu) (fun n ↦ (hretainedEventMeasurable n).nullMeasurableSet)
      hretainedEventAntitone hretainedEventFinite
  have hprefix :
      (fun n ↦ countableStoppingRemainder nu event cost C n (event i)) =
        fun n ↦ nu (retainedEvent n) := by
    funext n
    rw [countableStoppingRemainder_eq_restrict
      nu event cost C eventsMeasurable n]
    rw [Measure.restrict_apply (eventsMeasurable i)]
  have hlimit :
      countableStoppingLimitMeasure nu event cost C (event i) =
        nu (⋂ n, retainedEvent n) := by
    rw [countableStoppingLimitMeasure,
      Measure.restrict_apply (eventsMeasurable i)]
    congr 1
    ext x
    simp only [countableStoppingLimitSet, retainedEvent, retained,
      Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hxi, hxretained⟩ n
      exact ⟨hxi, hxretained n⟩
    · intro hx
      exact ⟨(hx 0).1, fun n ↦ (hx n).2⟩
  rw [hprefix, hlimit]
  exact htendsto

/-- Once an event is removed at a scan stage, the limiting remainder gives it
zero mass. -/
theorem countableStoppingLimitMeasure_event_eq_zero_of_removed_at
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (eventsMeasurable : ∀ i, MeasurableSet (event i))
    (n i : ℕ) (hindex : fairCountableStoppingIndex n = i)
    (hlarge :
      C * countableStoppingRemainder nu event cost C n Set.univ * cost i <
        countableStoppingRemainder nu event cost C n (event i)) :
    countableStoppingLimitMeasure nu event cost C (event i) = 0 := by
  have hnextZero :
      countableStoppingRemainder nu event cost C (n + 1) (event i) = 0 := by
    simp [countableStoppingRemainder, hindex, hlarge,
      Measure.restrict_apply (eventsMeasurable i)]
  have hcarrierSubset :
      countableStoppingLimitSet nu event cost C ⊆
        countableStoppingRemainderSet nu event cost C (n + 1) := by
    exact Set.iInter_subset _ (n + 1)
  have hlimitLe :
      countableStoppingLimitMeasure nu event cost C (event i) ≤
        countableStoppingRemainder nu event cost C (n + 1) (event i) := by
    rw [countableStoppingLimitMeasure,
      countableStoppingRemainder_eq_restrict
        nu event cost C eventsMeasurable (n + 1),
      Measure.restrict_apply (eventsMeasurable i),
      Measure.restrict_apply (eventsMeasurable i)]
    exact measure_mono (Set.inter_subset_inter_right _ hcarrierSubset)
  exact bot_unique (hlimitLe.trans_eq hnextZero)

/-- The fair countable stopping limit satisfies every enumerated relative cap
bound.  Thus no bad event can survive merely by being postponed to later
stages. -/
theorem countableStoppingLimitMeasure_good
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (eventsMeasurable : ∀ i, MeasurableSet (event i))
    (hfinite : nu Set.univ ≠ ⊤) :
    ∀ i,
      countableStoppingLimitMeasure nu event cost C (event i) ≤
        C * countableStoppingLimitMeasure nu event cost C Set.univ * cost i := by
  intro i
  by_contra hnotGood
  have hbad :
      C * countableStoppingLimitMeasure nu event cost C Set.univ * cost i <
        countableStoppingLimitMeasure nu event cost C (event i) :=
    lt_of_not_ge hnotGood
  have heventPositive :
      0 < countableStoppingLimitMeasure nu event cost C (event i) :=
    lt_of_le_of_lt bot_le hbad
  have hunivPositive :
      0 < countableStoppingLimitMeasure nu event cost C Set.univ :=
    heventPositive.trans_le (measure_mono (Set.subset_univ (event i)))
  have hunivNonzero :
      countableStoppingLimitMeasure nu event cost C Set.univ ≠ 0 :=
    hunivPositive.ne'
  have huniv := tendsto_countableStoppingRemainder_univ
    nu event cost C eventsMeasurable hfinite
  have hevent := tendsto_countableStoppingRemainder_event
    nu event cost C eventsMeasurable hfinite i
  have hleft :
      Tendsto
        (fun n ↦ C *
          countableStoppingRemainder nu event cost C n Set.univ * cost i)
        atTop
        (nhds (C * countableStoppingLimitMeasure nu event cost C Set.univ *
          cost i)) := by
    by_cases hC : C = 0
    · simpa [hC] using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ ↦ (0 : ENNReal)) atTop (nhds 0))
    · have hfirst := ENNReal.Tendsto.const_mul (a := C)
        huniv (Or.inl hunivNonzero)
      exact ENNReal.Tendsto.mul_const (b := cost i) hfirst
        (Or.inl (mul_ne_zero hC hunivNonzero))
  obtain ⟨middle, hleftMiddle, hmiddleEvent⟩ := exists_between hbad
  have hleftEventually :
      ∀ᶠ n in atTop,
        C * countableStoppingRemainder nu event cost C n Set.univ * cost i <
          middle :=
    (tendsto_order.mp hleft).2 middle hleftMiddle
  have heventEventually :
      ∀ᶠ n in atTop,
        middle < countableStoppingRemainder nu event cost C n (event i) :=
    (tendsto_order.mp hevent).1 middle hmiddleEvent
  have hbadEventually :
      ∀ᶠ n in atTop,
        C * countableStoppingRemainder nu event cost C n Set.univ * cost i <
          countableStoppingRemainder nu event cost C n (event i) := by
    filter_upwards [hleftEventually, heventEventually] with n hnLeft hnEvent
    exact hnLeft.trans hnEvent
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbadEventually
  obtain ⟨n, hnN, hindex⟩ :=
    exists_fairCountableStoppingIndex_eq_ge i N
  have hzero :=
    countableStoppingLimitMeasure_event_eq_zero_of_removed_at
      nu event cost C eventsMeasurable n i hindex (hN n hnN)
  exact heventPositive.ne' hzero

/-- Exact one-step conservation for the fair scan. -/
theorem countableStopping_step_conservation
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (eventsMeasurable : ∀ i, MeasurableSet (event i))
    (n : ℕ) :
    countableStoppingRemainder nu event cost C n Set.univ =
      countableStoppingRemovedMass nu event cost C n +
        countableStoppingRemainder nu event cost C (n + 1) Set.univ := by
  let current := countableStoppingRemainder nu event cost C n
  let i := fairCountableStoppingIndex n
  by_cases hlarge : C * current Set.univ * cost i < current (event i)
  · have hsplit : current Set.univ =
        current (event i) + current.restrict (event i)ᶜ Set.univ := by
      calc
        current Set.univ =
            (current.restrict (event i) +
              current.restrict (event i)ᶜ) Set.univ := by
          rw [Measure.restrict_add_restrict_compl (eventsMeasurable i)]
        _ = current (event i) +
            current.restrict (event i)ᶜ Set.univ := by
          simp [Measure.add_apply, Measure.restrict_apply]
    simpa [countableStoppingRemovedMass, countableStoppingRemainder,
      current, i, hlarge] using hsplit
  · simp [countableStoppingRemovedMass, countableStoppingRemainder,
      current, i, hlarge]

/-- Every stage charge is bounded by the actual mass removed at that stage. -/
theorem countableStoppingCharge_le_removedMass
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (n : ℕ) :
    countableStoppingCharge nu event cost C n ≤
      countableStoppingRemovedMass nu event cost C n := by
  let current := countableStoppingRemainder nu event cost C n
  let i := fairCountableStoppingIndex n
  by_cases hlarge : C * current Set.univ * cost i < current (event i)
  · simpa [countableStoppingCharge, countableStoppingRemovedMass,
      current, i, hlarge] using hlarge.le
  · simp [countableStoppingCharge, countableStoppingRemovedMass,
      current, i, hlarge]

/-- Exact finite-prefix telescope for the countable stopping scan. -/
theorem countableStopping_prefix_conservation
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (eventsMeasurable : ∀ i, MeasurableSet (event i)) :
    ∀ N : ℕ,
      nu Set.univ =
        (∑ n ∈ Finset.range N,
          countableStoppingRemovedMass nu event cost C n) +
        countableStoppingRemainder nu event cost C N Set.univ := by
  intro N
  induction N with
  | zero => simp [countableStoppingRemainder]
  | succ N ih =>
      have hstep := countableStopping_step_conservation
        nu event cost C eventsMeasurable N
      calc
        nu Set.univ =
            (∑ n ∈ Finset.range N,
              countableStoppingRemovedMass nu event cost C n) +
            countableStoppingRemainder nu event cost C N Set.univ := ih
        _ = (∑ n ∈ Finset.range N,
              countableStoppingRemovedMass nu event cost C n) +
            (countableStoppingRemovedMass nu event cost C N +
              countableStoppingRemainder nu event cost C (N + 1) Set.univ) := by
          rw [hstep]
        _ = ((∑ n ∈ Finset.range N,
              countableStoppingRemovedMass nu event cost C n) +
              countableStoppingRemovedMass nu event cost C N) +
            countableStoppingRemainder nu event cost C (N + 1) Set.univ := by
          ac_rfl
        _ = (∑ n ∈ Finset.range (N + 1),
              countableStoppingRemovedMass nu event cost C n) +
            countableStoppingRemainder nu event cost C (N + 1) Set.univ := by
          rw [Finset.sum_range_succ]

/-- Coefficient-one Carleson control at every finite scan depth. -/
theorem countableStopping_prefix_charge_le_removed
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      countableStoppingCharge nu event cost C n) ≤
    ∑ n ∈ Finset.range N,
      countableStoppingRemovedMass nu event cost C n := by
  exact Finset.sum_le_sum fun n _ ↦
    countableStoppingCharge_le_removedMass nu event cost C n

/-- Countable mass-conserving stopping in terminal-good-or-finite-paid form.
If the limiting good remainder has less than half the starting mass, continuity
from above detects this at a finite stage, where exact conservation forces the
removed prefix to contain at least half the mass. -/
theorem countableStopping_good_limit_or_paid_prefix
    {X : Type u} [MeasurableSpace X]
    (nu : Measure X) (event : ℕ → Set X) (cost : ℕ → ENNReal)
    (C : ENNReal) (eventsMeasurable : ∀ i, MeasurableSet (event i))
    (hfinite : nu Set.univ ≠ ⊤) :
    (nu Set.univ / 2 ≤
        countableStoppingLimitMeasure nu event cost C Set.univ ∧
      ∀ i,
        countableStoppingLimitMeasure nu event cost C (event i) ≤
          C * countableStoppingLimitMeasure nu event cost C Set.univ *
            cost i) ∨
    ∃ N : ℕ,
      nu Set.univ / 2 ≤
        ∑ n ∈ Finset.range N,
          countableStoppingRemovedMass nu event cost C n ∧
      (∑ n ∈ Finset.range N,
          countableStoppingCharge nu event cost C n) ≤
        ∑ n ∈ Finset.range N,
          countableStoppingRemovedMass nu event cost C n ∧
      nu Set.univ =
        (∑ n ∈ Finset.range N,
          countableStoppingRemovedMass nu event cost C n) +
        countableStoppingRemainder nu event cost C N Set.univ := by
  by_cases hhalf :
      nu Set.univ / 2 ≤
        countableStoppingLimitMeasure nu event cost C Set.univ
  · exact Or.inl ⟨hhalf,
      countableStoppingLimitMeasure_good
        nu event cost C eventsMeasurable hfinite⟩
  · right
    have hlimitLt :
        countableStoppingLimitMeasure nu event cost C Set.univ <
          nu Set.univ / 2 :=
      lt_of_not_ge hhalf
    have hsmallEventually :
        ∀ᶠ N in atTop,
          countableStoppingRemainder nu event cost C N Set.univ <
            nu Set.univ / 2 :=
      (tendsto_order.mp
        (tendsto_countableStoppingRemainder_univ
          nu event cost C eventsMeasurable hfinite)).2
        (nu Set.univ / 2) hlimitLt
    obtain ⟨N, hsmall⟩ := hsmallEventually.exists
    let removed : ENNReal :=
      ∑ n ∈ Finset.range N,
        countableStoppingRemovedMass nu event cost C n
    have hconservation := countableStopping_prefix_conservation
      nu event cost C eventsMeasurable N
    have hremovedHalf : nu Set.univ / 2 ≤ removed := by
      by_contra hnotRemoved
      have hremovedLt : removed < nu Set.univ / 2 :=
        lt_of_not_ge hnotRemoved
      have hcontradiction :
          removed + countableStoppingRemainder nu event cost C N Set.univ <
            nu Set.univ := by
        calc
          removed + countableStoppingRemainder nu event cost C N Set.univ <
              nu Set.univ / 2 + nu Set.univ / 2 :=
            ENNReal.add_lt_add hremovedLt hsmall
          _ = nu Set.univ := ENNReal.add_halves (nu Set.univ)
      rw [← hconservation] at hcontradiction
      exact (lt_irrefl _) hcontradiction
    refine ⟨N, ?_, ?_, hconservation⟩
    · exact hremovedHalf
    · exact countableStopping_prefix_charge_le_removed nu event cost C N

end StickyKakeya4
