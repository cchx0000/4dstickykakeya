import Theorems.Thm_StickyKakeya4_countable_mass_stopping_prefix
import Mathlib.Topology.Bases

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

universe u v

/-- Dense center used by the countable physical-ball scan. -/
noncomputable def countableBallCenter
    (Y : Type v) [PseudoMetricSpace Y] [TopologicalSpace.SeparableSpace Y]
    [Nonempty Y] (n : ℕ) : Y :=
  TopologicalSpace.denseSeq Y (Nat.unpair n).1

/-- Nonnegative rational radius used by the countable physical-ball scan. -/
noncomputable def countableBallRadius (n : ℕ) : ℝ :=
  |(((Encodable.decode (α := ℚ) (Nat.unpair n).2).getD 0 : ℚ) : ℝ)|

/-- Every metric ball is contained in an enumerated dense-center rational ball
whose radius is strictly less than twice the original radius. -/
theorem exists_countableBall_cover
    (Y : Type v) [PseudoMetricSpace Y] [TopologicalSpace.SeparableSpace Y]
    [Nonempty Y] (x : Y) {r : ℝ} (hr : 0 < r) :
    ∃ n : ℕ,
      Metric.ball x r ⊆
        Metric.ball (countableBallCenter Y n) (countableBallRadius n) ∧
      0 < countableBallRadius n ∧
      countableBallRadius n < 2 * r := by
  have hinterval : 5 * r / 4 < 3 * r / 2 := by linarith
  obtain ⟨q : ℚ, hqLower, hqUpper⟩ := exists_rat_btwn hinterval
  have hqPos : 0 < (q : ℝ) := by linarith
  have hgapPos : 0 < (q : ℝ) - r := by linarith
  obtain ⟨k, hk⟩ :=
    (TopologicalSpace.denseRange_denseSeq (α := Y)).exists_dist_lt x hgapPos
  let qIndex : ℕ := Encodable.encode q
  let n := Nat.pair k qIndex
  have hqDecode : Encodable.decode (α := ℚ) qIndex = some q := by
    simpa [qIndex] using Encodable.encodek q
  have hcenter : countableBallCenter Y n = TopologicalSpace.denseSeq Y k := by
    simp [countableBallCenter, n, Nat.unpair_pair]
  have hradius : countableBallRadius n = (q : ℝ) := by
    simp [countableBallRadius, n, Nat.unpair_pair, hqDecode,
      abs_of_pos hqPos]
  refine ⟨n, ?_, ?_, ?_⟩
  · intro y hy
    rw [Metric.mem_ball] at hy ⊢
    rw [hcenter, hradius]
    calc
      dist y (TopologicalSpace.denseSeq Y k) ≤
          dist y x + dist x (TopologicalSpace.denseSeq Y k) :=
        dist_triangle _ _ _
      _ < r + ((q : ℝ) - r) := add_lt_add hy hk
      _ = (q : ℝ) := by ring
  · simpa [hradius] using hqPos
  · rw [hradius]
    linarith

/-- Pullback of the `n`-th enumerated physical ball. -/
noncomputable def countableBallEvent
    {X : Type u} (Y : Type v) [PseudoMetricSpace Y]
    [TopologicalSpace.SeparableSpace Y] [Nonempty Y]
    (f : X → Y) (n : ℕ) : Set X :=
  f ⁻¹' Metric.ball (countableBallCenter Y n) (countableBallRadius n)

/-- Frostman cost attached to the `n`-th enumerated physical ball. -/
noncomputable def countableBallCost
    (Y : Type v) [PseudoMetricSpace Y] [TopologicalSpace.SeparableSpace Y]
    [Nonempty Y] (d : ℝ) (n : ℕ) : ENNReal :=
  (ENNReal.ofReal (countableBallRadius n)).rpow d

theorem measurableSet_countableBallEvent
    {X : Type u} [MeasurableSpace X]
    (Y : Type v) [PseudoMetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [TopologicalSpace.SeparableSpace Y] [Nonempty Y]
    (f : X → Y) (hf : Measurable f) (n : ℕ) :
    MeasurableSet (countableBallEvent Y f n) := by
  exact hf measurableSet_ball

/-- Bounds on the countable dense-center rational balls imply bounds on all
physical balls, with only a factor-two enlargement of the radius. -/
theorem countableBall_bound_to_all_balls
    {X : Type u} [MeasurableSpace X]
    (Y : Type v) [PseudoMetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [TopologicalSpace.SeparableSpace Y] [Nonempty Y]
    (mu : Measure X) (f : X → Y) (C : ENNReal) (d : ℝ) (hd : 0 ≤ d)
    (hbound : ∀ n,
      mu (countableBallEvent Y f n) ≤
        C * mu Set.univ * countableBallCost Y d n) :
    ∀ x : Y, ∀ r : ℝ, 0 < r →
      mu (f ⁻¹' Metric.ball x r) ≤
        C * mu Set.univ * (ENNReal.ofReal (2 * r)).rpow d := by
  intro x r hr
  obtain ⟨n, hsubset, _hradiusPos, hradiusTwo⟩ :=
    exists_countableBall_cover Y x hr
  calc
    mu (f ⁻¹' Metric.ball x r) ≤ mu (countableBallEvent Y f n) :=
      measure_mono (preimage_mono hsubset)
    _ ≤ C * mu Set.univ * countableBallCost Y d n := hbound n
    _ ≤ C * mu Set.univ * (ENNReal.ofReal (2 * r)).rpow d := by
      gcongr
      exact ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal hradiusTwo.le) hd

/-- The countable stopping theorem specialized to physical balls.  The good
branch is a genuine all-ball Frostman estimate; the other branch already has
a finite paid prefix carrying half the starting mass and coefficient-one
charge control. -/
theorem countableBall_good_limit_or_paid_prefix
    {X : Type u} [MeasurableSpace X]
    (Y : Type v) [PseudoMetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [TopologicalSpace.SeparableSpace Y] [Nonempty Y]
    (mu : Measure X) (f : X → Y) (hf : Measurable f)
    (C : ENNReal) (d : ℝ) (hd : 0 ≤ d) (hfinite : mu Set.univ ≠ ⊤) :
    let event : ℕ → Set X := countableBallEvent Y f
    let cost : ℕ → ENNReal := countableBallCost Y d
    let limit : Measure X :=
      countableStoppingLimitMeasure mu event cost C
    (mu Set.univ / 2 ≤ limit Set.univ ∧
      ∀ x : Y, ∀ r : ℝ, 0 < r →
        limit (f ⁻¹' Metric.ball x r) ≤
          C * limit Set.univ * (ENNReal.ofReal (2 * r)).rpow d) ∨
    ∃ N : ℕ,
      mu Set.univ / 2 ≤
        ∑ n ∈ Finset.range N,
          countableStoppingRemovedMass mu event cost C n ∧
      (∑ n ∈ Finset.range N,
          countableStoppingCharge mu event cost C n) ≤
        ∑ n ∈ Finset.range N,
          countableStoppingRemovedMass mu event cost C n ∧
      mu Set.univ =
        (∑ n ∈ Finset.range N,
          countableStoppingRemovedMass mu event cost C n) +
        countableStoppingRemainder mu event cost C N Set.univ := by
  dsimp only
  let event : ℕ → Set X := countableBallEvent Y f
  let cost : ℕ → ENNReal := countableBallCost Y d
  have heventMeasurable : ∀ n, MeasurableSet (event n) := fun n ↦
    measurableSet_countableBallEvent Y f hf n
  rcases countableStopping_good_limit_or_paid_prefix
      mu event cost C heventMeasurable hfinite with hgood | hpaid
  · left
    refine ⟨hgood.1, ?_⟩
    exact countableBall_bound_to_all_balls Y
      (countableStoppingLimitMeasure mu event cost C) f C d hd hgood.2
  · exact Or.inr hpaid

end StickyKakeya4
