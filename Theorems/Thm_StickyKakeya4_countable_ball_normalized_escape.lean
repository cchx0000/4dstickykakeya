import Theorems.Thm_StickyKakeya4_countable_ball_stopping

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

universe u v

/-- Normalize the positive-mass good remainder of the countable ball scan.
The factor-two enlargement used to pass from the countable dense family to
all balls is absorbed in the finite Frostman coefficient.  The alternative
retains the exact finite paid prefix, so no mass is discarded between the
measure branch and the geometric branch. -/
theorem countableBall_probability_escape_or_paid_prefix
    {X : Type u} [MeasurableSpace X] [Nonempty X]
    (Y : Type v) [PseudoMetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [TopologicalSpace.SeparableSpace Y] [Nonempty Y]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (f : X → Y) (hf : Measurable f)
    (C : ENNReal) (hCtop : C ≠ ⊤) (d : ℝ) (hd : 0 ≤ d) :
    let event : ℕ → Set X := countableBallEvent Y f
    let cost : ℕ → ENNReal := countableBallCost Y d
    let limit : Measure X :=
      countableStoppingLimitMeasure mu event cost C
    (∃ nu : Measure X,
      IsProbabilityMeasure nu ∧
      ∀ x : Y, ∀ r : ℝ, 0 < r →
        nu (f ⁻¹' Metric.ball x r) ≤
          (C * (2 : ENNReal).rpow d) *
            (ENNReal.ofReal r).rpow d) ∨
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
  let limit : Measure X :=
    countableStoppingLimitMeasure mu event cost C
  have hfinite : mu Set.univ ≠ ⊤ := by simp
  rcases countableBall_good_limit_or_paid_prefix
      Y mu f hf C d hd hfinite with hgood | hpaid
  · left
    have hlimitPos : 0 < limit Set.univ := by
      have : (0 : ENNReal) < mu Set.univ / 2 := by simp
      exact this.trans_le hgood.1
    have hlimitNe : limit ≠ 0 := by
      intro hzero
      have := congrArg (fun q : Measure X ↦ q Set.univ) hzero
      simpa using hlimitPos.ne' this
    let hlimitFinite : IsFiniteMeasure limit := by
      dsimp [limit, countableStoppingLimitMeasure]
      infer_instance
    let m : FiniteMeasure X := ⟨limit, hlimitFinite⟩
    let nu : Measure X := (m.normalize : Measure X)
    have hnuProbability : IsProbabilityMeasure nu := by
      dsimp [nu]
      infer_instance
    refine ⟨nu, hnuProbability, ?_⟩
    intro x r hr
    have hmNe : m ≠ 0 := by
      intro hmzero
      apply hlimitNe
      exact congrArg (fun q : FiniteMeasure X ↦ (q : Measure X)) hmzero
    have hmassValue : (↑m.mass : ENNReal) = limit Set.univ := by
      simp [m, FiniteMeasure.mass]
    have hmassZero : (↑m.mass : ENNReal) ≠ 0 := by
      rw [hmassValue]
      exact hlimitPos.ne'
    have hmassTop : (↑m.mass : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hmassNNZero : m.mass ≠ 0 := by
      intro hzero
      apply hmassZero
      simp [hzero]
    have hmassCancel :
        (↑m.mass⁻¹ : ENNReal) * limit Set.univ = 1 := by
      rw [← hmassValue]
      change (↑m.mass⁻¹ : ENNReal) * (↑m.mass : ENNReal) = 1
      rw [ENNReal.coe_inv hmassNNZero,
        ENNReal.inv_mul_cancel hmassZero hmassTop]
    have htwoR : ENNReal.ofReal (2 * r) =
        (2 : ENNReal) * ENNReal.ofReal r := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [show nu = (m.normalize : Measure X) by rfl,
      m.toMeasure_normalize_eq_of_nonzero hmNe, Measure.smul_apply]
    change (↑m.mass⁻¹ : ENNReal) * limit (f ⁻¹' Metric.ball x r) ≤ _
    calc
      (↑m.mass⁻¹ : ENNReal) * limit (f ⁻¹' Metric.ball x r) ≤
          (↑m.mass⁻¹ : ENNReal) *
            (C * limit Set.univ *
              (ENNReal.ofReal (2 * r)).rpow d) := by
        gcongr
        exact hgood.2 x r hr
      _ = C * (ENNReal.ofReal (2 * r)).rpow d := by
        rw [show (↑m.mass⁻¹ : ENNReal) *
              (C * limit Set.univ *
                (ENNReal.ofReal (2 * r)).rpow d) =
            ((↑m.mass⁻¹ : ENNReal) * limit Set.univ) * C *
                (ENNReal.ofReal (2 * r)).rpow d by ac_rfl]
        rw [hmassCancel, one_mul]
      _ = (C * (2 : ENNReal).rpow d) *
          (ENNReal.ofReal r).rpow d := by
        rw [htwoR]
        change C * ((2 * ENNReal.ofReal r) ^ d) =
          (C * (2 : ENNReal) ^ d) * (ENNReal.ofReal r) ^ d
        rw [ENNReal.mul_rpow_of_nonneg _ _ hd]
        ac_rfl
  · exact Or.inr hpaid

end StickyKakeya4
