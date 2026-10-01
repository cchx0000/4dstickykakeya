import Theorems.Thm_StickyKakeya4_countable_ball_normalized_escape
import Theorems.Thm_StickyKakeya4_front_parameter_probability

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- The positive coherent boundary cannot remain in the good remainder branch
of the fair countable ball scan.  At its fixed failed exponent, the scan with
coefficient one therefore removes at least half of the canonical marked
direction--fibre probability after finitely many stages.  The same prefix has
coefficient-one charge bounded by its actual removed mass, with exact mass
conservation. -/
theorem coherentBoundary_has_finite_paid_front_ball_prefix
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
      let f : FrontParameterSpace → E4 :=
        frontParametrization selector hmeasurable hvalid hselector
      let event : ℕ → Set FrontParameterSpace :=
        countableBallEvent E4 f
      let cost : ℕ → ENNReal :=
        countableBallCost E4 (4 - epsilon)
      ∃ N : ℕ,
        (1 : ENNReal) / 2 ≤
          ∑ n ∈ Finset.range N,
            countableStoppingRemovedMass
              (frontParameterProbability : Measure FrontParameterSpace)
              event cost 1 n ∧
        (∑ n ∈ Finset.range N,
            countableStoppingCharge
              (frontParameterProbability : Measure FrontParameterSpace)
              event cost 1 n) ≤
          ∑ n ∈ Finset.range N,
            countableStoppingRemovedMass
              (frontParameterProbability : Measure FrontParameterSpace)
              event cost 1 n ∧
        (1 : ENNReal) =
          (∑ n ∈ Finset.range N,
            countableStoppingRemovedMass
              (frontParameterProbability : Measure FrontParameterSpace)
              event cost 1 n) +
          countableStoppingRemainder
            (frontParameterProbability : Measure FrontParameterSpace)
            event cost 1 N Set.univ := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hfailure⟩ := hboundary.2
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_⟩
  let f : FrontParameterSpace → E4 :=
    frontParametrization selector hmeasurable hvalid hselector
  let event : ℕ → Set FrontParameterSpace := countableBallEvent E4 f
  let cost : ℕ → ENNReal := countableBallCost E4 (4 - epsilon)
  let mu : Measure FrontParameterSpace := frontParameterProbability
  letI : Nonempty FrontParameterSpace :=
    ⟨(metricSphereToNormSphere (Classical.choice metricSphereNonempty),
      ⟨0, by constructor <;> norm_num⟩)⟩
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hd : 0 ≤ 4 - epsilon := by linarith
  rcases countableBall_probability_escape_or_paid_prefix
      E4 mu f
      (measurable_frontParametrization selector hmeasurable hvalid hselector)
      1 (by simp) (4 - epsilon) hd with hgood | hpaid
  · obtain ⟨nu, hnuProbability, hnuBall⟩ := hgood
    let K : ENNReal := (2 : ENNReal).rpow (4 - epsilon)
    have hKtop : K ≠ ⊤ := by
      exact ne_of_lt
        (ENNReal.rpow_lt_top_of_nonneg hd ENNReal.ofNat_ne_top)
    obtain ⟨x, r, hr, hrOne, hlarge⟩ :=
      hfailure nu hnuProbability K hKtop
    have hsmall := hnuBall x r hr
    exfalso
    exact (not_lt_of_ge (by simpa [K] using hsmall)) hlarge
  · simpa [mu, f, event, cost] using hpaid

/-- A half-mass paid prefix contains an actual positive-mass stopped source.
The source is the current retained carrier intersected with the active marked
front-ball preimage, hence is measurable for the original canonical law.  Its
canonical mass equals both the current event mass and the mass removed at that
stage, and it strictly dominates the coefficient-one Frostman charge. -/
theorem coherentBoundary_has_positive_paid_front_ball_stage
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    ∃ (epsilon : ℝ) (n i : ℕ) (source : Set FrontParameterSpace),
      0 < epsilon ∧ epsilon < 4 ∧
      let f : FrontParameterSpace → E4 :=
        frontParametrization selector hmeasurable hvalid hselector
      let event : ℕ → Set FrontParameterSpace :=
        countableBallEvent E4 f
      let cost : ℕ → ENNReal :=
        countableBallCost E4 (4 - epsilon)
      i = fairCountableStoppingIndex n ∧
      source = event i ∩
        countableStoppingRemainderSet
          (frontParameterProbability : Measure FrontParameterSpace)
          event cost 1 n ∧
      MeasurableSet source ∧
      0 < (frontParameterProbability : Measure FrontParameterSpace) source ∧
      (frontParameterProbability : Measure FrontParameterSpace) source =
        countableStoppingRemovedMass
          (frontParameterProbability : Measure FrontParameterSpace)
          event cost 1 n ∧
      countableStoppingRemainder
          (frontParameterProbability : Measure FrontParameterSpace)
          event cost 1 n Set.univ * cost i <
        (frontParameterProbability : Measure FrontParameterSpace) source := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, N, hhalf, _hcharge,
      _hconservation⟩ :=
    coherentBoundary_has_finite_paid_front_ball_prefix
      selector hmeasurable hvalid hselector hboundary
  let f : FrontParameterSpace → E4 :=
    frontParametrization selector hmeasurable hvalid hselector
  let event : ℕ → Set FrontParameterSpace := countableBallEvent E4 f
  let cost : ℕ → ENNReal := countableBallCost E4 (4 - epsilon)
  let mu : Measure FrontParameterSpace := frontParameterProbability
  have heventMeasurable : ∀ j, MeasurableSet (event j) := fun j ↦
    measurableSet_countableBallEvent E4 f
      (measurable_frontParametrization selector hmeasurable hvalid hselector) j
  have hsumPos :
      0 < ∑ k ∈ Finset.range N,
        countableStoppingRemovedMass mu event cost 1 k := by
    have hhalfPos : (0 : ENNReal) < 1 / 2 := by norm_num
    exact hhalfPos.trans_le (by simpa [mu, f, event, cost] using hhalf)
  have hsumNe :
      (∑ k ∈ Finset.range N,
        countableStoppingRemovedMass mu event cost 1 k) ≠ 0 :=
    hsumPos.ne'
  have hexists : ∃ n ∈ Finset.range N,
      countableStoppingRemovedMass mu event cost 1 n ≠ 0 := by
    by_contra hnone
    apply hsumNe
    apply Finset.sum_eq_zero
    intro n hn
    by_contra hne
    exact hnone ⟨n, hn, hne⟩
  obtain ⟨n, hn, hremovedNe⟩ := hexists
  let i := fairCountableStoppingIndex n
  let current := countableStoppingRemainder mu event cost 1 n
  have hlarge : current Set.univ * cost i < current (event i) := by
    by_contra hnot
    have hzero : countableStoppingRemovedMass mu event cost 1 n = 0 := by
      simp [countableStoppingRemovedMass, current, i, hnot]
    exact hremovedNe hzero
  let source := event i ∩
    countableStoppingRemainderSet mu event cost 1 n
  have hsourceMeasurable : MeasurableSet source :=
    (heventMeasurable i).inter
      (measurableSet_countableStoppingRemainderSet
        mu event cost 1 heventMeasurable n)
  have hcurrentSource : current (event i) = mu source := by
    change countableStoppingRemainder mu event cost 1 n (event i) = mu source
    rw [countableStoppingRemainder_eq_restrict
      mu event cost 1 heventMeasurable n]
    rw [Measure.restrict_apply (heventMeasurable i)]
  have hsourcePos : 0 < mu source := by
    rw [← hcurrentSource]
    exact (bot_le : 0 ≤ current Set.univ * cost i).trans_lt hlarge
  have hremovedEq :
      mu source = countableStoppingRemovedMass mu event cost 1 n := by
    rw [countableStoppingRemovedMass]
    simp only [one_mul]
    change mu source =
      if current Set.univ * cost i < current (event i) then
        current (event i) else 0
    rw [if_pos hlarge]
    exact hcurrentSource.symm
  refine ⟨epsilon, n, i, source, hepsilon, hepsilonFour, ?_⟩
  refine ⟨rfl, rfl, hsourceMeasurable, ?_, ?_, ?_⟩
  · simpa [mu] using hsourcePos
  · simpa [mu] using hremovedEq
  · simpa [mu, current] using (hlarge.trans_eq hcurrentSource)

end StickyKakeya4
