import Theorems.Thm_StickyKakeya4_global_terminal_band

/-!
# Fixed-angle roots have no sufficiently small same-cap terminals

This is a guardrail for applying the global terminal-band ledger to a root
graph with a fixed positive direction separation, as in Proposition 7.76,
equation (305), of the manuscript. The root separation is an explicit
hypothesis, expressed as zero mass on pairs at distance less than `tau`.
The endpoint directions throughout are those of the original ordered pair.

If `R < tau`, the root gives zero mass to the closed direction band of width
`R`. Consequently, terminal measures with a measure-valued root budget and
support in that band have zero aggregate mass. In particular this applies
to original endpoint pairs lying in one terminal cap of radius at most `T`
when `2 * T < tau`.

The complementary direction band has exactly the entire root mass. Thus
bounding that cross-band mass is equivalent to bounding the root mass itself;
terminal vanishing alone gives no reduction of that remaining obligation.

This does not bound paid mass or cross-cap mass, nor does it refute the main
sticky Kakeya theorem. It exposes why shrinking same-cap terminals alone
cannot close the original edge mass: any remaining fixed-angle root mass
must be accounted for outside this terminal class. No assertion that all
root mass reaches these terminals is made. In particular, no separate
geometric theorem estimating paid or cross-cap mass is refuted here.
-/

open MeasureTheory Set
open scoped ENNReal

namespace StickyKakeya4.FixedAngleTerminalVanishing

variable {X D I : Type*} [MeasurableSpace X] [PseudoMetricSpace D]

/-- Almost-everywhere fixed-angle separation gives the precise null-set
hypothesis used below. -/
theorem root_strict_band_eq_zero_of_ae
    (root : Measure (X × X)) (direction : X → D) (tau : ℝ)
    (hseparation : ∀ᵐ p ∂root, tau ≤ dist (direction p.1) (direction p.2)) :
    root {p | dist (direction p.1) (direction p.2) < tau} = 0 := by
  simpa only [not_le] using (ae_iff.mp hseparation)

/-- A closed direction band strictly narrower than the root separation is
root-null. Measurability is unnecessary for this null-set containment. -/
theorem root_directionBand_eq_zero
    (root : Measure (X × X)) (direction : X → D) {R tau : ℝ}
    (hseparation : root {p | dist (direction p.1) (direction p.2) < tau} = 0)
    (hR : R < tau) :
    root (GlobalTerminalBand.directionBand direction R) = 0 := by
  apply measure_mono_null _ hseparation
  intro p hp
  exact lt_of_le_of_lt hp hR

variable [MeasurableSpace D] [BorelSpace D] [SecondCountableTopology D]

/-- The complementary band retains all fixed-angle root mass once the band
is narrower than the fixed separation. This equality uses no terminal data. -/
theorem root_compl_directionBand_eq_univ
    (root : Measure (X × X)) {direction : X → D}
    (hdirection : Measurable direction) {R tau : ℝ}
    (hseparation : root {p | dist (direction p.1) (direction p.2) < tau} = 0)
    (hR : R < tau) :
    root (GlobalTerminalBand.directionBand direction R)ᶜ = root univ := by
  have hnull := root_directionBand_eq_zero root direction hseparation hR
  simpa only [hnull, zero_add] using
    (measure_add_measure_compl (μ := root)
      (GlobalTerminalBand.measurableSet_directionBand hdirection R))

/-- Below the fixed separation, a proposed upper bound for cross-band root
mass is exactly the same upper-bound obligation for the entire root mass.
This does not rule out proving either bound using additional geometry. -/
theorem root_compl_directionBand_le_iff
    (root : Measure (X × X)) {direction : X → D}
    (hdirection : Measurable direction) {R tau : ℝ} (B : ℝ≥0∞)
    (hseparation : root {p | dist (direction p.1) (direction p.2) < tau} = 0)
    (hR : R < tau) :
    root (GlobalTerminalBand.directionBand direction R)ᶜ ≤ B ↔ root univ ≤ B := by
  rw [root_compl_directionBand_eq_univ root hdirection hseparation hR]

/-- A measure-valued root budget and terminal band support force the sum of
terminal masses to vanish below the fixed-angle separation. -/
theorem terminal_mass_eq_zero_of_fixed_angle
    (root : Measure (X × X)) (terminal : I → Measure (X × X))
    {direction : X → D} (hdirection : Measurable direction) {R tau : ℝ}
    (hseparation : root {p | dist (direction p.1) (direction p.2) < tau} = 0)
    (hR : R < tau) (hbudget : Measure.sum terminal ≤ root)
    (hsupport : ∀ i, terminal i (GlobalTerminalBand.directionBand direction R)ᶜ = 0) :
    (∑' i, terminal i univ) = 0 := by
  apply le_antisymm _ bot_le
  calc
    (∑' i, terminal i univ) ≤ root (GlobalTerminalBand.directionBand direction R) :=
      GlobalTerminalBand.terminal_mass_le_root_band root terminal _
        (GlobalTerminalBand.measurableSet_directionBand hdirection R) hbudget hsupport
    _ = 0 := root_directionBand_eq_zero root direction hseparation hR

/-- Under the same hypotheses, every individual terminal measure is zero. -/
theorem terminal_eq_zero_of_fixed_angle
    (root : Measure (X × X)) (terminal : I → Measure (X × X))
    {direction : X → D} (hdirection : Measurable direction) {R tau : ℝ}
    (hseparation : root {p | dist (direction p.1) (direction p.2) < tau} = 0)
    (hR : R < tau) (hbudget : Measure.sum terminal ≤ root)
    (hsupport : ∀ i, terminal i (GlobalTerminalBand.directionBand direction R)ᶜ = 0) :
    ∀ i, terminal i = 0 := by
  intro i
  apply Measure.measure_univ_eq_zero.mp
  apply le_antisymm _ bot_le
  calc
    terminal i univ ≤ ∑' j, terminal j univ := ENNReal.le_tsum i
    _ = 0 := terminal_mass_eq_zero_of_fixed_angle root terminal hdirection
      hseparation hR hbudget hsupport

/-- Nodewise same-cap support supplies the band invariant. No overlap or
relation among the cap centers is required. At `2 * T < tau`, the aggregate
mass of these inherited original endpoint pairs vanishes. -/
theorem terminal_mass_eq_zero_of_same_cap
    (root : Measure (X × X)) (terminal : I → Measure (X × X))
    {direction : X → D} (hdirection : Measurable direction)
    (center : I → D) (radius : I → ℝ) {T tau : ℝ}
    (hseparation : root {p | dist (direction p.1) (direction p.2) < tau} = 0)
    (hT : 2 * T < tau) (hbudget : Measure.sum terminal ≤ root)
    (hradius : ∀ i, radius i ≤ T)
    (hcaps : ∀ i, terminal i
      {p | direction p.1 ∈ Metric.closedBall (center i) (radius i) ∧
        direction p.2 ∈ Metric.closedBall (center i) (radius i)}ᶜ = 0) :
    (∑' i, terminal i univ) = 0 := by
  exact terminal_mass_eq_zero_of_fixed_angle root terminal hdirection
    hseparation hT hbudget
    (GlobalTerminalBand.band_support_of_cap_support terminal direction
      center radius T hradius hcaps)

end StickyKakeya4.FixedAngleTerminalVanishing
