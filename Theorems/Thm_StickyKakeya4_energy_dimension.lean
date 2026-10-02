import Theorems.Thm_StickyKakeya4_frostman_mass_distribution
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Finite energy gives supported Frostman measures

The energy-to-measure step used after Theorem 6.27 of the original manuscript.
Finite positive-exponent inverse-distance energy makes the potential finite
almost everywhere. A positive-mass bounded-potential restriction has a uniform
ball estimate; normalizing that restriction preserves its original support.

This proof neither closes the geometric residual estimate nor invokes an
unformalized slicing theorem. In particular, obtaining an extra longitudinal
dimension from the transverse projected energies remains a separate step.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section
namespace StickyKakeya4.EnergyDimension

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

/-- The singularity at coincident points is retained as infinity for `t > 0`. -/
def inverseDistancePotential (μ : Measure X) (t : ℝ) (x : X) : ℝ≥0∞ :=
  ∫⁻ y, edist x y ^ (-t) ∂μ

theorem measurable_inverseDistancePotential (μ : Measure X) [SFinite μ] (t : ℝ) :
    Measurable (inverseDistancePotential μ t) := by
  have h : Measurable (fun p : X × X => edist p.1 p.2 ^ (-t)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_edist
  exact h.lintegral_prod_right'

omit [SecondCountableTopology X] in
/-- A ball containing `x` is controlled by the inverse-distance potential at
`x`. The radius doubling is explicit and includes the singular diagonal. -/
theorem ball_mass_le_potential (μ : Measure X) (t : ℝ) (ht : 0 < t)
    (a x : X) (r : ℝ) (hr : 0 < r) (hx : x ∈ Metric.ball a r) :
    μ (Metric.ball a r) ≤ ENNReal.ofReal (2 * r) ^ t * inverseDistancePotential μ t x := by
  let R : ℝ≥0∞ := ENNReal.ofReal (2 * r)
  have hR0 : R ≠ 0 := by dsimp [R]; positivity
  have hRtop : R ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlower : R ^ (-t) * μ (Metric.ball a r) ≤ inverseDistancePotential μ t x := by
    calc
      R ^ (-t) * μ (Metric.ball a r) = ∫⁻ _y in Metric.ball a r, R ^ (-t) ∂μ := by
        simp only [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ y in Metric.ball a r, edist x y ^ (-t) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
        have hd : edist x y ≤ R := by
          rw [edist_dist]
          apply ENNReal.ofReal_le_ofReal
          have hxa : dist x a < r := Metric.mem_ball.mp hx
          have hay : dist a y < r := by simpa [dist_comm] using Metric.mem_ball.mp hy
          exact (dist_triangle x a y).trans (by linarith)
        rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
        exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hd ht.le)
      _ ≤ inverseDistancePotential μ t x := setLIntegral_le_lintegral _ _
  have hcancel : R ^ t * R ^ (-t) = 1 := by
    rw [← ENNReal.rpow_add t (-t) hR0 hRtop]
    simp
  calc
    μ (Metric.ball a r) = R ^ t * (R ^ (-t) * μ (Metric.ball a r)) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ R ^ t * inverseDistancePotential μ t x := mul_le_mul_right hlower _

/-- Restriction to a measurable bounded-potential piece yields a uniform
Frostman ball estimate, including balls centered outside the piece. -/
theorem restrict_ball_growth_of_bounded_potential
    (μ : Measure X) (t : ℝ) (ht : 0 < t)
    (G : Set X) (_hG : MeasurableSet G) (N : ℝ≥0∞)
    (hpotential : ∀ x ∈ G, inverseDistancePotential μ t x ≤ N)
    (a : X) (r : ℝ) (hr : 0 < r) :
    (μ.restrict G) (Metric.ball a r) ≤
      (N * (2 : ℝ≥0∞) ^ t) * ENNReal.ofReal r ^ t := by
  by_cases hzero : (μ.restrict G) (Metric.ball a r) = 0
  · rw [hzero]; exact bot_le
  · have hpos : μ (Metric.ball a r ∩ G) ≠ 0 := by
      rwa [Measure.restrict_apply Metric.isOpen_ball.measurableSet] at hzero
    obtain ⟨x, hxball, hxG⟩ := nonempty_of_measure_ne_zero hpos
    calc
      (μ.restrict G) (Metric.ball a r) ≤ μ (Metric.ball a r) := Measure.restrict_le_self _
      _ ≤ ENNReal.ofReal (2 * r) ^ t * inverseDistancePotential μ t x :=
        ball_mass_le_potential μ t ht a x r hr hxball
      _ ≤ ENNReal.ofReal (2 * r) ^ t * N := mul_le_mul_right (hpotential x hxG) _
      _ = (N * (2 : ℝ≥0∞) ^ t) * ENNReal.ofReal r ^ t := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.mul_rpow_of_nonneg _ _ ht.le]
        norm_num
        ac_rfl

/-- A finite integrable nonnegative function is uniformly bounded on a
positive-mass measurable piece of any nonzero finite measure. -/
theorem exists_bounded_measurable_piece
    {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (P : A → ℝ≥0∞) (hP : Measurable P)
    (hfiniteIntegral : (∫⁻ a, P a ∂μ) < ⊤) :
    ∃ G : Set A, MeasurableSet G ∧ μ G ≠ 0 ∧
      ∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ a ∈ G, P a ≤ N := by
  let G : ℕ → Set A := fun n => {x | P x ≤ (n : ℝ≥0∞)}
  have hfinite := ae_lt_top hP hfiniteIntegral.ne
  have hfull : ∀ᵐ x ∂μ, x ∈ ⋃ n, G n := by
    filter_upwards [hfinite] with x hx
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx.ne
    exact mem_iUnion.mpr ⟨n, hn.le⟩
  have hunion : μ (⋃ n, G n) ≠ 0 := by
    have hc : μ (⋃ n, G n)ᶜ = 0 := by
      exact mem_ae_iff.mp hfull
    intro hz
    have hall := measure_union_null hz hc
    rw [union_compl_self] at hall
    exact hμ (Measure.measure_univ_eq_zero.mp hall)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hunion
  exact ⟨G n, measurableSet_le hP measurable_const,
    hn.ne', (n : ℝ≥0∞), ENNReal.natCast_ne_top n, fun x hx => hx⟩

/-- A nonzero finite measure of finite energy contains a positive-mass
measurable piece on which its potential has a finite uniform bound. -/
theorem exists_bounded_potential_piece
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ ≠ 0) (t : ℝ)
    (henergy : (∫⁻ x, inverseDistancePotential μ t x ∂μ) < ⊤) :
    ∃ G : Set X, MeasurableSet G ∧ μ G ≠ 0 ∧
      ∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ x ∈ G, inverseDistancePotential μ t x ≤ N := by
  exact exists_bounded_measurable_piece μ hμ (inverseDistancePotential μ t)
    (measurable_inverseDistancePotential μ t) henergy

/-- Finite positive-exponent energy supplies a probability Frostman measure
carried by the very same set. No closure or weak-limit support substitution
occurs: the output is a normalized restriction of the input measure. -/
theorem exists_supported_frostman_probability_of_finite_energy
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (s : Set X) (hsupport : μ sᶜ = 0) (t : ℝ) (ht : 0 < t)
    (henergy : (∫⁻ x, inverseDistancePotential μ t x ∂μ) < ⊤) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ν sᶜ = 0 ∧
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (a : X) (r : ℝ), 0 < r →
        ν (Metric.ball a r) ≤ C * ENNReal.ofReal r ^ t := by
  obtain ⟨G, hG, hGpos, N, hN, hpotential⟩ :=
    exists_bounded_potential_piece μ hμ t henergy
  let : Nonempty X := ⟨(nonempty_of_measure_ne_zero hGpos).choose⟩
  let m : FiniteMeasure X := ⟨μ.restrict G, inferInstance⟩
  have hm : m ≠ 0 := by
    intro hzero
    have hz : μ.restrict G = 0 := congrArg (fun q : FiniteMeasure X => (q : Measure X)) hzero
    exact hGpos (Measure.restrict_eq_zero.mp hz)
  let ν : Measure X := (m.normalize : Measure X)
  let C : ℝ≥0∞ := (↑m.mass⁻¹ : ℝ≥0∞) * (N * (2 : ℝ≥0∞) ^ t)
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.mul_ne_top hN (ENNReal.rpow_ne_top_of_nonneg ht.le (by norm_num)))
  refine ⟨ν, by dsimp [ν]; infer_instance, ?_, C, hC, ?_⟩
  · have hs : (μ.restrict G) sᶜ = 0 :=
      le_antisymm ((Measure.restrict_le_self sᶜ).trans_eq hsupport) bot_le
    rw [show ν = (m.normalize : Measure X) by rfl,
      m.toMeasure_normalize_eq_of_nonzero hm, Measure.smul_apply]
    change (↑m.mass⁻¹ : ℝ≥0∞) * (μ.restrict G) sᶜ = 0
    rw [hs, mul_zero]
  · intro a r hr
    rw [show ν = (m.normalize : Measure X) by rfl,
      m.toMeasure_normalize_eq_of_nonzero hm, Measure.smul_apply]
    change (↑m.mass⁻¹ : ℝ≥0∞) * (μ.restrict G) (Metric.ball a r) ≤ C * ENNReal.ofReal r ^ t
    calc
      _ ≤ (↑m.mass⁻¹ : ℝ≥0∞) * ((N * (2 : ℝ≥0∞) ^ t) * ENNReal.ofReal r ^ t) :=
        mul_le_mul_right (restrict_ball_growth_of_bounded_potential μ t ht G hG N hpotential a r hr) _
      _ = _ := by dsimp [C]; ac_rfl

/-- The existing mass-distribution principle converts a supported finite
energy measure in physical four-space to a Hausdorff dimension lower bound. -/
theorem le_dimH_of_supported_finite_energy
    (μ : Measure E4) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (s : Set E4) (hsupport : μ sᶜ = 0) (t : NNReal) (ht : 0 < t)
    (henergy : (∫⁻ x, inverseDistancePotential μ (t : ℝ) x ∂μ) < ⊤) :
    (t : ℝ≥0∞) ≤ dimH s := by
  obtain ⟨ν, hν, hsν, C, hC, hball⟩ :=
    exists_supported_frostman_probability_of_finite_energy μ hμ s hsupport (t : ℝ)
      (by exact_mod_cast ht) henergy
  let : IsProbabilityMeasure ν := hν
  exact le_dimH_of_hausdorffMeasure_ne_zero
    (hausdorffMeasure_ne_zero_of_ball_growth ν s hsν C hC t ht
      (fun a r hr _ => hball a r hr))

/-- The supported-energy input at every exponent below four yields the
repository's original front-Frostman conclusion. This is an analytic adapter,
not a claim that geometric residual estimates already provide its hypotheses. -/
theorem hasFrontFrostmanMeasures_of_supported_finite_energies
    (selector : Set MarkedLine)
    (henergy : ∀ ε : ℝ, 0 < ε → ε < 4 →
      ∃ μ : Measure E4, IsFiniteMeasure μ ∧ μ ≠ 0 ∧
        μ (unitFront selector)ᶜ = 0 ∧
        (∫⁻ x, inverseDistancePotential μ (4 - ε) x ∂μ) < ⊤) :
    HasFrontFrostmanMeasures selector := by
  intro ε hε hε4
  obtain ⟨μ, hμfinite, hμ, hs, hE⟩ := henergy ε hε hε4
  let : IsFiniteMeasure μ := hμfinite
  obtain ⟨ν, hν, hsν, C, hC, hball⟩ :=
    exists_supported_frostman_probability_of_finite_energy μ hμ
      (unitFront selector) hs (4 - ε) (by linarith) hE
  exact ⟨ν, hν, hsν, C, hC, fun a r hr _ => hball a r hr⟩

/-- Finite energies on the actual front at every sub-four exponent imply the
required four-dimensional lower bound, with the original support unchanged. -/
theorem dimH_ge_four_of_supported_finite_energies
    (selector : Set MarkedLine)
    (henergy : ∀ ε : ℝ, 0 < ε → ε < 4 →
      ∃ μ : Measure E4, IsFiniteMeasure μ ∧ μ ≠ 0 ∧
        μ (unitFront selector)ᶜ = 0 ∧
        (∫⁻ x, inverseDistancePotential μ (4 - ε) x ∂μ) < ⊤) :
    (4 : ℝ≥0∞) ≤ dimH (unitFront selector) :=
  dimH_ge_four_of_front_frostman_measures selector
    (hasFrontFrostmanMeasures_of_supported_finite_energies selector henergy)

end StickyKakeya4.EnergyDimension
