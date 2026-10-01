import Theorems.Thm_StickyKakeya4_conditioned_boundary_packet_extension

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- Quantitative conditioned packet extension at one fixed failed-Frostman
exponent.  The exponent and failure oracle are parameters, so the same loss is
retained after every later source restriction. -/
theorem conditioned_packet_extension_with_mass_of_failed_frostman_scale_for_measure
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilonFour : epsilon < 4)
    (hfailure : ∀ nu : Measure FrontParameterSpace,
      IsProbabilityMeasure nu →
      ∀ C : ENNReal, C ≠ ⊤ →
        ∃ (x : E4) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
          C * (ENNReal.ofReal r).rpow (4 - epsilon) <
            nu ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
              Metric.ball x r))
    (nu : Measure FrontParameterSpace)
    (hnuProbability : IsProbabilityMeasure nu)
    (source : Set FrontParameterSpace)
    (hsourceMeasurable : MeasurableSet source)
    (hsourcePos : 0 < nu source)
    (rho : ℝ) (hrho : 0 < rho) (hrhoOne : rho ≤ 1) :
    ∃ (x : E4) (r : ℝ),
      0 < r ∧ r < rho ∧
      nu source *
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal r).rpow (4 - epsilon)) <
        nu
          (source ∩
            (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
              Metric.ball x r) := by
  letI : Nonempty FrontParameterSpace :=
    ⟨(metricSphereToNormSphere (Classical.choice metricSphereNonempty),
      ⟨0, by constructor <;> norm_num⟩)⟩
  letI : IsProbabilityMeasure nu := hnuProbability
  let mu : Measure FrontParameterSpace := nu
  let conditionedFinite : FiniteMeasure FrontParameterSpace :=
    ⟨mu.restrict source, inferInstance⟩
  have hconditionedFiniteNe : conditionedFinite ≠ 0 := by
    intro hzero
    have hzero' : (conditionedFinite : Measure FrontParameterSpace) = 0 := by
      rw [hzero]
      rfl
    have hsourceZero : mu source = 0 :=
      Measure.restrict_eq_zero.mp (by simpa [conditionedFinite] using hzero')
    exact hsourcePos.ne' (by simpa [mu] using hsourceZero)
  let conditioned : ProbabilityMeasure FrontParameterSpace :=
    conditionedFinite.normalize
  letI : IsProbabilityMeasure (conditioned : Measure FrontParameterSpace) := by
    infer_instance
  let q : ℝ := 4 - epsilon
  have hq : 0 < q := by
    dsimp [q]
    linarith
  let base : ENNReal := (ENNReal.ofReal rho).rpow q
  have hbase0 : base ≠ 0 := by
    exact ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hrho)
      ENNReal.ofReal_ne_top)
  have hbaseTop : base ≠ ⊤ := by
    exact ne_of_lt
      (ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
  have hCtop : base⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hbase0
  obtain ⟨x, r, hr, hrOne, hlarge⟩ :=
    hfailure (conditioned : Measure FrontParameterSpace) (by infer_instance)
      base⁻¹ hCtop
  have hrSmall : r < rho := by
    by_contra hnot
    have hrhoLe : rho ≤ r := le_of_not_gt hnot
    have hpowMono : base ≤ (ENNReal.ofReal r).rpow q := by
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hrhoLe) hq.le
    have hone : 1 ≤ base⁻¹ * (ENNReal.ofReal r).rpow q := by
      calc
        1 = base⁻¹ * base := (ENNReal.inv_mul_cancel hbase0 hbaseTop).symm
        _ ≤ base⁻¹ * (ENNReal.ofReal r).rpow q := by gcongr
    have hprobability :
        (conditioned : Measure FrontParameterSpace)
            ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
              Metric.ball x r) ≤ 1 := by
      calc
        (conditioned : Measure FrontParameterSpace)
            ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
              Metric.ball x r) ≤
            (conditioned : Measure FrontParameterSpace) Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact (not_lt_of_ge (hprobability.trans hone))
      (by simpa [base, q] using hlarge)
  let target : Set FrontParameterSpace :=
    (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
      Metric.ball x r
  have htargetMeasurable : MeasurableSet target :=
    (measurable_frontParametrization selector hmeasurable hvalid hselector)
      Metric.isOpen_ball.measurableSet
  have hconditionedMassValue :
      (↑conditionedFinite.mass : ENNReal) = mu source := by
    simp [conditionedFinite, FiniteMeasure.mass, hsourceMeasurable]
  have hconditionedMassZero :
      (↑conditionedFinite.mass : ENNReal) ≠ 0 := by
    rw [hconditionedMassValue]
    exact (by simpa [mu] using hsourcePos.ne')
  have hconditionedNNMassZero : conditionedFinite.mass ≠ 0 := by
    intro hzero
    apply hconditionedMassZero
    rw [hzero]
    rfl
  have hconditionedMassTop :
      (↑conditionedFinite.mass : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hconditionedMassFormula :
      (conditioned : Measure FrontParameterSpace) target =
        (↑conditionedFinite.mass : ENNReal)⁻¹ * mu (target ∩ source) := by
    change (conditionedFinite.normalize : Measure FrontParameterSpace) target = _
    rw [conditionedFinite.toMeasure_normalize_eq_of_nonzero
      hconditionedFiniteNe, Measure.smul_apply]
    change (↑conditionedFinite.mass⁻¹ : ENNReal) *
      (mu.restrict source) target = _
    rw [Measure.restrict_apply htargetMeasurable]
    simpa [ENNReal.coe_inv hconditionedNNMassZero]
  have hraw :
      mu source * (base⁻¹ * (ENNReal.ofReal r).rpow q) <
        mu (target ∩ source) := by
    have hmul := ENNReal.mul_lt_mul_left hconditionedMassZero
      hconditionedMassTop (by simpa [target, q] using hlarge)
    rw [hconditionedMassFormula] at hmul
    calc
      mu source * (base⁻¹ * (ENNReal.ofReal r).rpow q) =
          (base⁻¹ * (ENNReal.ofReal r).rpow q) *
            (↑conditionedFinite.mass : ENNReal) := by
        rw [hconditionedMassValue]
        ac_rfl
      _ < (((↑conditionedFinite.mass : ENNReal)⁻¹ *
            mu (target ∩ source))) *
          (↑conditionedFinite.mass : ENNReal) := hmul
      _ = mu (target ∩ source) := by
        rw [show (((↑conditionedFinite.mass : ENNReal)⁻¹ *
              mu (target ∩ source))) *
              (↑conditionedFinite.mass : ENNReal) =
            ((↑conditionedFinite.mass : ENNReal)⁻¹ *
              (↑conditionedFinite.mass : ENNReal)) *
                mu (target ∩ source) by ac_rfl,
          ENNReal.inv_mul_cancel hconditionedMassZero hconditionedMassTop,
          one_mul]
  refine ⟨x, r, hr, hrSmall, ?_⟩
  simpa [mu, target, base, q, Set.inter_comm] using hraw

/-- Backward-compatible specialization to the canonical front parameter
probability. -/
theorem conditioned_packet_extension_with_mass_of_failed_frostman_scale
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilonFour : epsilon < 4)
    (hfailure : ∀ nu : Measure FrontParameterSpace,
      IsProbabilityMeasure nu →
      ∀ C : ENNReal, C ≠ ⊤ →
        ∃ (x : E4) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
          C * (ENNReal.ofReal r).rpow (4 - epsilon) <
            nu ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
              Metric.ball x r))
    (source : Set FrontParameterSpace)
    (hsourceMeasurable : MeasurableSet source)
    (hsourcePos :
      0 < (frontParameterProbability : Measure FrontParameterSpace) source)
    (rho : ℝ) (hrho : 0 < rho) (hrhoOne : rho ≤ 1) :
    ∃ (x : E4) (r : ℝ),
      0 < r ∧ r < rho ∧
      (frontParameterProbability : Measure FrontParameterSpace) source *
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal r).rpow (4 - epsilon)) <
        (frontParameterProbability : Measure FrontParameterSpace)
          (source ∩
            (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
              Metric.ball x r) := by
  exact conditioned_packet_extension_with_mass_of_failed_frostman_scale_for_measure
    selector hmeasurable hvalid hselector epsilon hepsilon hepsilonFour
      hfailure frontParameterProbability (by infer_instance) source
        hsourceMeasurable hsourcePos rho hrho hrhoOne

/-- The source-hereditary failed-Frostman packet oracle for an arbitrary
base probability law.  This is the version consumed by the packing-piece
finite source, whose parameter law need not be the canonical sphere--fibre
product law. -/
theorem coherentBoundary_conditioned_packet_extension_with_uniform_mass_for_measure
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (nu : Measure FrontParameterSpace)
    (hnuProbability : IsProbabilityMeasure nu) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
      ∀ (source : Set FrontParameterSpace),
        MeasurableSet source →
        0 < nu source →
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          ∃ (x : E4) (r : ℝ),
            0 < r ∧ r < rho ∧
            nu source *
                (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
                  (ENNReal.ofReal r).rpow (4 - epsilon)) <
              nu (source ∩
                (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
                  Metric.ball x r) := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hfailure⟩ :=
    coherentConcentrationBoundary_extracts_failed_frostman_scale
      selector hmeasurable hvalid hselector hboundary
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_⟩
  intro source hsourceMeasurable hsourcePos rho hrho hrhoOne
  exact conditioned_packet_extension_with_mass_of_failed_frostman_scale_for_measure
    selector hmeasurable hvalid hselector epsilon hepsilon hepsilonFour
      hfailure nu hnuProbability source hsourceMeasurable hsourcePos
        rho hrho hrhoOne

/-- A coherent boundary chooses one failed exponent once and for all.  Every
measurable positive-mass descendant of the canonical marked parameter law
then has a smaller packet with the same relative mass exponent.  This is the
source-hereditary packet oracle required by the mass-conserving stopping
argument. -/
theorem coherentBoundary_conditioned_packet_extension_with_uniform_mass
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
      ∀ (source : Set FrontParameterSpace),
        MeasurableSet source →
        0 < (frontParameterProbability : Measure FrontParameterSpace) source →
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          ∃ (x : E4) (r : ℝ),
            0 < r ∧ r < rho ∧
            (frontParameterProbability : Measure FrontParameterSpace) source *
                (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
                  (ENNReal.ofReal r).rpow (4 - epsilon)) <
              (frontParameterProbability : Measure FrontParameterSpace)
                (source ∩
                  (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
                    Metric.ball x r) := by
  exact
    coherentBoundary_conditioned_packet_extension_with_uniform_mass_for_measure
      selector hmeasurable hvalid hselector hboundary
        frontParameterProbability (by infer_instance)

/-- Single-source projection of the uniform packet oracle. -/
theorem coherentBoundary_conditioned_packet_extension_with_mass
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (source : Set FrontParameterSpace)
    (hsourceMeasurable : MeasurableSet source)
    (hsourcePos :
      0 < (frontParameterProbability : Measure FrontParameterSpace) source)
    (rho : ℝ) (hrho : 0 < rho) (hrhoOne : rho ≤ 1) :
    ∃ (epsilon : ℝ) (x : E4) (r : ℝ),
      0 < epsilon ∧ epsilon < 4 ∧
      0 < r ∧ r < rho ∧
      (frontParameterProbability : Measure FrontParameterSpace) source *
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal r).rpow (4 - epsilon)) <
        (frontParameterProbability : Measure FrontParameterSpace)
          (source ∩
            (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
              Metric.ball x r) := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, horacle⟩ :=
    coherentBoundary_conditioned_packet_extension_with_uniform_mass
      selector hmeasurable hvalid hselector hboundary
  obtain ⟨x, r, hr, hrho, hmass⟩ :=
    horacle source hsourceMeasurable hsourcePos rho hrho hrhoOne
  exact ⟨epsilon, x, r, hepsilon, hepsilonFour, hr, hrho, hmass⟩

end StickyKakeya4
