import Theorems.Thm_StickyKakeya4_coherent_boundary_shrinking_packets

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- The coherent boundary can be restarted after restricting the canonical
marked direction--fibre law to any measurable positive-mass source.  The new
physical packet has radius below the prescribed request scale and meets the
retained source in positive original mass.  This is the measure-theoretic
extension step needed for compatible fresh-return histories; no external
Kakeya estimate is used. -/
theorem coherentBoundary_conditioned_packet_extension
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
    ∃ (x : E4) (r : ℝ),
      0 < r ∧ r < rho ∧
      0 < (frontParameterProbability : Measure FrontParameterSpace)
        (source ∩
          (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
            Metric.ball x r) := by
  letI : Nonempty FrontParameterSpace :=
    ⟨(metricSphereToNormSphere (Classical.choice metricSphereNonempty),
      ⟨0, by constructor <;> norm_num⟩)⟩
  obtain ⟨epsilon, hepsilon, hepsilonFour, hfailure⟩ :=
    coherentConcentrationBoundary_extracts_failed_frostman_scale
      selector hmeasurable hvalid hselector hboundary
  let mu : Measure FrontParameterSpace := frontParameterProbability
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
  have hleftPos :
      0 < base⁻¹ * (ENNReal.ofReal r).rpow q := by
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hbaseTop)
      (ne_of_gt
        (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr) ENNReal.ofReal_ne_top))
  have hconditionedTargetPos :
      0 < (conditioned : Measure FrontParameterSpace) target := by
    exact hleftPos.trans (by simpa [target, base, q] using hlarge)
  have hrawTargetPos : 0 < mu (target ∩ source) := by
    by_contra hnot
    have hrawZero : mu (target ∩ source) = 0 :=
      bot_unique (le_of_not_gt hnot)
    have hconditionedZero :
        (conditioned : Measure FrontParameterSpace) target = 0 := by
      change (conditionedFinite.normalize : Measure FrontParameterSpace) target = 0
      rw [conditionedFinite.toMeasure_normalize_eq_of_nonzero
        hconditionedFiniteNe, Measure.smul_apply]
      have hfiniteTargetZero :
          (conditionedFinite : Measure FrontParameterSpace) target = 0 := by
        change (mu.restrict source) target = 0
        rw [Measure.restrict_apply htargetMeasurable]
        exact hrawZero
      rw [hfiniteTargetZero]
      simp
    exact (ne_of_gt hconditionedTargetPos) hconditionedZero
  refine ⟨x, r, hr, hrSmall, ?_⟩
  simpa [mu, target, Set.inter_comm] using hrawTargetPos

end StickyKakeya4
