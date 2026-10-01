import Theorems.Thm_StickyKakeya4_conditioned_boundary_packet_chain

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace StickyKakeya4

/-- The canonical parameter event in which the retained marked direction lies
in one spherical cap.  The affine fibre coordinate is left completely free. -/
def frontDirectionCap
    (theta : {theta : E4 // ‖theta‖ = 1}) (r : ℝ) :
    Set FrontParameterSpace :=
  Prod.fst ⁻¹' Metric.ball theta r

theorem measurableSet_frontDirectionCap
    (theta : {theta : E4 // ‖theta‖ = 1}) (r : ℝ) :
    MeasurableSet (frontDirectionCap theta r) :=
  Metric.isOpen_ball.measurableSet.preimage measurable_fst

/-- The direction marginal of the canonical direction--fibre law is exactly
the normalized spherical measure.  In particular the unrestricted affine
mark does not change the mass of a direction cap. -/
theorem frontParameterProbability_frontDirectionCap
    (theta : {theta : E4 // ‖theta‖ = 1}) (r : ℝ) :
    (frontParameterProbability : Measure FrontParameterSpace)
        (frontDirectionCap theta r) =
      (normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1})
        (Metric.ball theta r) := by
  rw [frontParameterProbability, ProbabilityMeasure.toMeasure_prod]
  rw [show frontDirectionCap theta r =
      Metric.ball theta r ×ˢ (Set.univ : Set
        (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) by
    ext z
    simp [frontDirectionCap]]
  rw [Measure.prod_prod, measure_univ, mul_one]

/-- Cubic cap bound for a marked parameter source.  This is hereditary under
arbitrary measurable source restriction because only set inclusion is used. -/
theorem frontParameterProbability_source_le_directionCap
    (source : Set FrontParameterSpace)
    (theta : {theta : E4 // ‖theta‖ = 1}) {r : ℝ}
    (hsource : source ⊆ frontDirectionCap theta r)
    (hr : 0 < r) (hrone : r ≤ 1) :
    (frontParameterProbability : Measure FrontParameterSpace) source ≤
      metricSphereCapConstant * (ENNReal.ofReal r) ^ 3 := by
  calc
    (frontParameterProbability : Measure FrontParameterSpace) source ≤
        (frontParameterProbability : Measure FrontParameterSpace)
          (frontDirectionCap theta r) := measure_mono hsource
    _ = (normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1})
          (Metric.ball theta r) :=
      frontParameterProbability_frontDirectionCap theta r
    _ ≤ metricSphereCapConstant * (ENNReal.ofReal r) ^ 3 :=
      normSphereProbability_ball_upper_bound theta hr hrone

/-- A positive amount of canonical marked mass cannot be squeezed into one
direction cap below the explicit cubic threshold.  This is the quantitative
mass firewall needed after two separated probes have collapsed all surviving
directions into one cap. -/
theorem no_positive_mass_source_in_too_small_directionCap
    (source : Set FrontParameterSpace)
    (theta : {theta : E4 // ‖theta‖ = 1}) {q r : ℝ≥0∞}
    (hq : q ≤ (frontParameterProbability : Measure FrontParameterSpace) source)
    (hsource : source ⊆ frontDirectionCap theta r.toReal)
    (hrpos : r ≠ 0) (hrtop : r ≠ ⊤)
    (hrone : r ≤ 1)
    (hsmall : metricSphereCapConstant * r ^ 3 < q) : False := by
  have hrRealPos : 0 < r.toReal := ENNReal.toReal_pos hrpos hrtop
  have hrRealOne : r.toReal ≤ 1 := by
    have := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hrone
    simpa using this
  have hcap := frontParameterProbability_source_le_directionCap
    source theta hsource hrRealPos hrRealOne
  have hofReal : ENNReal.ofReal r.toReal = r := ENNReal.ofReal_toReal hrtop
  rw [hofReal] at hcap
  exact (not_lt_of_ge (hq.trans hcap)) hsmall

end StickyKakeya4
