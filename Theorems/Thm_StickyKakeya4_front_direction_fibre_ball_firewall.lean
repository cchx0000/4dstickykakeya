import Theorems.Thm_StickyKakeya4_front_two_probe_direction_firewall

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- A marked parameter source which is simultaneously localized in one
direction cap and one physical front ball has the full `3 + 1` product bound.
The three powers come from the spherical direction law and the last power is
the exact affine-fibre length. -/
theorem frontParameterProbability_source_le_directionCap_and_ball
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (source : Set FrontParameterSpace)
    (theta : {theta : E4 // ‖theta‖ = 1}) (x : E4) {r delta : ℝ}
    (hsourceCap : source ⊆ frontDirectionCap theta r)
    (hsourceBall : source ⊆
      (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
        Metric.ball x delta)
    (hr : 0 < r) (hrone : r ≤ 1) (hdelta : 0 ≤ delta) :
    (frontParameterProbability : Measure FrontParameterSpace) source ≤
      ENNReal.ofReal (2 * delta) *
        (metricSphereCapConstant * (ENNReal.ofReal r) ^ 3) := by
  let f : FrontParameterSpace → E4 :=
    frontParametrization selector hmeasurable hvalid hselector
  let target : Set FrontParameterSpace :=
    frontDirectionCap theta r ∩ f ⁻¹' Metric.ball x delta
  have htargetMeasurable : MeasurableSet target :=
    (measurableSet_frontDirectionCap theta r).inter
      (Metric.isOpen_ball.measurableSet.preimage
        (measurable_frontParametrization selector hmeasurable hvalid hselector))
  have hsourceTarget : source ⊆ target := by
    intro z hz
    exact ⟨hsourceCap hz, hsourceBall hz⟩
  calc
    (frontParameterProbability : Measure FrontParameterSpace) source ≤
        (frontParameterProbability : Measure FrontParameterSpace) target :=
      measure_mono hsourceTarget
    _ = ∫⁻ theta',
        (fibreIntervalProbability : Measure
          (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
          (Prod.mk theta' ⁻¹' target)
        ∂(normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1}) := by
      rw [frontParameterProbability, ProbabilityMeasure.toMeasure_prod]
      exact Measure.prod_apply htargetMeasurable
    _ ≤ ∫⁻ theta',
        (Metric.ball theta r).indicator
          (fun _ ↦ ENNReal.ofReal (2 * delta)) theta'
        ∂(normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1}) := by
      apply lintegral_mono
      intro theta'
      by_cases hcap : theta' ∈ Metric.ball theta r
      · rw [Set.indicator_of_mem hcap]
        have hsection : Prod.mk theta' ⁻¹' target =
            markedLineBallFibreSet
              (selectorLine selector hmeasurable hvalid hselector theta')
              x delta := by
          ext t
          simp [target, f, frontDirectionCap, markedLineBallFibreSet,
            frontParametrization, rawFrontParam, hcap]
        change (fibreIntervalProbability : Measure
          (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
            (Prod.mk theta' ⁻¹' target) ≤ ENNReal.ofReal (2 * delta)
        rw [hsection]
        exact fibreIntervalProbability_markedLineBallFibreSet_le
          (hvalid _ (selectorLine selector hmeasurable hvalid hselector
            theta').property) x hdelta
      · have hindicator :
            (Metric.ball theta r).indicator
              (fun _ ↦ ENNReal.ofReal (2 * delta)) theta' = 0 := by
            simp [hcap]
        rw [hindicator]
        have hsection : Prod.mk theta' ⁻¹' target = ∅ := by
          ext t
          simp [target, frontDirectionCap, hcap]
        change (fibreIntervalProbability : Measure
          (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
            (Prod.mk theta' ⁻¹' target) ≤ 0
        rw [hsection, measure_empty]
    _ = ENNReal.ofReal (2 * delta) *
        (normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1})
          (Metric.ball theta r) := by
      exact lintegral_indicator_const Metric.isOpen_ball.measurableSet _
    _ ≤ ENNReal.ofReal (2 * delta) *
        (metricSphereCapConstant * (ENNReal.ofReal r) ^ 3) := by
      gcongr
      exact normSphereProbability_ball_upper_bound theta hr hrone

/-- The source-hereditary two-probe estimate with the affine fibre retained.
Besides the two common graph probes, one physical ball containing the marked
occurrences supplies the fourth power which is absent from a direction-only
cap estimate. -/
theorem frontParameterProbability_source_le_of_two_probe_and_ball
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (source : Set FrontParameterSpace) (reference : MarkedLine)
    (href : reference ∈ selector)
    (hsourcePos : ∀ z ∈ source,
      0 < direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4))
    (hrefPos : 0 < direction reference (3 : Fin 4))
    (s t Rs Rt g eta : ℝ)
    (hRs : ∀ z ∈ source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1) s -
        northGraphEvaluation reference s‖ ≤ Rs)
    (hRt : ∀ z ∈ source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1) t -
        northGraphEvaluation reference t‖ ≤ Rt)
    (x : E4) (delta : ℝ)
    (hsourceBall : source ⊆
      (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
        Metric.ball x delta)
    (hRsNonneg : 0 ≤ Rs) (hRtNonneg : 0 ≤ Rt)
    (hg : 0 < g) (hsep : g ≤ |t - s|) (heta : 0 < eta)
    (hradiusOne : 2 * ((Rs + Rt) / g) + eta ≤ 1)
    (hdelta : 0 ≤ delta) :
    (frontParameterProbability : Measure FrontParameterSpace) source ≤
      ENNReal.ofReal (2 * delta) *
        (metricSphereCapConstant *
          (ENNReal.ofReal (2 * ((Rs + Rt) / g) + eta)) ^ 3) := by
  apply frontParameterProbability_source_le_directionCap_and_ball
    selector hmeasurable hvalid hselector source
      ⟨direction reference, (hvalid reference href).1⟩ x
  · exact source_subset_frontDirectionCap_of_two_probe
      selector hmeasurable hvalid hselector source reference href
      hsourcePos hrefPos s t Rs Rt g eta hRs hRt hg hsep heta
  · exact hsourceBall
  · have hquotient : 0 ≤ (Rs + Rt) / g :=
      div_nonneg (add_nonneg hRsNonneg hRtNonneg) hg.le
    nlinarith
  · exact hradiusOne
  · exact hdelta

end StickyKakeya4
