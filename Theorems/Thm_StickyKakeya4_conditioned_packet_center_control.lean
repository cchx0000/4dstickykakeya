import Theorems.Thm_StickyKakeya4_conditioned_boundary_packet_extension

open MeasureTheory Set

noncomputable section

namespace StickyKakeya4

/-- If the retained parameter source already lies over one physical packet,
then a positive-mass conditioned extension has a quantitatively compatible
center.  The estimate is just the triangle inequality through a parameter
point in the positive-mass intersection; it introduces no compactness or
external Kakeya input. -/
theorem coherentBoundary_conditioned_packet_extension_with_center_control
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
    (oldCenter : E4) (oldRadius : ℝ)
    (hsourceSubset : source ⊆
      (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
        Metric.ball oldCenter oldRadius)
    (rho : ℝ) (hrho : 0 < rho) (hrhoOne : rho ≤ 1) :
    ∃ (x : E4) (r : ℝ),
      0 < r ∧ r < rho ∧
      0 < (frontParameterProbability : Measure FrontParameterSpace)
        (source ∩
          (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
            Metric.ball x r) ∧
      dist x oldCenter < r + oldRadius := by
  obtain ⟨x, r, hr, hrSmall, hintersectionPos⟩ :=
    coherentBoundary_conditioned_packet_extension selector hmeasurable
      hvalid hselector hboundary source hsourceMeasurable hsourcePos
      rho hrho hrhoOne
  let f : FrontParameterSpace → E4 :=
    frontParametrization selector hmeasurable hvalid hselector
  have hintersectionNonempty :
      (source ∩ f ⁻¹' Metric.ball x r).Nonempty :=
    nonempty_of_measure_ne_zero (ne_of_gt (by simpa [f] using hintersectionPos))
  obtain ⟨z, hzSource, hzNew⟩ := hintersectionNonempty
  have hzOld : f z ∈ Metric.ball oldCenter oldRadius :=
    hsourceSubset hzSource
  have hnew : dist (f z) x < r := Metric.mem_ball.mp hzNew
  have hold : dist (f z) oldCenter < oldRadius := Metric.mem_ball.mp hzOld
  refine ⟨x, r, hr, hrSmall, hintersectionPos, ?_⟩
  calc
    dist x oldCenter ≤ dist x (f z) + dist (f z) oldCenter :=
      dist_triangle _ _ _
    _ < r + oldRadius :=
      add_lt_add (by simpa [dist_comm] using hnew) hold

end StickyKakeya4
