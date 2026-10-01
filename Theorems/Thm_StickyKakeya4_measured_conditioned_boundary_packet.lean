import Theorems.Thm_StickyKakeya4_conditioned_boundary_packet_mass
import Theorems.Thm_StickyKakeya4_north_conditioned_boundary_probe_control

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace StickyKakeya4

/-- A positive-mass physical packet for a specified probability law on the
canonical direction--fibre parameter space.  Keeping the law as an explicit
parameter is essential for the packing-piece route: its retained law is not
the unconditioned canonical product probability. -/
structure MeasuredConditionedBoundaryPacketState
    (nu : Measure FrontParameterSpace)
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) where
  source : Set FrontParameterSpace
  center : E4
  radius : ℝ
  source_measurable : MeasurableSet source
  source_pos : 0 < nu source
  source_subset_ball : source ⊆
    (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
      Metric.ball center radius
  radius_pos : 0 < radius
  radius_le_one : radius ≤ 1

/-- Literal retained-source child relation for a fixed parameter law. -/
def IsMeasuredConditionedBoundaryPacketChild
    {nu : Measure FrontParameterSpace}
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (parent child : MeasuredConditionedBoundaryPacketState nu selector
      hmeasurable hvalid hselector) : Prop :=
  child.source = parent.source ∩
    (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
      Metric.ball child.center child.radius ∧
  child.radius < parent.radius / 4 ∧
  dist child.center parent.center < child.radius + parent.radius

/-- A fixed failed-Frostman exponent and an arbitrary-law packet oracle give a
genuine retained child below any affordable comparison scale.  The same law
measures the parent, child, and relative mass gain. -/
theorem MeasuredConditionedBoundaryPacketState.exists_quantitative_child_below
    {nu : Measure FrontParameterSpace}
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonFour : epsilon < 4)
    (horacle : ∀ (source : Set FrontParameterSpace),
      MeasurableSet source → 0 < nu source →
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        ∃ (x : E4) (r : ℝ),
          0 < r ∧ r < rho ∧
          nu source *
              (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
                (ENNReal.ofReal r).rpow (4 - epsilon)) <
            nu (source ∩
              (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
                Metric.ball x r))
    (parent : MeasuredConditionedBoundaryPacketState nu selector
      hmeasurable hvalid hselector)
    (rho : ℝ) (hrho : 0 < rho) (hrhoQuarter : rho ≤ parent.radius / 4)
    (hrhoOne : rho ≤ 1) :
    ∃ child : MeasuredConditionedBoundaryPacketState nu selector
        hmeasurable hvalid hselector,
      IsMeasuredConditionedBoundaryPacketChild parent child ∧
      child.radius < rho ∧
      nu parent.source *
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal child.radius).rpow (4 - epsilon)) <
        nu child.source := by
  obtain ⟨x, r, hr, hrSmall, hmass⟩ :=
    horacle parent.source parent.source_measurable parent.source_pos
      rho hrho hrhoOne
  let f : FrontParameterSpace → E4 :=
    frontParametrization selector hmeasurable hvalid hselector
  let childSource : Set FrontParameterSpace :=
    parent.source ∩ f ⁻¹' Metric.ball x r
  have hchildMeasurable : MeasurableSet childSource := by
    exact parent.source_measurable.inter
      ((measurable_frontParametrization selector hmeasurable hvalid hselector)
        Metric.isOpen_ball.measurableSet)
  have hchildPos : 0 < nu childSource := by
    exact (bot_le : 0 ≤ nu parent.source *
      (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
        (ENNReal.ofReal r).rpow (4 - epsilon))).trans_lt
          (by simpa [childSource, f] using hmass)
  have hintersectionNonempty : childSource.Nonempty :=
    nonempty_of_measure_ne_zero (ne_of_gt hchildPos)
  obtain ⟨z, hzParent, hzNew⟩ := hintersectionNonempty
  have hzOld : f z ∈ Metric.ball parent.center parent.radius :=
    parent.source_subset_ball hzParent
  have hcenter : dist x parent.center < r + parent.radius := by
    calc
      dist x parent.center ≤ dist x (f z) + dist (f z) parent.center :=
        dist_triangle _ _ _
      _ < r + parent.radius := by
        exact add_lt_add
          (by simpa [dist_comm] using (Metric.mem_ball.mp hzNew))
          (Metric.mem_ball.mp hzOld)
  have hrQuarter : r < parent.radius / 4 := hrSmall.trans_le hrhoQuarter
  have hrOne : r ≤ 1 := (le_of_lt hrSmall).trans hrhoOne
  let child : MeasuredConditionedBoundaryPacketState nu selector
      hmeasurable hvalid hselector :=
    { source := childSource
      center := x
      radius := r
      source_measurable := hchildMeasurable
      source_pos := hchildPos
      source_subset_ball := by intro w hw; exact hw.2
      radius_pos := hr
      radius_le_one := hrOne }
  refine ⟨child, ?_, ?_, ?_⟩
  · exact ⟨rfl, hrQuarter, by simpa [child] using hcenter⟩
  · simpa [child] using hrSmall
  · simpa [child, childSource, f] using hmass

/-- A positive measured packet contains an actual retained parameter. -/
theorem MeasuredConditionedBoundaryPacketState.source_nonempty
    {nu : Measure FrontParameterSpace}
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (state : MeasuredConditionedBoundaryPacketState nu selector
      hmeasurable hvalid hselector) :
    state.source.Nonempty :=
  nonempty_of_measure_ne_zero (ne_of_gt state.source_pos)

/-- Common north-chart probe control is purely geometric and therefore holds
for a packet measured by any law. -/
theorem MeasuredConditionedBoundaryPacketState.source_common_probe_of_north
    {nu : Measure FrontParameterSpace}
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (state : MeasuredConditionedBoundaryPacketState nu selector
      hmeasurable hvalid hselector)
    (hstateNorth : state.source ⊆ contactNorthParameterCap)
    (z : FrontParameterSpace) (hz : z ∈ state.source) :
    ‖northGraphEvaluation
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (state.center (3 : Fin 4)) -
      horizontalProjection state.center‖ < 3 * state.radius := by
  let line := selectorLine selector hmeasurable hvalid hselector z.1
  have hlineValid : IsValidLine line := hvalid line line.property
  have hhalf : (1 / 2 : ℝ) ≤ direction line (3 : Fin 4) := by
    rw [direction_selectorLine selector hmeasurable hvalid hselector z.1]
    exact contactNorthParameterCap_direction_ge_half z (hstateNorth hz)
  have hlinePos : 0 < direction line (3 : Fin 4) :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hhalf
  have hnearFront :
      dist state.center (rawFrontParam (line, (z.2 : ℝ))) < state.radius := by
    have hzBall := state.source_subset_ball hz
    change dist
      (frontParametrization selector hmeasurable hvalid hselector z)
      state.center < state.radius at hzBall
    simpa [line, frontParametrization_eq_rawFrontParam, dist_comm] using hzBall
  have hfixed :=
    dist_fixedHeightPoint_lt_chartAmplification_mul_of_rawFrontParam_near
      line hlineValid hlinePos.ne' state.center (z.2 : ℝ) state.radius
      hnearFront
  have hfixedThree :
      dist (fixedHeightPoint line (state.center (3 : Fin 4)))
        state.center < 3 * state.radius := by
    refine hfixed.trans_le ?_
    exact mul_le_mul_of_nonneg_right
      (north_chartAmplification_le_three line hhalf) state.radius_pos.le
  calc
    ‖northGraphEvaluation line (state.center (3 : Fin 4)) -
        horizontalProjection state.center‖ =
        ‖horizontalProjection
          (fixedHeightPoint line (state.center (3 : Fin 4)) - state.center)‖ := by
      rw [horizontalProjection_sub,
        horizontalProjection_fixedHeightPoint line
          (state.center (3 : Fin 4)) hlinePos.ne']
    _ ≤ ‖fixedHeightPoint line (state.center (3 : Fin 4)) - state.center‖ :=
      norm_horizontalProjection_le _
    _ = dist (fixedHeightPoint line (state.center (3 : Fin 4)))
          state.center := by rw [dist_eq_norm]
    _ < 3 * state.radius := hfixedThree

/-- Pairwise common-probe form for two actual retained parameters. -/
theorem MeasuredConditionedBoundaryPacketState.source_pair_common_probe_of_north
    {nu : Measure FrontParameterSpace}
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (state : MeasuredConditionedBoundaryPacketState nu selector
      hmeasurable hvalid hselector)
    (hstateNorth : state.source ⊆ contactNorthParameterCap)
    (z z' : FrontParameterSpace) (hz : z ∈ state.source)
    (hz' : z' ∈ state.source) :
    ‖northGraphEvaluation
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (state.center (3 : Fin 4)) -
      northGraphEvaluation
        (selectorLine selector hmeasurable hvalid hselector z'.1)
          (state.center (3 : Fin 4))‖ < 6 * state.radius := by
  let c := horizontalProjection state.center
  let u := northGraphEvaluation
    (selectorLine selector hmeasurable hvalid hselector z.1)
      (state.center (3 : Fin 4))
  let v := northGraphEvaluation
    (selectorLine selector hmeasurable hvalid hselector z'.1)
      (state.center (3 : Fin 4))
  have hzProbe := state.source_common_probe_of_north hstateNorth z hz
  have hz'Probe := state.source_common_probe_of_north hstateNorth z' hz'
  change ‖u - v‖ < 6 * state.radius
  change ‖u - c‖ < 3 * state.radius at hzProbe
  change ‖v - c‖ < 3 * state.radius at hz'Probe
  calc
    ‖u - v‖ = ‖(u - c) + (c - v)‖ := by congr 1 <;> abel
    _ ≤ ‖u - c‖ + ‖c - v‖ := norm_add_le _ _
    _ = ‖u - c‖ + ‖v - c‖ := by rw [norm_sub_rev c v]
    _ < 3 * state.radius + 3 * state.radius :=
      add_lt_add hzProbe hz'Probe
    _ = 6 * state.radius := by ring

end StickyKakeya4
