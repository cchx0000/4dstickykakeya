import Theorems.Thm_StickyKakeya4_north_conditioned_boundary_packet_chain
import Theorems.Thm_StickyKakeya4_collision_edge_contact_residual

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace StickyKakeya4

/-- A point of the canonical front parametrization is the corresponding raw
marked-line front point, with the affine mark retained. -/
theorem frontParametrization_eq_rawFrontParam
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (z : FrontParameterSpace) :
    frontParametrization selector hmeasurable hvalid hselector z =
      rawFrontParam
        (selectorLine selector hmeasurable hvalid hselector z.1,
          (z.2 : ℝ)) := by
  rfl

/-- The uniform north-cap bound `d₄ ≥ 1/2` gives chart amplification at most
three. -/
theorem north_chartAmplification_le_three
    (line : MarkedLine) (hhalf : (1 / 2 : ℝ) ≤
      direction line (3 : Fin 4)) :
    |(direction line (3 : Fin 4))⁻¹| + 1 ≤ 3 := by
  have hpos : 0 < direction line (3 : Fin 4) :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hhalf
  have hinv : (direction line (3 : Fin 4))⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hpos).2 (by nlinarith)
  rw [abs_of_pos (inv_pos.mpr hpos)]
  linarith

/-- State-level north-chart probe control.  This formulation does not require
embedding the packet into an infinite chain, so it applies directly to a
budget-adapted retained child. -/
theorem ConditionedBoundaryPacketState.source_common_probe_of_north
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (state : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector)
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

/-- Pairwise state-level form of the north common-probe estimate. -/
theorem ConditionedBoundaryPacketState.source_pair_common_probe_of_north
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (state : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector)
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

/-- Every retained occurrence in one north conditioned packet has a common
contact probe at the packet center's fourth coordinate.  Its horizontal graph
evaluation lies within three packet radii of the common horizontal center. -/
theorem NorthConditionedBoundaryPacketChain.source_common_probe
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (northChain : NorthConditionedBoundaryPacketChain selector hmeasurable
      hvalid hselector) (n : ℕ) (z : FrontParameterSpace)
    (hz : z ∈ (northChain.chain.state n).source) :
    ‖northGraphEvaluation
        (selectorLine selector hmeasurable hvalid hselector z.1)
          ((northChain.chain.state n).center (3 : Fin 4)) -
      horizontalProjection (northChain.chain.state n).center‖ <
        3 * (northChain.chain.state n).radius := by
  let state := northChain.chain.state n
  let line := selectorLine selector hmeasurable hvalid hselector z.1
  have hlineValid : IsValidLine line := hvalid line line.property
  have hhalf : (1 / 2 : ℝ) ≤ direction line (3 : Fin 4) := by
    rw [direction_selectorLine selector hmeasurable hvalid hselector z.1]
    exact contactNorthParameterCap_direction_ge_half z
      (northChain.source_north n hz)
  have hlinePos : 0 < direction line (3 : Fin 4) :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hhalf
  have hnearFront :
      dist state.center
        (rawFrontParam (line, (z.2 : ℝ))) < state.radius := by
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
          (fixedHeightPoint line (state.center (3 : Fin 4)) -
            state.center)‖ := by
      rw [horizontalProjection_sub,
        horizontalProjection_fixedHeightPoint line
          (state.center (3 : Fin 4)) hlinePos.ne']
    _ ≤ ‖fixedHeightPoint line (state.center (3 : Fin 4)) -
          state.center‖ := norm_horizontalProjection_le _
    _ = dist (fixedHeightPoint line (state.center (3 : Fin 4)))
          state.center := by rw [dist_eq_norm]
    _ < 3 * state.radius := hfixedThree

/-- Pairwise form of the preceding common-probe estimate: any two retained
occurrences in the packet have graph evaluations separated by less than six
packet radii at the same physical height. -/
theorem NorthConditionedBoundaryPacketChain.source_pair_common_probe
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (northChain : NorthConditionedBoundaryPacketChain selector hmeasurable
      hvalid hselector) (n : ℕ) (z z' : FrontParameterSpace)
    (hz : z ∈ (northChain.chain.state n).source)
    (hz' : z' ∈ (northChain.chain.state n).source) :
    ‖northGraphEvaluation
        (selectorLine selector hmeasurable hvalid hselector z.1)
          ((northChain.chain.state n).center (3 : Fin 4)) -
      northGraphEvaluation
        (selectorLine selector hmeasurable hvalid hselector z'.1)
          ((northChain.chain.state n).center (3 : Fin 4))‖ <
        6 * (northChain.chain.state n).radius := by
  let c := horizontalProjection (northChain.chain.state n).center
  let u := northGraphEvaluation
    (selectorLine selector hmeasurable hvalid hselector z.1)
      ((northChain.chain.state n).center (3 : Fin 4))
  let v := northGraphEvaluation
    (selectorLine selector hmeasurable hvalid hselector z'.1)
      ((northChain.chain.state n).center (3 : Fin 4))
  have hzProbe := northChain.source_common_probe n z hz
  have hz'Probe := northChain.source_common_probe n z' hz'
  change ‖u - v‖ < 6 * (northChain.chain.state n).radius
  change ‖u - c‖ < 3 * (northChain.chain.state n).radius at hzProbe
  change ‖v - c‖ < 3 * (northChain.chain.state n).radius at hz'Probe
  calc
    ‖u - v‖ = ‖(u - c) + (c - v)‖ := by congr 1 <;> abel
    _ ≤ ‖u - c‖ + ‖c - v‖ := norm_add_le _ _
    _ = ‖u - c‖ + ‖v - c‖ := by rw [norm_sub_rev c v]
    _ < 3 * (northChain.chain.state n).radius +
        3 * (northChain.chain.state n).radius :=
      add_lt_add hzProbe hz'Probe
    _ = 6 * (northChain.chain.state n).radius := by ring

end StickyKakeya4
