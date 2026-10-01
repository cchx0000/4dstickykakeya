import Theorems.Thm_StickyKakeya4_conditioned_packet_center_control
import Theorems.Thm_StickyKakeya4_four_probe_cauchy_extraction

open Filter MeasureTheory Set Topology

noncomputable section

namespace StickyKakeya4

/-- One positive-mass conditioned concentration packet.  The source is kept
inside the displayed physical ball, so later packet extensions inherit an
actual common physical occurrence rather than only a scalar mass bound. -/
structure ConditionedBoundaryPacketState
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) where
  source : Set FrontParameterSpace
  center : E4
  radius : ℝ
  source_measurable : MeasurableSet source
  source_pos :
    0 < (frontParameterProbability : Measure FrontParameterSpace) source
  source_subset_ball : source ⊆
    (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
      Metric.ball center radius
  radius_pos : 0 < radius
  radius_le_one : radius ≤ 1

/-- The parent/child relation for conditioned packets.  It records literal
source restriction, geometric radius contraction, and center motion through
one retained parameter point. -/
def IsConditionedBoundaryPacketChild
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (parent child : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector) : Prop :=
  child.source = parent.source ∩
    (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
      Metric.ball child.center child.radius ∧
  child.radius < parent.radius / 4 ∧
  dist child.center parent.center < child.radius + parent.radius

/-- Every conditioned packet has a strictly smaller positive-mass child.
The coherent-boundary oracle is applied only after restricting and
normalizing the current source, and the two centers are compared through a
point retained by both packets. -/
theorem ConditionedBoundaryPacketState.exists_child
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (parent : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector) :
    ∃ child : ConditionedBoundaryPacketState selector hmeasurable
        hvalid hselector,
      IsConditionedBoundaryPacketChild parent child := by
  have hrho : 0 < parent.radius / 4 := by linarith [parent.radius_pos]
  have hrhoOne : parent.radius / 4 ≤ 1 := by
    have hquarter : parent.radius / 4 ≤ (1 : ℝ) / 4 :=
      (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2
        parent.radius_le_one
    exact hquarter.trans (by norm_num)
  obtain ⟨x, r, hr, hrSmall, hsourcePos, hcenter⟩ :=
    coherentBoundary_conditioned_packet_extension_with_center_control
      selector hmeasurable hvalid hselector hboundary
      parent.source parent.source_measurable parent.source_pos
      parent.center parent.radius parent.source_subset_ball
      (parent.radius / 4) hrho hrhoOne
  let f : FrontParameterSpace → E4 :=
    frontParametrization selector hmeasurable hvalid hselector
  let childSource : Set FrontParameterSpace :=
    parent.source ∩ f ⁻¹' Metric.ball x r
  have hchildMeasurable : MeasurableSet childSource := by
    exact parent.source_measurable.inter
      ((measurable_frontParametrization selector hmeasurable hvalid hselector)
        Metric.isOpen_ball.measurableSet)
  have hrOne : r ≤ 1 := by
    exact le_trans (le_of_lt hrSmall) hrhoOne
  let child : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector :=
    { source := childSource
      center := x
      radius := r
      source_measurable := hchildMeasurable
      source_pos := by simpa [childSource, f] using hsourcePos
      source_subset_ball := by
        intro z hz
        exact hz.2
      radius_pos := hr
      radius_le_one := hrOne }
  refine ⟨child, ?_⟩
  refine ⟨?_, hrSmall, ?_⟩
  · rfl
  · simpa [child] using hcenter

/-- A full dependent-choice history of nested positive-mass packets. -/
structure ConditionedBoundaryPacketChain
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) where
  state : ℕ → ConditionedBoundaryPacketState selector hmeasurable
    hvalid hselector
  child : ∀ n, IsConditionedBoundaryPacketChild (state n) (state (n + 1))

/-- Literal source restriction makes every child source a subset of its
parent source. -/
theorem ConditionedBoundaryPacketChain.source_succ_subset
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (chain : ConditionedBoundaryPacketChain selector hmeasurable
      hvalid hselector) (n : ℕ) :
    (chain.state (n + 1)).source ⊆ (chain.state n).source := by
  rw [(chain.child n).1]
  exact Set.inter_subset_left

/-- Classical choice of one child, used only to package the serial packet
relation into a countable history. -/
noncomputable def conditionedBoundaryPacketNext
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (parent : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector) :
    ConditionedBoundaryPacketState selector hmeasurable hvalid hselector :=
  Classical.choose (parent.exists_child hboundary)

theorem conditionedBoundaryPacketNext_isChild
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (parent : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector) :
    IsConditionedBoundaryPacketChild parent
      (conditionedBoundaryPacketNext hboundary parent) :=
  Classical.choose_spec (parent.exists_child hboundary)

/-- The coherent boundary supplies an initial localized packet and then one
compatible child at every depth.  No external Kakeya estimate is used. -/
theorem coherentBoundary_has_conditioned_packet_chain
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    Nonempty (ConditionedBoundaryPacketChain selector hmeasurable
      hvalid hselector) := by
  let f : FrontParameterSpace → E4 :=
    frontParametrization selector hmeasurable hvalid hselector
  obtain ⟨x, r, hr, hrOne, hmass⟩ :=
    coherentBoundary_conditioned_packet_extension selector hmeasurable
      hvalid hselector hboundary Set.univ MeasurableSet.univ
      (by simp) 1 (by norm_num) (by norm_num)
  let source : Set FrontParameterSpace := f ⁻¹' Metric.ball x r
  let initial : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector :=
    { source := source
      center := x
      radius := r
      source_measurable :=
        (measurable_frontParametrization selector hmeasurable hvalid hselector)
          Metric.isOpen_ball.measurableSet
      source_pos := by simpa [source, f] using hmass
      source_subset_ball := by intro z hz; exact hz
      radius_pos := hr
      radius_le_one := le_trans (le_of_lt hrOne) (le_refl 1) }
  let state : ℕ → ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector := fun n ↦
    (conditionedBoundaryPacketNext hboundary)^[n] initial
  refine ⟨⟨state, ?_⟩⟩
  intro n
  change IsConditionedBoundaryPacketChild
    ((conditionedBoundaryPacketNext hboundary)^[n] initial)
    ((conditionedBoundaryPacketNext hboundary)^[n + 1] initial)
  rw [Function.iterate_succ_apply']
  exact conditionedBoundaryPacketNext_isChild hboundary _

theorem ConditionedBoundaryPacketChain.radius_step_le
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (chain : ConditionedBoundaryPacketChain selector hmeasurable
      hvalid hselector) (n : ℕ) :
    (chain.state (n + 1)).radius ≤ (chain.state n).radius / 4 :=
  le_of_lt (chain.child n).2.1

theorem ConditionedBoundaryPacketChain.radius_geometric
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (chain : ConditionedBoundaryPacketChain selector hmeasurable
      hvalid hselector) (n : ℕ) :
    (chain.state n).radius ≤ 1 / (4 : ℝ) ^ n := by
  exact deterministic_cap_contraction_iterate
    (fun k ↦ (chain.state k).radius) 1 4 (by norm_num)
      (chain.state 0).radius_le_one chain.radius_step_le n

/-- The physical packet centers form a Cauchy sequence.  This is the first
cross-scale coherence output: it follows from literal nesting and geometric
radius contraction, not from an assumed limiting center. -/
theorem ConditionedBoundaryPacketChain.cauchy_center
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (chain : ConditionedBoundaryPacketChain selector hmeasurable
      hvalid hselector) :
    CauchySeq (fun n ↦ (chain.state n).center) := by
  apply cauchySeq_of_geometric_successive_dist
    (fun n ↦ (chain.state n).center) (5 / 4 : ℝ) (1 / 4 : ℝ)
      (by norm_num) (by norm_num) (by norm_num)
  intro n
  have hmotion := le_of_lt (chain.child n).2.2
  have hnext := chain.radius_step_le n
  have hcurrent := chain.radius_geometric n
  calc
    dist (chain.state n).center (chain.state (n + 1)).center =
        dist (chain.state (n + 1)).center (chain.state n).center :=
      dist_comm _ _
    _ ≤ (chain.state (n + 1)).radius + (chain.state n).radius := hmotion
    _ ≤ (5 / 4 : ℝ) * (chain.state n).radius := by linarith
    _ ≤ (5 / 4 : ℝ) * (1 / (4 : ℝ) ^ n) := by
      gcongr
    _ = (5 / 4 : ℝ) * (1 / 4 : ℝ) ^ n := by
      simp [one_div, inv_pow]

theorem ConditionedBoundaryPacketChain.radius_tendsto_zero
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (chain : ConditionedBoundaryPacketChain selector hmeasurable
      hvalid hselector) :
    Tendsto (fun n ↦ (chain.state n).radius) atTop (nhds 0) := by
  apply squeeze_zero
    (fun n ↦ (chain.state n).radius_pos.le)
    (fun n ↦ ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 : ℝ) / 4 < 1))
  simpa [one_div, inv_pow] using chain.radius_geometric n

/-- A canonical parameter witness from the positive-mass packet.  Choice is
made only after positivity has supplied nonemptiness. -/
noncomputable def ConditionedBoundaryPacketState.witness
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (state : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector) : FrontParameterSpace :=
  Classical.choose
    (nonempty_of_measure_ne_zero (ne_of_gt state.source_pos))

theorem ConditionedBoundaryPacketState.witness_mem_source
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (state : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector) :
    state.witness ∈ state.source :=
  Classical.choose_spec
    (nonempty_of_measure_ne_zero (ne_of_gt state.source_pos))

theorem ConditionedBoundaryPacketState.witness_physical_mem_ball
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (state : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector) :
    frontParametrization selector hmeasurable hvalid hselector state.witness ∈
      Metric.ball state.center state.radius :=
  state.source_subset_ball state.witness_mem_source

/-- Completeness supplies the common physical center approached by the
nested packet chain. -/
theorem ConditionedBoundaryPacketChain.exists_center_limit
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (chain : ConditionedBoundaryPacketChain selector hmeasurable
      hvalid hselector) :
    ∃ limit : E4,
      Tendsto (fun n ↦ (chain.state n).center) atTop (nhds limit) :=
  cauchySeq_tendsto_of_complete chain.cauchy_center

/-- Every chosen genuine parameter occurrence in the nested sources has a
physical image converging to the same center limit. -/
theorem ConditionedBoundaryPacketChain.witness_physical_tendsto
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (chain : ConditionedBoundaryPacketChain selector hmeasurable
      hvalid hselector)
    {limit : E4}
    (hcenter : Tendsto (fun n ↦ (chain.state n).center)
      atTop (nhds limit)) :
    Tendsto
      (fun n ↦ frontParametrization selector hmeasurable hvalid hselector
        (chain.state n).witness)
      atTop (nhds limit) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hcenterEventually : ∀ᶠ n in atTop,
      dist (chain.state n).center limit < epsilon / 2 := by
    have hball : Metric.ball limit (epsilon / 2) ∈ nhds limit :=
      Metric.ball_mem_nhds limit (by linarith)
    filter_upwards [hcenter hball] with n hn
    simpa [Metric.mem_ball] using hn
  have hradiusEventually : ∀ᶠ n in atTop,
      (chain.state n).radius < epsilon / 2 :=
    (tendsto_order.1 chain.radius_tendsto_zero).2
      (epsilon / 2) (by linarith)
  have hfinal : ∀ᶠ n in atTop,
      dist
        (frontParametrization selector hmeasurable hvalid hselector
          (chain.state n).witness)
        limit < epsilon := by
    filter_upwards [hcenterEventually, hradiusEventually] with n hc hr
    have hwitness :=
      Metric.mem_ball.mp (chain.state n).witness_physical_mem_ball
    calc
      dist
          (frontParametrization selector hmeasurable hvalid hselector
            (chain.state n).witness)
          limit ≤
        dist
            (frontParametrization selector hmeasurable hvalid hselector
              (chain.state n).witness)
            (chain.state n).center +
          dist (chain.state n).center limit :=
        dist_triangle _ _ _
      _ < (chain.state n).radius + epsilon / 2 :=
        add_lt_add hwitness hc
      _ < epsilon := by linarith
  exact Filter.eventually_atTop.1 hfinal

end StickyKakeya4
