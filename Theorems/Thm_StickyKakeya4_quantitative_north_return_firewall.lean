import Theorems.Thm_StickyKakeya4_quantitative_conditioned_boundary_packet_chain
import Theorems.Thm_StickyKakeya4_north_conditioned_boundary_probe_control
import Theorems.Thm_StickyKakeya4_front_direction_fibre_ball_firewall

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- The quantitative conditioned chain initialized in one fixed positive north
chart.  The same source restriction therefore carries both the four-dimensional
mass ledger and the uniform graph-coordinate estimates. -/
structure QuantitativeNorthConditionedBoundaryPacketChain
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) where
  chain : QuantitativeConditionedBoundaryPacketChain selector hmeasurable
    hvalid hselector
  source_north : ∀ n, (chain.state n).source ⊆ contactNorthParameterCap

def QuantitativeNorthConditionedBoundaryPacketChain.toNorthChain
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (chain : QuantitativeNorthConditionedBoundaryPacketChain selector
      hmeasurable hvalid hselector) :
    NorthConditionedBoundaryPacketChain selector hmeasurable hvalid hselector where
  chain := chain.chain.toChain
  source_north := chain.source_north

/-- A coherent boundary supplies the quantitative packet chain without ever
leaving the fixed north chart. -/
theorem coherentBoundary_has_quantitative_north_conditioned_packet_chain
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    Nonempty (QuantitativeNorthConditionedBoundaryPacketChain selector
      hmeasurable hvalid hselector) := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, horacle⟩ :=
    coherentBoundary_conditioned_packet_extension_with_uniform_mass
      selector hmeasurable hvalid hselector hboundary
  obtain ⟨x, r, hr, hrOne, hmass⟩ :=
    horacle contactNorthParameterCap measurableSet_contactNorthParameterCap
      frontParameterProbability_contactNorthParameterCap_pos
      1 (by norm_num) (by norm_num)
  let f : FrontParameterSpace → E4 :=
    frontParametrization selector hmeasurable hvalid hselector
  let source : Set FrontParameterSpace :=
    contactNorthParameterCap ∩ f ⁻¹' Metric.ball x r
  have hsourceMeasurable : MeasurableSet source :=
    measurableSet_contactNorthParameterCap.inter
      (Metric.isOpen_ball.measurableSet.preimage
        (measurable_frontParametrization selector hmeasurable hvalid hselector))
  have hsourcePos :
      0 < (frontParameterProbability : Measure FrontParameterSpace) source := by
    exact (bot_le : 0 ≤
      (frontParameterProbability : Measure FrontParameterSpace)
          contactNorthParameterCap *
        (((ENNReal.ofReal 1).rpow (4 - epsilon))⁻¹ *
          (ENNReal.ofReal r).rpow (4 - epsilon))).trans_lt
            (by simpa [source, f] using hmass)
  let initial : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector :=
    { source := source
      center := x
      radius := r
      source_measurable := hsourceMeasurable
      source_pos := hsourcePos
      source_subset_ball := by intro z hz; exact hz.2
      radius_pos := hr
      radius_le_one := le_of_lt hrOne }
  let next := quantitativeConditionedBoundaryPacketNext
    hepsilon hepsilonFour horacle
  let state : ℕ → ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector := fun n ↦ next^[n] initial
  let qchain : QuantitativeConditionedBoundaryPacketChain selector
      hmeasurable hvalid hselector :=
    { epsilon := epsilon
      epsilon_pos := hepsilon
      epsilon_lt_four := hepsilonFour
      state := state
      quantitative_child := by
        intro n
        change IsQuantitativeConditionedBoundaryPacketChild epsilon
          (next^[n] initial) (next^[n + 1] initial)
        rw [Function.iterate_succ_apply']
        exact quantitativeConditionedBoundaryPacketNext_spec
          hepsilon hepsilonFour horacle _ }
  refine ⟨⟨qchain, ?_⟩⟩
  intro n
  induction n with
  | zero =>
      intro z hz
      have hz' : z ∈ source := by
        simpa [qchain, state] using hz
      exact hz'.1
  | succ n ih =>
      exact (qchain.toChain.source_succ_subset n).trans ih

/-- The precise coefficient-one terminal for a fresh separated return.  The
ordinary packet center gives the first common probe.  Any second common probe
at a separated height forces a direction cap; the original packet ball keeps
the affine fibre and upgrades the cap law to four dimensions.  The recorded
relative child-mass lower bound then contradicts that upper bound as soon as
the displayed numerical budget closes. -/
theorem QuantitativeNorthConditionedBoundaryPacketChain.no_separated_return_at_child
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (northChain : QuantitativeNorthConditionedBoundaryPacketChain selector
      hmeasurable hvalid hselector)
    (n : ℕ) (t g E eta : ℝ) (outerCenter : E3)
    (hreturn : ∀ z ∈ (northChain.chain.state (n + 1)).source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1) t -
        outerCenter‖ ≤ E)
    (hE : 0 ≤ E) (hg : 0 < g)
    (hsep : g ≤
      |t - (northChain.chain.state (n + 1)).center (3 : Fin 4)|)
    (heta : 0 < eta)
    (hradiusOne :
      2 * ((6 * (northChain.chain.state (n + 1)).radius + 2 * E) / g) +
          eta ≤ 1)
    (hbudget :
      ENNReal.ofReal (2 * (northChain.chain.state (n + 1)).radius) *
          (metricSphereCapConstant *
            (ENNReal.ofReal
              (2 * ((6 * (northChain.chain.state (n + 1)).radius + 2 * E) / g) +
                eta)) ^ 3) ≤
        (frontParameterProbability : Measure FrontParameterSpace)
            (northChain.chain.state n).source *
          (((ENNReal.ofReal ((northChain.chain.state n).radius / 4)).rpow
              (4 - northChain.chain.epsilon))⁻¹ *
            (ENNReal.ofReal (northChain.chain.state (n + 1)).radius).rpow
              (4 - northChain.chain.epsilon))) :
    False := by
  let child := northChain.chain.state (n + 1)
  let referenceParameter := child.witness
  let reference : MarkedLine :=
    selectorLine selector hmeasurable hvalid hselector referenceParameter.1
  have hrefParameter : referenceParameter ∈ child.source :=
    child.witness_mem_source
  have href : reference ∈ selector :=
    (selectorLine selector hmeasurable hvalid hselector
      referenceParameter.1).property
  have hsourcePos : ∀ z ∈ child.source,
      0 < direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4) := by
    intro z hz
    exact northChain.toNorthChain.source_direction_pos (n + 1) z hz
  have hrefPos : 0 < direction reference (3 : Fin 4) :=
    hsourcePos referenceParameter hrefParameter
  have hfirst : ∀ z ∈ child.source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            (child.center (3 : Fin 4)) -
        northGraphEvaluation reference (child.center (3 : Fin 4))‖ ≤
          6 * child.radius := by
    intro z hz
    exact le_of_lt
      (northChain.toNorthChain.source_pair_common_probe
        (n + 1) z referenceParameter hz hrefParameter)
  have hsecond : ∀ z ∈ child.source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1) t -
        northGraphEvaluation reference t‖ ≤ 2 * E := by
    intro z hz
    let u := northGraphEvaluation
      (selectorLine selector hmeasurable hvalid hselector z.1) t
    let v := northGraphEvaluation reference t
    have hu : ‖u - outerCenter‖ ≤ E := by
      simpa [u] using hreturn z hz
    have hv : ‖v - outerCenter‖ ≤ E := by
      simpa [v, reference, referenceParameter] using
        hreturn referenceParameter hrefParameter
    calc
      ‖u - v‖ = ‖(u - outerCenter) + (outerCenter - v)‖ := by
        congr 1 <;> abel
      _ ≤ ‖u - outerCenter‖ + ‖outerCenter - v‖ := norm_add_le _ _
      _ = ‖u - outerCenter‖ + ‖v - outerCenter‖ := by
        rw [norm_sub_rev outerCenter v]
      _ ≤ E + E := add_le_add hu hv
      _ = 2 * E := by ring
  have hmeasureUpper :
      (frontParameterProbability : Measure FrontParameterSpace) child.source ≤
        ENNReal.ofReal (2 * child.radius) *
          (metricSphereCapConstant *
            (ENNReal.ofReal
              (2 * ((6 * child.radius + 2 * E) / g) + eta)) ^ 3) := by
    apply frontParameterProbability_source_le_of_two_probe_and_ball
      selector hmeasurable hvalid hselector child.source reference href
      hsourcePos hrefPos (child.center (3 : Fin 4)) t
      (6 * child.radius) (2 * E) g eta hfirst hsecond
      child.center child.radius child.source_subset_ball
    · exact mul_nonneg (by norm_num) child.radius_pos.le
    · exact mul_nonneg (by norm_num) hE
    · exact hg
    · simpa [abs_sub_comm] using hsep
    · exact heta
    · simpa [child] using hradiusOne
    · exact child.radius_pos.le
  have hmassLower := (northChain.chain.quantitative_child n).2
  have hmeasureLeLower :
      (frontParameterProbability : Measure FrontParameterSpace) child.source ≤
        (frontParameterProbability : Measure FrontParameterSpace)
            (northChain.chain.state n).source *
          (((ENNReal.ofReal ((northChain.chain.state n).radius / 4)).rpow
              (4 - northChain.chain.epsilon))⁻¹ *
            (ENNReal.ofReal child.radius).rpow
              (4 - northChain.chain.epsilon)) := by
    exact hmeasureUpper.trans (by simpa [child] using hbudget)
  exact (not_lt_of_ge hmeasureLeLower) (by simpa [child] using hmassLower)

end StickyKakeya4
