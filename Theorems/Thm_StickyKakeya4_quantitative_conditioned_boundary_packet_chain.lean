import Theorems.Thm_StickyKakeya4_conditioned_boundary_packet_chain
import Theorems.Thm_StickyKakeya4_conditioned_boundary_packet_mass

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- A conditioned child with the exact relative mass gain supplied by the
fixed failed-Frostman exponent.  The geometric child relation and the mass
ledger are kept in one predicate so that dependent choice cannot silently
change the exponent between generations. -/
def IsQuantitativeConditionedBoundaryPacketChild
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (epsilon : ℝ)
    (parent child : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector) : Prop :=
  IsConditionedBoundaryPacketChild parent child ∧
  (frontParameterProbability : Measure FrontParameterSpace) parent.source *
      (((ENNReal.ofReal (parent.radius / 4)).rpow (4 - epsilon))⁻¹ *
        (ENNReal.ofReal child.radius).rpow (4 - epsilon)) <
    (frontParameterProbability : Measure FrontParameterSpace) child.source

/-- The quantitative child may be requested at any positive comparison scale
`rho` below the geometric quarter-scale.  Keeping `rho` explicit is essential:
it lets the later four-dimensional collision budget choose a genuinely
affordable scale before the failed-Frostman oracle chooses the child. -/
theorem ConditionedBoundaryPacketState.exists_quantitative_child_below
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonFour : epsilon < 4)
    (horacle : ∀ (source : Set FrontParameterSpace),
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
                  Metric.ball x r))
    (parent : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector)
    (rho : ℝ) (hrho : 0 < rho) (hrhoQuarter : rho ≤ parent.radius / 4)
    (hrhoOne : rho ≤ 1) :
    ∃ child : ConditionedBoundaryPacketState selector hmeasurable
        hvalid hselector,
      IsConditionedBoundaryPacketChild parent child ∧
      child.radius < rho ∧
      (frontParameterProbability : Measure FrontParameterSpace) parent.source *
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal child.radius).rpow (4 - epsilon)) <
        (frontParameterProbability : Measure FrontParameterSpace) child.source := by
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
  have hchildPos :
      0 < (frontParameterProbability : Measure FrontParameterSpace)
        childSource := by
    exact (bot_le : 0 ≤
      (frontParameterProbability : Measure FrontParameterSpace) parent.source *
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
  let child : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector :=
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

/-- The uniform conditioned packet oracle produces a quantitative child and
also gives the center-motion estimate required for cross-scale coherence. -/
theorem ConditionedBoundaryPacketState.exists_quantitative_child
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonFour : epsilon < 4)
    (horacle : ∀ (source : Set FrontParameterSpace),
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
                  Metric.ball x r))
    (parent : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector) :
    ∃ child : ConditionedBoundaryPacketState selector hmeasurable
        hvalid hselector,
      IsQuantitativeConditionedBoundaryPacketChild epsilon parent child := by
  have hrho : 0 < parent.radius / 4 := by linarith [parent.radius_pos]
  have hrhoOne : parent.radius / 4 ≤ 1 := by
    have hquarter : parent.radius / 4 ≤ (1 : ℝ) / 4 :=
      (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2
        parent.radius_le_one
    exact hquarter.trans (by norm_num)
  obtain ⟨x, r, hr, hrSmall, hmass⟩ :=
    horacle parent.source parent.source_measurable parent.source_pos
      (parent.radius / 4) hrho hrhoOne
  let f : FrontParameterSpace → E4 :=
    frontParametrization selector hmeasurable hvalid hselector
  let childSource : Set FrontParameterSpace :=
    parent.source ∩ f ⁻¹' Metric.ball x r
  have hchildMeasurable : MeasurableSet childSource := by
    exact parent.source_measurable.inter
      ((measurable_frontParametrization selector hmeasurable hvalid hselector)
        Metric.isOpen_ball.measurableSet)
  have hchildPos :
      0 < (frontParameterProbability : Measure FrontParameterSpace)
        childSource := by
    exact (bot_le : 0 ≤
      (frontParameterProbability : Measure FrontParameterSpace) parent.source *
        (((ENNReal.ofReal (parent.radius / 4)).rpow (4 - epsilon))⁻¹ *
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
  have hrOne : r ≤ 1 :=
    (le_of_lt hrSmall).trans hrhoOne
  let child : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector :=
    { source := childSource
      center := x
      radius := r
      source_measurable := hchildMeasurable
      source_pos := hchildPos
      source_subset_ball := by intro w hw; exact hw.2
      radius_pos := hr
      radius_le_one := hrOne }
  refine ⟨child, ?_, ?_⟩
  · exact ⟨rfl, hrSmall, by simpa [child] using hcenter⟩
  · simpa [child, childSource, f] using hmass

/-- A coherent nested packet history with one fixed failed exponent and its
exact source-mass inequality recorded at every generation. -/
structure QuantitativeConditionedBoundaryPacketChain
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_four : epsilon < 4
  state : ℕ → ConditionedBoundaryPacketState selector hmeasurable
    hvalid hselector
  quantitative_child : ∀ n,
    IsQuantitativeConditionedBoundaryPacketChild epsilon
      (state n) (state (n + 1))

def QuantitativeConditionedBoundaryPacketChain.toChain
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (chain : QuantitativeConditionedBoundaryPacketChain selector hmeasurable
      hvalid hselector) :
    ConditionedBoundaryPacketChain selector hmeasurable hvalid hselector where
  state := chain.state
  child := fun n ↦ (chain.quantitative_child n).1

/-- Choice of one quantitative child; this packages the already-proved serial
relation and is not used as a mathematical definition of the packet geometry. -/
noncomputable def quantitativeConditionedBoundaryPacketNext
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonFour : epsilon < 4)
    (horacle : ∀ (source : Set FrontParameterSpace),
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
                  Metric.ball x r))
    (parent : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector) :
    ConditionedBoundaryPacketState selector hmeasurable hvalid hselector :=
  Classical.choose
    (parent.exists_quantitative_child hepsilon hepsilonFour horacle)

theorem quantitativeConditionedBoundaryPacketNext_spec
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonFour : epsilon < 4)
    (horacle : ∀ (source : Set FrontParameterSpace),
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
                  Metric.ball x r))
    (parent : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector) :
    IsQuantitativeConditionedBoundaryPacketChild epsilon parent
      (quantitativeConditionedBoundaryPacketNext hepsilon hepsilonFour
        horacle parent) :=
  Classical.choose_spec
    (parent.exists_quantitative_child hepsilon hepsilonFour horacle)

/-- Package the quantitative child relation from any prescribed positive
initial packet.  This is the reusable dependent-choice step needed when the
initial source has already been restricted to a fixed contact chart. -/
theorem quantitativeConditionedBoundaryPacketChain_of_initial
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonFour : epsilon < 4)
    (horacle : ∀ (source : Set FrontParameterSpace),
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
                  Metric.ball x r))
    (initial : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector) :
    Nonempty (QuantitativeConditionedBoundaryPacketChain selector
      hmeasurable hvalid hselector) := by
  let next := quantitativeConditionedBoundaryPacketNext
    hepsilon hepsilonFour horacle
  let state : ℕ → ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector := fun n ↦ next^[n] initial
  refine ⟨⟨epsilon, hepsilon, hepsilonFour, state, ?_⟩⟩
  intro n
  change IsQuantitativeConditionedBoundaryPacketChild epsilon
    (next^[n] initial) (next^[n + 1] initial)
  rw [Function.iterate_succ_apply']
  exact quantitativeConditionedBoundaryPacketNext_spec
    hepsilon hepsilonFour horacle _

/-- Every coherent concentration boundary has a compatible quantitative
packet chain.  In particular, the fixed failed exponent and every relative
mass gain survive all descendant restrictions. -/
theorem coherentBoundary_has_quantitative_conditioned_packet_chain
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    Nonempty (QuantitativeConditionedBoundaryPacketChain selector
      hmeasurable hvalid hselector) := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, horacle⟩ :=
    coherentBoundary_conditioned_packet_extension_with_uniform_mass
      selector hmeasurable hvalid hselector hboundary
  obtain ⟨x, r, hr, hrOne, hmass⟩ :=
    horacle Set.univ MeasurableSet.univ (by simp) 1 (by norm_num) (by norm_num)
  let f : FrontParameterSpace → E4 :=
    frontParametrization selector hmeasurable hvalid hselector
  let source : Set FrontParameterSpace := f ⁻¹' Metric.ball x r
  have hsourceMeasurable : MeasurableSet source :=
    Metric.isOpen_ball.measurableSet.preimage
      (measurable_frontParametrization selector hmeasurable hvalid hselector)
  have hsourcePos :
      0 < (frontParameterProbability : Measure FrontParameterSpace) source := by
    exact (bot_le : 0 ≤
      (frontParameterProbability : Measure FrontParameterSpace) Set.univ *
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
      source_subset_ball := by intro z hz; exact hz
      radius_pos := hr
      radius_le_one := le_of_lt hrOne }
  let next := quantitativeConditionedBoundaryPacketNext
    hepsilon hepsilonFour horacle
  let state : ℕ → ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector := fun n ↦ next^[n] initial
  refine ⟨⟨epsilon, hepsilon, hepsilonFour, state, ?_⟩⟩
  intro n
  change IsQuantitativeConditionedBoundaryPacketChild epsilon
    (next^[n] initial) (next^[n + 1] initial)
  rw [Function.iterate_succ_apply']
  exact quantitativeConditionedBoundaryPacketNext_spec
    hepsilon hepsilonFour horacle _

end StickyKakeya4
