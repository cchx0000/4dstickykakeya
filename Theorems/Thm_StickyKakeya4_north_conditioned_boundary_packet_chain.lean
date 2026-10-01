import Theorems.Thm_StickyKakeya4_front_direction_cap_firewall

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace StickyKakeya4

/-- Fixed north pole used by the contact chart, defined independently of the
Wang--Zakharov files. -/
def contactNorthPole : E4 := EuclideanSpace.single (3 : Fin 4) 1

theorem norm_contactNorthPole : ‖contactNorthPole‖ = 1 := by
  simp [contactNorthPole]

def contactNorthDirection : {theta : E4 // ‖theta‖ = 1} :=
  ⟨contactNorthPole, norm_contactNorthPole⟩

/-- Canonical direction--fibre parameters in a fixed positive north cap. -/
def contactNorthParameterCap : Set FrontParameterSpace :=
  frontDirectionCap contactNorthDirection (1 / 4)

theorem measurableSet_contactNorthParameterCap :
    MeasurableSet contactNorthParameterCap :=
  measurableSet_frontDirectionCap contactNorthDirection (1 / 4)

theorem frontParameterProbability_contactNorthParameterCap_pos :
    0 < (frontParameterProbability : Measure FrontParameterSpace)
      contactNorthParameterCap := by
  rw [contactNorthParameterCap,
    frontParameterProbability_frontDirectionCap]
  exact pos_iff_ne_zero.mpr
    (normSphereProbability_ball_ne_zero contactNorthDirection (by norm_num))

/-- Every direction in the fixed contact north cap has fourth coordinate at
least one half, hence lies uniformly inside the positive graph chart. -/
theorem contactNorthParameterCap_direction_ge_half
    (z : FrontParameterSpace) (hz : z ∈ contactNorthParameterCap) :
    (1 / 2 : ℝ) ≤ (z.1 : E4) (3 : Fin 4) := by
  have hball : dist (z.1 : E4) contactNorthPole < (1 / 4 : ℝ) := hz
  have hnorm : ‖(z.1 : E4) - contactNorthPole‖ < (1 / 4 : ℝ) := by
    simpa [dist_eq_norm] using hball
  have hinner := abs_real_inner_le_norm contactNorthPole
    ((z.1 : E4) - contactNorthPole)
  rw [norm_contactNorthPole, one_mul] at hinner
  have hcoordinate :
      |(z.1 : E4) (3 : Fin 4) - 1| ≤
        ‖(z.1 : E4) - contactNorthPole‖ := by
    simpa [contactNorthPole, EuclideanSpace.inner_single_left] using hinner
  have habs : |(z.1 : E4) (3 : Fin 4) - 1| < (1 / 4 : ℝ) :=
    hcoordinate.trans_lt hnorm
  have hlower := (abs_lt.mp habs).1
  linarith

/-- A conditioned packet chain whose every retained source remains inside the
same fixed positive north chart. -/
structure NorthConditionedBoundaryPacketChain
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) where
  chain : ConditionedBoundaryPacketChain selector hmeasurable hvalid hselector
  source_north : ∀ n,
    (chain.state n).source ⊆ contactNorthParameterCap

/-- The coherent boundary may be initialized on the positive-mass north cap.
Every later source is a literal restriction of the preceding source, so the
uniform positive chart bound survives through the entire chain. -/
theorem coherentBoundary_has_north_conditioned_packet_chain
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    Nonempty (NorthConditionedBoundaryPacketChain selector hmeasurable
      hvalid hselector) := by
  let f : FrontParameterSpace → E4 :=
    frontParametrization selector hmeasurable hvalid hselector
  obtain ⟨x, r, hr, hrOne, hmass⟩ :=
    coherentBoundary_conditioned_packet_extension selector hmeasurable
      hvalid hselector hboundary contactNorthParameterCap
      measurableSet_contactNorthParameterCap
      frontParameterProbability_contactNorthParameterCap_pos
      1 (by norm_num) (by norm_num)
  let source : Set FrontParameterSpace :=
    contactNorthParameterCap ∩ f ⁻¹' Metric.ball x r
  let initial : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector :=
    { source := source
      center := x
      radius := r
      source_measurable :=
        measurableSet_contactNorthParameterCap.inter
          ((measurable_frontParametrization selector hmeasurable hvalid
            hselector) Metric.isOpen_ball.measurableSet)
      source_pos := by simpa [source, f] using hmass
      source_subset_ball := by intro z hz; exact hz.2
      radius_pos := hr
      radius_le_one := le_of_lt hrOne }
  let state : ℕ → ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector := fun n ↦
    (conditionedBoundaryPacketNext hboundary)^[n] initial
  let chain : ConditionedBoundaryPacketChain selector hmeasurable
      hvalid hselector :=
    { state := state
      child := by
        intro n
        change IsConditionedBoundaryPacketChild
          ((conditionedBoundaryPacketNext hboundary)^[n] initial)
          ((conditionedBoundaryPacketNext hboundary)^[n + 1] initial)
        rw [Function.iterate_succ_apply']
        exact conditionedBoundaryPacketNext_isChild hboundary _ }
  refine ⟨⟨chain, ?_⟩⟩
  intro n
  induction n with
  | zero =>
      intro z hz
      exact hz.1
  | succ n ih =>
      exact (chain.source_succ_subset n).trans ih

/-- Every actual selected line represented in a north conditioned source has
strictly positive fourth direction coordinate. -/
theorem NorthConditionedBoundaryPacketChain.source_direction_pos
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (northChain : NorthConditionedBoundaryPacketChain selector hmeasurable
      hvalid hselector) (n : ℕ) (z : FrontParameterSpace)
    (hz : z ∈ (northChain.chain.state n).source) :
    0 < direction
      (selectorLine selector hmeasurable hvalid hselector z.1)
        (3 : Fin 4) := by
  rw [direction_selectorLine selector hmeasurable hvalid hselector z.1]
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (contactNorthParameterCap_direction_ge_half z
      (northChain.source_north n hz))

end StickyKakeya4
