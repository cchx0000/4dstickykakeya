import Theorems.Thm_StickyKakeya4_measured_conditioned_boundary_packet
import Theorems.Thm_StickyKakeya4_packing_piece_two_probe_firewall
import Theorems.Thm_StickyKakeya4_quantitative_return_budget

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- A retained carrier piece lying in the fixed north cap gives full support,
up to null sets, to the corresponding canonical north parameter cap. -/
theorem markedCarrierPieceFrontParameterProbability_compl_contactNorthParameterCap_eq_zero
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {piece : Set (E4 × E4)}
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass : (selectorCarrierProbability selector hmeasurable hvalid
      hselector : Measure (E4 × E4)) piece ≠ 0)
    (hpieceNorth : ∀ q ∈ piece,
      dist q.1 contactNorthPole < (1 / 4 : ℝ)) :
    (markedCarrierPieceFrontParameterProbability selector hmeasurable
      hvalid hselector piece : Measure FrontParameterSpace)
        contactNorthParameterCapᶜ = 0 := by
  let cell : Set MarkedLine :=
    lineDirectionBall contactNorthPole (1 / 4)
  have hcap : contactNorthParameterCap =
      frontParameterLineCell selector hmeasurable hvalid hselector cell := by
    ext z
    change dist (z.1 : E4) contactNorthPole < (1 / 4 : ℝ) ↔
      dist
        (direction
          (selectorLine selector hmeasurable hvalid hselector z.1))
        contactNorthPole < (1 / 4 : ℝ)
    rw [direction_selectorLine selector hmeasurable hvalid hselector z.1]
  have hlineSupport :
      (markedCarrierPieceLineProbability selector hmeasurable hvalid
        hselector piece : Measure MarkedLine) cellᶜ = 0 := by
    apply measure_mono_null _
      (markedCarrierPieceLineProbability_apply_compl_eq_zero
        selector hmeasurable hvalid hselector piece hpieceMeasurable
          hpieceCarrier hpieceMass)
    intro line hline hlinePiece
    apply hline
    exact hpieceNorth (direction line, offset line) hlinePiece.2
  rw [hcap]
  change
    (markedCarrierPieceFrontParameterProbability selector hmeasurable
      hvalid hselector piece : Measure FrontParameterSpace)
      ((frontParameterSelectedLine selector hmeasurable hvalid hselector ⁻¹'
        cell)ᶜ) = 0
  rw [← preimage_compl]
  calc
    (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure FrontParameterSpace)
        (frontParameterSelectedLine selector hmeasurable hvalid hselector ⁻¹'
          cellᶜ) =
      (markedCarrierPieceLineProbability selector hmeasurable hvalid
        hselector piece : Measure MarkedLine) cellᶜ := by
      simpa only [frontParameterLineCell] using
        (markedCarrierPieceFrontParameterProbability_frontParameterLineCell
          selector hmeasurable hvalid hselector piece
            (measurableSet_lineDirectionBall contactNorthPole (1 / 4)).compl)
    _ = 0 := hlineSupport

theorem markedCarrierPieceFrontParameterProbability_contactNorthParameterCap_pos
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {piece : Set (E4 × E4)}
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass : (selectorCarrierProbability selector hmeasurable hvalid
      hselector : Measure (E4 × E4)) piece ≠ 0)
    (hpieceNorth : ∀ q ∈ piece,
      dist q.1 contactNorthPole < (1 / 4 : ℝ)) :
    0 < (markedCarrierPieceFrontParameterProbability selector hmeasurable
      hvalid hselector piece : Measure FrontParameterSpace)
        contactNorthParameterCap := by
  let nu : Measure FrontParameterSpace :=
    markedCarrierPieceFrontParameterProbability selector hmeasurable
      hvalid hselector piece
  have hcompl : nu contactNorthParameterCapᶜ = 0 :=
    markedCarrierPieceFrontParameterProbability_compl_contactNorthParameterCap_eq_zero
      hpieceMeasurable hpieceCarrier hpieceMass hpieceNorth
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hunivLe : nu Set.univ ≤
      nu contactNorthParameterCap + nu contactNorthParameterCapᶜ := by
    simpa only [union_compl_self] using
      (measure_union_le contactNorthParameterCap contactNorthParameterCapᶜ
        (μ := nu))
  rw [hzero, hcompl, zero_add] at hunivLe
  have hunivZero : nu Set.univ = 0 := le_zero_iff.mp hunivLe
  letI : IsProbabilityMeasure nu := by infer_instance
  simpa using hunivZero

/-- The coherent boundary can be initialized on the actual packing-piece law.
It returns one fixed exponent, its source-hereditary oracle, and a positive
north packet all measured by that same law. -/
theorem coherentBoundary_has_measured_packingPiece_north_packet
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    {piece : Set (E4 × E4)}
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass : (selectorCarrierProbability selector hmeasurable hvalid
      hselector : Measure (E4 × E4)) piece ≠ 0)
    (hpieceNorth : ∀ q ∈ piece,
      dist q.1 contactNorthPole < (1 / 4 : ℝ)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
      (∀ (source : Set FrontParameterSpace),
        MeasurableSet source →
        0 < (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace) source →
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          ∃ (x : E4) (r : ℝ),
            0 < r ∧ r < rho ∧
            (markedCarrierPieceFrontParameterProbability selector hmeasurable
                hvalid hselector piece : Measure FrontParameterSpace) source *
                (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
                  (ENNReal.ofReal r).rpow (4 - epsilon)) <
              (markedCarrierPieceFrontParameterProbability selector hmeasurable
                hvalid hselector piece : Measure FrontParameterSpace)
                (source ∩
                  (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
                    Metric.ball x r)) ∧
      ∃ parent : MeasuredConditionedBoundaryPacketState
          (markedCarrierPieceFrontParameterProbability selector hmeasurable
            hvalid hselector piece : Measure FrontParameterSpace)
          selector hmeasurable hvalid hselector,
        parent.source ⊆ contactNorthParameterCap := by
  let nu : Measure FrontParameterSpace :=
    markedCarrierPieceFrontParameterProbability selector hmeasurable
      hvalid hselector piece
  have hnuProbability : IsProbabilityMeasure nu := by infer_instance
  obtain ⟨epsilon, hepsilon, hepsilonFour, horacle⟩ :=
    coherentBoundary_conditioned_packet_extension_with_uniform_mass_for_measure
      selector hmeasurable hvalid hselector hboundary nu hnuProbability
  have hnorthPos : 0 < nu contactNorthParameterCap :=
    markedCarrierPieceFrontParameterProbability_contactNorthParameterCap_pos
      hpieceMeasurable hpieceCarrier hpieceMass hpieceNorth
  obtain ⟨x, r, hr, hrOne, hmass⟩ :=
    horacle contactNorthParameterCap measurableSet_contactNorthParameterCap
      hnorthPos 1 (by norm_num) (by norm_num)
  let f : FrontParameterSpace → E4 :=
    frontParametrization selector hmeasurable hvalid hselector
  let source : Set FrontParameterSpace :=
    contactNorthParameterCap ∩ f ⁻¹' Metric.ball x r
  have hsourceMeasurable : MeasurableSet source :=
    measurableSet_contactNorthParameterCap.inter
      ((measurable_frontParametrization selector hmeasurable hvalid hselector)
        Metric.isOpen_ball.measurableSet)
  have hsourcePos : 0 < nu source := by
    exact (bot_le : 0 ≤ nu contactNorthParameterCap *
      (((ENNReal.ofReal 1).rpow (4 - epsilon))⁻¹ *
        (ENNReal.ofReal r).rpow (4 - epsilon))).trans_lt
          (by simpa [source, f] using hmass)
  let parent : MeasuredConditionedBoundaryPacketState nu selector
      hmeasurable hvalid hselector :=
    { source := source
      center := x
      radius := r
      source_measurable := hsourceMeasurable
      source_pos := hsourcePos
      source_subset_ball := by intro z hz; exact hz.2
      radius_pos := hr
      radius_le_one := le_of_lt hrOne }
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_, parent, ?_⟩
  · simpa [nu] using horacle
  · intro z hz
    exact hz.1

/-- For the actual packing-piece probability, a retained child whose relative
failed-Frostman mass pays the full cap--fibre cost cannot admit a second common
probe at a separated height. -/
theorem no_separated_return_of_packingPiece_relative_mass
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {piece : Set (E4 × E4)}
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass : (selectorCarrierProbability selector hmeasurable hvalid
      hselector : Measure (E4 × E4)) piece ≠ 0)
    (parent child : MeasuredConditionedBoundaryPacketState
      (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure FrontParameterSpace)
      selector hmeasurable hvalid hselector)
    (hchildNorth : child.source ⊆ contactNorthParameterCap)
    (epsilon rho t g E eta : ℝ) (outerCenter : E3)
    (hmassLower :
      (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace) parent.source *
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal child.radius).rpow (4 - epsilon)) <
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace) child.source)
    (hreturn : ∀ z ∈ child.source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1) t -
        outerCenter‖ ≤ E)
    (hE : 0 ≤ E) (hg : 0 < g)
    (hsep : g ≤ |t - child.center (3 : Fin 4)|)
    (heta : 0 < eta)
    (hradiusOne :
      2 * ((6 * child.radius + 2 * E) / g) + eta ≤ 1)
    (hbudget :
      ENNReal.ofReal (2 * child.radius) *
          (carrierPieceDirectionCapConstant selector hmeasurable hvalid
            hselector piece *
            (ENNReal.ofReal
              (2 * ((6 * child.radius + 2 * E) / g) + eta)) ^ 3) ≤
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
            hvalid hselector piece : Measure FrontParameterSpace) parent.source *
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal child.radius).rpow (4 - epsilon))) :
    False := by
  obtain ⟨referenceParameter, hrefParameter⟩ := child.source_nonempty
  let reference : MarkedLine :=
    selectorLine selector hmeasurable hvalid hselector referenceParameter.1
  have href : reference ∈ selector :=
    (selectorLine selector hmeasurable hvalid hselector
      referenceParameter.1).property
  have hsourcePos : ∀ z ∈ child.source,
      0 < direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4) := by
    intro z hz
    have hhalf : (1 / 2 : ℝ) ≤ direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4) := by
      rw [direction_selectorLine selector hmeasurable hvalid hselector z.1]
      exact contactNorthParameterCap_direction_ge_half z (hchildNorth hz)
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le hhalf
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
      (child.source_pair_common_probe_of_north hchildNorth
        z referenceParameter hz hrefParameter)
  have hsecond : ∀ z ∈ child.source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1) t -
        northGraphEvaluation reference t‖ ≤ 2 * E := by
    intro z hz
    let u := northGraphEvaluation
      (selectorLine selector hmeasurable hvalid hselector z.1) t
    let v := northGraphEvaluation reference t
    have hu : ‖u - outerCenter‖ ≤ E := by simpa [u] using hreturn z hz
    have hv : ‖v - outerCenter‖ ≤ E := by
      simpa [v, reference] using hreturn referenceParameter hrefParameter
    calc
      ‖u - v‖ = ‖(u - outerCenter) + (outerCenter - v)‖ := by
        congr 1 <;> abel
      _ ≤ ‖u - outerCenter‖ + ‖outerCenter - v‖ := norm_add_le _ _
      _ = ‖u - outerCenter‖ + ‖v - outerCenter‖ := by
        rw [norm_sub_rev outerCenter v]
      _ ≤ E + E := add_le_add hu hv
      _ = 2 * E := by ring
  have hmeasureUpper :
      (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace) child.source ≤
        ENNReal.ofReal (2 * child.radius) *
          (carrierPieceDirectionCapConstant selector hmeasurable hvalid
            hselector piece *
            (ENNReal.ofReal
              (2 * ((6 * child.radius + 2 * E) / g) + eta)) ^ 3) := by
    apply
      markedCarrierPieceFrontParameterProbability_source_le_of_two_probe_and_ball
        selector hmeasurable hvalid hselector piece hpieceMeasurable
          hpieceCarrier hpieceMass child.source reference href hsourcePos hrefPos
          (child.center (3 : Fin 4)) t (6 * child.radius) (2 * E) g eta
          hfirst hsecond child.center child.radius child.source_subset_ball
    · exact mul_nonneg (by norm_num) child.radius_pos.le
    · exact mul_nonneg (by norm_num) hE
    · exact hg
    · simpa [abs_sub_comm] using hsep
    · exact heta
    · exact hradiusOne
    · exact child.radius_pos.le
  exact (not_lt_of_ge (hmeasureUpper.trans hbudget)) hmassLower

/-- The packing-piece failed-Frostman oracle chooses an affordable retained
north child before any second return is tested.  Consequently every return
whose error is linear in the child radius must remain within the prescribed
height gap. -/
theorem MeasuredConditionedBoundaryPacketState.exists_packingPiece_budget_adapted_north_child
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {piece : Set (E4 × E4)}
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass : (selectorCarrierProbability selector hmeasurable hvalid
      hselector : Measure (E4 × E4)) piece ≠ 0)
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonFour : epsilon < 4)
    (horacle : ∀ (source : Set FrontParameterSpace),
      MeasurableSet source →
      0 < (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure FrontParameterSpace) source →
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        ∃ (x : E4) (r : ℝ),
          0 < r ∧ r < rho ∧
          (markedCarrierPieceFrontParameterProbability selector hmeasurable
              hvalid hselector piece : Measure FrontParameterSpace) source *
              (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
                (ENNReal.ofReal r).rpow (4 - epsilon)) <
            (markedCarrierPieceFrontParameterProbability selector hmeasurable
              hvalid hselector piece : Measure FrontParameterSpace)
              (source ∩
                (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
                  Metric.ball x r))
    (parent : MeasuredConditionedBoundaryPacketState
      (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure FrontParameterSpace)
      selector hmeasurable hvalid hselector)
    (hparentNorth : parent.source ⊆ contactNorthParameterCap)
    (g K : ℝ) (hg : 0 < g) (hK : 0 ≤ K) :
    ∃ (rho : ℝ) (child : MeasuredConditionedBoundaryPacketState
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace)
        selector hmeasurable hvalid hselector),
      0 < rho ∧ rho ≤ parent.radius / 4 ∧ rho ≤ 1 ∧
      IsMeasuredConditionedBoundaryPacketChild parent child ∧
      child.radius < rho ∧
      (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace) parent.source *
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal child.radius).rpow (4 - epsilon)) <
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace) child.source ∧
      child.source ⊆ contactNorthParameterCap ∧
      ∀ (t E : ℝ) (outerCenter : E3),
        0 ≤ E → E ≤ K * child.radius →
        g ≤ |t - child.center (3 : Fin 4)| →
        ¬ (∀ z ∈ child.source,
          ‖northGraphEvaluation
              (selectorLine selector hmeasurable hvalid hselector z.1) t -
            outerCenter‖ ≤ E) := by
  let L : ℝ := 2 * ((6 + 2 * K) / g) + 1
  have hLpos : 0 < L := by
    dsimp [L]
    positivity
  let Cdir : ENNReal :=
    carrierPieceDirectionCapConstant selector hmeasurable hvalid hselector piece
  let cost : ENNReal :=
    ENNReal.ofReal 2 * Cdir * (ENNReal.ofReal L) ^ 3
  have hcostTop : cost ≠ ⊤ := by
    dsimp [cost, Cdir]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (carrierPieceDirectionCapConstant_ne_top selector hmeasurable hvalid
          hselector piece))
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hmassTop :
      (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure FrontParameterSpace) parent.source ≠
          ⊤ := measure_ne_top _ _
  have hchoiceRadius : 0 < min (parent.radius / 4) (1 / L) := by
    rw [lt_min_iff]
    exact ⟨by linarith [parent.radius_pos], one_div_pos.mpr hLpos⟩
  obtain ⟨rho, hrho, hrhoChoice, hrhoOne, hscaleBudget⟩ :=
    exists_scale_fourth_power_le
      ((markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure FrontParameterSpace) parent.source)
      cost parent.source_pos hmassTop hcostTop
      (min (parent.radius / 4) (1 / L)) hchoiceRadius
  have hrhoQuarter : rho ≤ parent.radius / 4 :=
    hrhoChoice.trans (min_le_left _ _)
  have hrhoInvL : rho ≤ 1 / L :=
    hrhoChoice.trans (min_le_right _ _)
  obtain ⟨child, hchild, hchildRho, hmassLower⟩ :=
    parent.exists_quantitative_child_below hepsilon hepsilonFour horacle
      rho hrho hrhoQuarter hrhoOne
  have hchildNorth : child.source ⊆ contactNorthParameterCap := by
    intro z hz
    rw [hchild.1] at hz
    exact hparentNorth hz.1
  refine ⟨rho, child, hrho, hrhoQuarter, hrhoOne, hchild, hchildRho,
    hmassLower, hchildNorth, ?_⟩
  intro t E outerCenter hE hEK hsep hreturn
  have hnumerator :
      6 * child.radius + 2 * E ≤ (6 + 2 * K) * child.radius := by
    nlinarith [child.radius_pos]
  have hquotient :
      (6 * child.radius + 2 * E) / g ≤
        ((6 + 2 * K) * child.radius) / g :=
    (div_le_div_iff_of_pos_right hg).2 hnumerator
  have hcapLe :
      2 * ((6 * child.radius + 2 * E) / g) + child.radius ≤
        L * child.radius := by
    calc
      2 * ((6 * child.radius + 2 * E) / g) + child.radius ≤
          2 * (((6 + 2 * K) * child.radius) / g) + child.radius := by
        gcongr
      _ = L * child.radius := by
        dsimp [L]
        field_simp [hg.ne']
  have hchildInvL : child.radius < 1 / L :=
    hchildRho.trans_le hrhoInvL
  have hLchild : L * child.radius < 1 := by
    have hmul := mul_lt_mul_of_pos_left hchildInvL hLpos
    simpa [hLpos.ne'] using hmul
  have hradiusOne :
      2 * ((6 * child.radius + 2 * E) / g) + child.radius ≤ 1 :=
    hcapLe.trans hLchild.le
  have hOfRealCap :
      ENNReal.ofReal
          (2 * ((6 * child.radius + 2 * E) / g) + child.radius) ≤
        ENNReal.ofReal L * ENNReal.ofReal child.radius := by
    calc
      ENNReal.ofReal
          (2 * ((6 * child.radius + 2 * E) / g) + child.radius) ≤
          ENNReal.ofReal (L * child.radius) :=
        ENNReal.ofReal_le_ofReal hcapLe
      _ = ENNReal.ofReal L * ENNReal.ofReal child.radius := by
        rw [ENNReal.ofReal_mul hLpos.le]
  have hgeometricCost :
      ENNReal.ofReal (2 * child.radius) *
          (Cdir *
            (ENNReal.ofReal
              (2 * ((6 * child.radius + 2 * E) / g) + child.radius)) ^ 3) ≤
        cost * (ENNReal.ofReal child.radius) ^ 4 := by
    calc
      ENNReal.ofReal (2 * child.radius) *
          (Cdir *
            (ENNReal.ofReal
              (2 * ((6 * child.radius + 2 * E) / g) + child.radius)) ^ 3) =
          (ENNReal.ofReal 2 * ENNReal.ofReal child.radius) *
            (Cdir *
              (ENNReal.ofReal
                (2 * ((6 * child.radius + 2 * E) / g) + child.radius)) ^ 3) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (ENNReal.ofReal 2 * ENNReal.ofReal child.radius) *
            (Cdir *
              (ENNReal.ofReal L * ENNReal.ofReal child.radius) ^ 3) := by
        gcongr
      _ = cost * (ENNReal.ofReal child.radius) ^ 4 := by
        dsimp [cost]
        ring
  have hrelativeBudget :
      cost * (ENNReal.ofReal child.radius) ^ 4 ≤
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
            hvalid hselector piece : Measure FrontParameterSpace) parent.source *
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal child.radius).rpow (4 - epsilon)) :=
    fourth_power_le_relative_frostman_budget
      ((markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure FrontParameterSpace) parent.source)
      cost epsilon child.radius rho hepsilon hepsilonFour child.radius_pos
        hrho hchildRho.le hscaleBudget
  exact no_separated_return_of_packingPiece_relative_mass
    hpieceMeasurable hpieceCarrier hpieceMass parent child hchildNorth
      epsilon rho t g E child.radius outerCenter hmassLower hreturn hE hg hsep
      child.radius_pos hradiusOne (hgeometricCost.trans hrelativeBudget)

/-- Direct boundary output for the retained packing piece: one fixed failed
exponent, a literal parent/child source restriction, the exact relative mass
gain, and the internally paid exclusion of every separated common return. -/
theorem coherentBoundary_produces_packingPiece_budget_adapted_north_child
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    {piece : Set (E4 × E4)}
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass : (selectorCarrierProbability selector hmeasurable hvalid
      hselector : Measure (E4 × E4)) piece ≠ 0)
    (hpieceNorth : ∀ q ∈ piece,
      dist q.1 contactNorthPole < (1 / 4 : ℝ))
    (g K : ℝ) (hg : 0 < g) (hK : 0 ≤ K) :
    ∃ (epsilon : ℝ)
      (parent child : MeasuredConditionedBoundaryPacketState
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace)
        selector hmeasurable hvalid hselector)
      (rho : ℝ),
      0 < epsilon ∧ epsilon < 4 ∧
      parent.source ⊆ contactNorthParameterCap ∧
      0 < rho ∧ rho ≤ parent.radius / 4 ∧ rho ≤ 1 ∧
      IsMeasuredConditionedBoundaryPacketChild parent child ∧
      child.radius < rho ∧
      (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace) parent.source *
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal child.radius).rpow (4 - epsilon)) <
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace) child.source ∧
      child.source ⊆ contactNorthParameterCap ∧
      ∀ (t E : ℝ) (outerCenter : E3),
        0 ≤ E → E ≤ K * child.radius →
        g ≤ |t - child.center (3 : Fin 4)| →
        ¬ (∀ z ∈ child.source,
          ‖northGraphEvaluation
              (selectorLine selector hmeasurable hvalid hselector z.1) t -
            outerCenter‖ ≤ E) := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, horacle, parent,
      hparentNorth⟩ :=
    coherentBoundary_has_measured_packingPiece_north_packet hboundary
      hpieceMeasurable hpieceCarrier hpieceMass hpieceNorth
  obtain ⟨rho, child, hrho, hrhoQuarter, hrhoOne, hchild, hchildRho,
      hmassLower, hchildNorth, hnoReturn⟩ :=
    parent.exists_packingPiece_budget_adapted_north_child
      hpieceMeasurable hpieceCarrier hpieceMass hepsilon hepsilonFour
        horacle hparentNorth g K hg hK
  exact ⟨epsilon, parent, child, rho, hepsilon, hepsilonFour,
    hparentNorth, hrho, hrhoQuarter, hrhoOne, hchild, hchildRho,
    hmassLower, hchildNorth, hnoReturn⟩

end StickyKakeya4
