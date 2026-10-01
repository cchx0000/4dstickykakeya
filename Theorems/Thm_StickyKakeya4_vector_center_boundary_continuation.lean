import Theorems.Thm_StickyKakeya4_vector_center_carleson
import Theorems.Thm_StickyKakeya4_law_level_return_budget

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- A positive physical ball for the normalized packing-piece front law is a
literal measured north packet for the same marked direction--fibre law.  The
north cap is intersected into the source rather than inferred pointwise from
an almost-everywhere support statement; its mass is unchanged because the
piece law gives the complement zero mass. -/
theorem markedCarrierPiece_front_ball_excess_has_measured_north_packet
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass : (selectorCarrierProbability selector hmeasurable hvalid
      hselector : Measure (E4 × E4)) piece ≠ 0)
    (hpieceNorth : ∀ q ∈ piece,
      dist q.1 contactNorthPole < (1 / 4 : ℝ))
    (x : E4) (r : ℝ) (threshold : ENNReal)
    (hr : 0 < r) (hrOne : r ≤ 1)
    (hexcess : threshold <
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball x r)) :
    ∃ parent : MeasuredConditionedBoundaryPacketState
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace)
        selector hmeasurable hvalid hselector,
      parent.source ⊆ contactNorthParameterCap ∧
      threshold <
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace)
          parent.source := by
  let nu : Measure FrontParameterSpace :=
    markedCarrierPieceFrontParameterProbability selector hmeasurable
      hvalid hselector piece
  let f : FrontParameterSpace → E4 :=
    frontParametrization selector hmeasurable hvalid hselector
  have hnorth : nu contactNorthParameterCapᶜ = 0 := by
    simpa [nu] using
      (markedCarrierPieceFrontParameterProbability_contactNorthSupport
        hpieceMeasurable hpieceCarrier hpieceMass hpieceNorth)
  have haeNorth : ∀ᵐ z ∂nu, z ∈ contactNorthParameterCap := by
    rw [ae_iff]
    exact hnorth
  have hpreimageMass :
      threshold < nu (f ⁻¹' Metric.ball x r) := by
    calc
      threshold <
          (markedCarrierPieceFrontProbability selector hmeasurable hvalid
            hselector piece : Measure E4) (Metric.ball x r) := hexcess
      _ = Measure.map f nu (Metric.ball x r) := by
        rw [map_frontParametrization_markedCarrierPieceFrontParameterProbability]
      _ = nu (f ⁻¹' Metric.ball x r) := by
        rw [Measure.map_apply
          (measurable_frontParametrization selector hmeasurable hvalid hselector)
          Metric.isOpen_ball.measurableSet]
  let source : Set FrontParameterSpace :=
    contactNorthParameterCap ∩ f ⁻¹' Metric.ball x r
  have hsourceMeasurable : MeasurableSet source := by
    exact measurableSet_contactNorthParameterCap.inter
      ((measurable_frontParametrization selector hmeasurable hvalid hselector)
        Metric.isOpen_ball.measurableSet)
  have hsourceMass : threshold < nu source := by
    dsimp [source]
    rw [Measure.measure_inter_eq_of_ae haeNorth]
    exact hpreimageMass
  have hsourcePos : 0 < nu source :=
    (bot_le : 0 ≤ threshold).trans_lt hsourceMass
  let parent : MeasuredConditionedBoundaryPacketState nu selector
      hmeasurable hvalid hselector :=
    { source := source
      center := x
      radius := r
      source_measurable := hsourceMeasurable
      source_pos := hsourcePos
      source_subset_ball := by intro z hz; exact hz.2
      radius_pos := hr
      radius_le_one := hrOne }
  refine ⟨parent, ?_, ?_⟩
  · intro z hz
    exact hz.1
  · simpa [parent, nu] using hsourceMass

/-- A four-dimensional ball excess for a north-localized packing piece enters
the genuine boundary continuation, not a WZ pruning surrogate.  The same
marked parameter law supplies the parent packet, the quantitative descendant,
the cap--fibre bound, and the exclusion of every separated common return whose
error is at most `K` times the child radius. -/
theorem markedCarrierPiece_front_ball_excess_produces_budget_adapted_child
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass : (selectorCarrierProbability selector hmeasurable hvalid
      hselector : Measure (E4 × E4)) piece ≠ 0)
    (hpieceNorth : ∀ q ∈ piece,
      dist q.1 contactNorthPole < (1 / 4 : ℝ))
    (x : E4) (r : ℝ) (threshold : ENNReal)
    (hr : 0 < r) (hrOne : r ≤ 1)
    (hexcess : threshold <
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball x r))
    (g K : ℝ) (hg : 0 < g) (hK : 0 ≤ K) :
    ∃ (epsilon : ℝ)
      (parent child : MeasuredConditionedBoundaryPacketState
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace)
        selector hmeasurable hvalid hselector)
      (rho : ℝ),
      0 < epsilon ∧ epsilon < 4 ∧
      parent.source ⊆ contactNorthParameterCap ∧
      threshold <
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace) parent.source ∧
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
  let nu : Measure FrontParameterSpace :=
    markedCarrierPieceFrontParameterProbability selector hmeasurable
      hvalid hselector piece
  have hnuProbability : IsProbabilityMeasure nu := by
    dsimp [nu]
    infer_instance
  obtain ⟨parent, hparentNorth, hparentMass⟩ :=
    markedCarrierPiece_front_ball_excess_has_measured_north_packet
      selector hmeasurable hvalid hselector piece hpieceMeasurable
        hpieceCarrier hpieceMass hpieceNorth x r threshold hr hrOne hexcess
  obtain ⟨epsilon, hepsilon, hepsilonFour, horacle⟩ :=
    coherentBoundary_conditioned_packet_extension_with_uniform_mass_for_measure
      selector hmeasurable hvalid hselector hboundary nu hnuProbability
  let Cfront : ENNReal :=
    carrierPieceDirectionCapConstant selector hmeasurable hvalid hselector piece
  have hCfrontTop : Cfront ≠ ⊤ := by
    exact carrierPieceDirectionCapConstant_ne_top
      selector hmeasurable hvalid hselector piece
  have hfront : HasFrontDirectionFibreBound selector hmeasurable hvalid
      hselector nu Cfront := by
    simpa [nu, Cfront] using
      (markedCarrierPieceFrontParameterProbability_hasFrontDirectionFibreBound
        selector hmeasurable hvalid hselector piece hpieceMeasurable
          hpieceCarrier hpieceMass)
  obtain ⟨rho, child, hrho, hrhoQuarter, hrhoOne, hchild,
      hchildRho, hchildMass, hchildNorth, hnoReturn⟩ :=
    parent.exists_budget_adapted_north_child_for_measure
      hnuProbability hCfrontTop hfront hepsilon hepsilonFour horacle
        hparentNorth g K hg hK
  refine ⟨epsilon, parent, child, rho, hepsilon, hepsilonFour,
    hparentNorth, ?_, hrho, hrhoQuarter, hrhoOne, hchild, hchildRho,
    ?_, hchildNorth, hnoReturn⟩
  · simpa [nu] using hparentMass
  · simpa [nu] using hchildMass

/-- The complete local continuation of the moving-vector-centre failure.  A
three-dimensional moving-secant mass excess is first converted into the
correct four-dimensional front-ball excess and then, for the same normalized
marked packing-piece law, into a quantitative child packet excluding every
separated common return in its allowed error budget.  No Wang--Zakharov input
appears in either conversion. -/
theorem moving_secant_rpow_mass_excess_produces_budget_adapted_child
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass : (selectorCarrierProbability selector hmeasurable hvalid
      hselector : Measure (E4 × E4)) piece ≠ 0)
    (hpieceNorth : ∀ q ∈ piece,
      dist q.1 contactNorthPole < (1 / 4 : ℝ))
    (lines : ℕ → Set MarkedLine)
    (hlinesMeasurable : ∀ e, MeasurableSet (lines e))
    (hlinesDisjoint : Pairwise (fun e e' => Disjoint (lines e) (lines e')))
    (firstTime : MarkedLine → ℝ) (firstCenter : MarkedLine → E3)
    (outerTime : ℝ) (outerPoint : E4)
    (Rs R L delta kappa zeta : ℝ) (Q : ENNReal)
    (houterTime : outerPoint (3 : Fin 4) = outerTime)
    (hR : 0 ≤ R) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hscale : Rs + L * R < delta / 2)
    (hkappa : 0 ≤ kappa) (hzeta : zeta ≤ 3)
    (hscaleLower : kappa * R ≤ delta)
    (hchart : ∀ e line,
      line ∈ selectorLinesOverCarrierPiece selector piece →
      line ∈ lines e → direction line (3 : Fin 4) ≠ 0)
    (hfirst : ∀ e line,
      line ∈ selectorLinesOverCarrierPiece selector piece →
      line ∈ lines e →
        ‖northGraphEvaluation line (firstTime line) - firstCenter line‖ ≤ Rs)
    (hslope : ∀ e line,
      line ∈ selectorLinesOverCarrierPiece selector piece →
      line ∈ lines e →
        ‖northGraphSlope line -
          (outerTime - firstTime line)⁻¹ •
            (horizontalProjection outerPoint - firstCenter line)‖ ≤ R)
    (htimeNe : ∀ e line,
      line ∈ selectorLinesOverCarrierPiece selector piece →
      line ∈ lines e → outerTime - firstTime line ≠ 0)
    (hgapUpper : ∀ e line,
      line ∈ selectorLinesOverCarrierPiece selector piece →
      line ∈ lines e → |outerTime - firstTime line| ≤ L)
    (hsegment : ∀ e line,
      line ∈ selectorLinesOverCarrierPiece selector piece →
      line ∈ lines e →
        fixedHeightTime line outerTime - mark line ∈
          Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hexcess : Q * (ENNReal.ofReal R).rpow (3 - zeta) <
      ∑' e, (markedCarrierPieceLineProbability selector hmeasurable
        hvalid hselector piece : Measure MarkedLine) (lines e))
    (g K : ℝ) (hg : 0 < g) (hK : 0 ≤ K) :
    ∃ (epsilon : ℝ)
      (parent child : MeasuredConditionedBoundaryPacketState
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace)
        selector hmeasurable hvalid hselector)
      (rho : ℝ),
      0 < epsilon ∧ epsilon < 4 ∧
      parent.source ⊆ contactNorthParameterCap ∧
      ENNReal.ofReal (kappa / 2) * Q *
          (ENNReal.ofReal R).rpow (4 - zeta) <
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure FrontParameterSpace) parent.source ∧
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
  apply markedCarrierPiece_front_ball_excess_produces_budget_adapted_child
    selector hmeasurable hvalid hselector hboundary piece hpieceMeasurable
      hpieceCarrier hpieceMass hpieceNorth outerPoint delta
      (ENNReal.ofReal (kappa / 2) * Q *
        (ENNReal.ofReal R).rpow (4 - zeta)) hdelta hdeltaOne
  · exact moving_secant_rpow_mass_excess_forces_scale_four_front_ball_excess
      selector hmeasurable hvalid hselector piece hpieceMeasurable
        hpieceCarrier hpieceMass lines hlinesMeasurable hlinesDisjoint
        firstTime firstCenter outerTime outerPoint Rs R L delta kappa zeta Q
        houterTime hR hdelta hdeltaOne hscale hkappa hzeta hscaleLower
        hchart hfirst hslope htimeNe hgapUpper hsegment hexcess
  · exact hg
  · exact hK

end StickyKakeya4
