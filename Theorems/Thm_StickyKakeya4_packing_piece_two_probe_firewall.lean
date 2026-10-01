import Theorems.Thm_StickyKakeya4_retained_parameter_cell_source
import Theorems.Thm_StickyKakeya4_front_two_probe_direction_firewall
import Theorems.Thm_StickyKakeya4_north_conditioned_boundary_packet_chain

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- A parameter law has the required four-dimensional cap--fibre firewall if
every source simultaneously contained in one direction cap and one physical
front ball has the product `r^3 delta` upper bound. -/
def HasFrontDirectionFibreBound
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (nu : Measure FrontParameterSpace) (Cdir : ENNReal) : Prop :=
  ∀ (source : Set FrontParameterSpace)
    (theta : {theta : E4 // ‖theta‖ = 1}) (x : E4) (r delta : ℝ),
    source ⊆ frontDirectionCap theta r →
    source ⊆
      (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
        Metric.ball x delta →
    0 < r → r ≤ 1 → 0 ≤ delta →
    nu source ≤ ENNReal.ofReal (2 * delta) *
      (Cdir * (ENNReal.ofReal r) ^ 3)

/-- The cap--fibre certificate is already the source-hereditary two-probe
firewall.  This formulation no longer mentions the packing piece from which
the parameter law was constructed. -/
theorem HasFrontDirectionFibreBound.source_le_of_two_probe_and_ball
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {nu : Measure FrontParameterSpace} {Cdir : ENNReal}
    (hfront : HasFrontDirectionFibreBound selector hmeasurable hvalid
      hselector nu Cdir)
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
    nu source ≤ ENNReal.ofReal (2 * delta) *
      (Cdir *
        (ENNReal.ofReal (2 * ((Rs + Rt) / g) + eta)) ^ 3) := by
  apply hfront source
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

/-- The actual packing-piece parameter law is supported on the canonical
north parameter cap whenever the retained carrier piece is north-localized.
This support fact is exposed before the packing piece is existentially hidden
by the public finite-scale source interface. -/
theorem markedCarrierPieceFrontParameterProbability_contactNorthSupport
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

/-- The packing-piece parameter law retains the same `3 + 1` cap--fibre
bound as the canonical product law, with the conditioned carrier cap constant.
The proof first identifies the exact marked-line--fibre product law, so the
affine mark is never discarded. -/
theorem markedCarrierPieceFrontParameterProbability_source_le_directionCap_and_ball
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (source : Set FrontParameterSpace)
    (theta : {theta : E4 // ‖theta‖ = 1}) (x : E4) {r delta : ℝ}
    (hsourceCap : source ⊆ frontDirectionCap theta r)
    (hsourceBall : source ⊆
      (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
        Metric.ball x delta)
    (hr : 0 < r) (hrone : r ≤ 1) (hdelta : 0 ≤ delta) :
    (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure FrontParameterSpace) source ≤
      ENNReal.ofReal (2 * delta) *
        (carrierPieceDirectionCapConstant selector hmeasurable hvalid
          hselector piece * (ENNReal.ofReal r) ^ 3) := by
  let nuParam : Measure FrontParameterSpace :=
    markedCarrierPieceFrontParameterProbability selector hmeasurable
      hvalid hselector piece
  let nuLine : Measure MarkedLine :=
    markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece
  let fibre : Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    fibreIntervalProbability
  let F := frontParameterSelectedLineFibre selector hmeasurable hvalid hselector
  let f := frontParametrization selector hmeasurable hvalid hselector
  let targetFront : Set FrontParameterSpace :=
    frontDirectionCap theta r ∩ f ⁻¹' Metric.ball x delta
  let targetLine : Set
      (MarkedLine × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    Prod.fst ⁻¹' lineDirectionBall (theta : E4) r ∩
      markedLineFibreFrontParam ⁻¹' Metric.ball x delta
  have htargetFrontMeasurable : MeasurableSet targetFront :=
    (measurableSet_frontDirectionCap theta r).inter
      (Metric.isOpen_ball.measurableSet.preimage
        (measurable_frontParametrization selector hmeasurable hvalid hselector))
  have htargetLineMeasurable : MeasurableSet targetLine :=
    ((measurableSet_lineDirectionBall (theta : E4) r).preimage
      measurable_fst).inter
        (Metric.isOpen_ball.measurableSet.preimage
          measurable_markedLineFibreFrontParam)
  have hpreimage : F ⁻¹' targetLine = targetFront := by
    ext z
    simp only [F, targetLine, targetFront,
      frontParameterSelectedLineFibre, frontParameterSelectedLine,
      frontDirectionCap, lineDirectionBall, f, markedLineFibreFrontParam,
      Set.mem_inter_iff, Set.mem_preimage, Metric.mem_ball]
    rw [direction_selectorLine selector hmeasurable hvalid hselector z.1]
    rfl
  have hsourceTarget : source ⊆ targetFront := by
    intro z hz
    exact ⟨hsourceCap hz, hsourceBall hz⟩
  have htargetMeasure :
      nuParam targetFront = (nuLine.prod fibre) targetLine := by
    calc
      nuParam targetFront = nuParam (F ⁻¹' targetLine) := by rw [hpreimage]
      _ = Measure.map F nuParam targetLine := by
        rw [Measure.map_apply
          (measurable_frontParameterSelectedLineFibre selector hmeasurable
            hvalid hselector) htargetLineMeasurable]
      _ = (nuLine.prod fibre) targetLine := by
        rw [map_frontParameterSelectedLineFibre_markedCarrierPieceFrontParameterProbability]
  have hnuLineSupport :
      nuLine (selectorLinesOverCarrierPiece selector piece)ᶜ = 0 := by
    exact markedCarrierPieceLineProbability_apply_compl_eq_zero
      selector hmeasurable hvalid hselector piece hpieceMeasurable
        hpieceCarrier hmass
  have hproductBound :
      (nuLine.prod fibre) targetLine ≤
        ENNReal.ofReal (2 * delta) *
          nuLine (lineDirectionBall (theta : E4) r) := by
    rw [Measure.prod_apply htargetLineMeasurable]
    calc
      (∫⁻ line, fibre (Prod.mk line ⁻¹' targetLine) ∂nuLine) ≤
          ∫⁻ line,
            (lineDirectionBall (theta : E4) r).indicator
              (fun _ ↦ ENNReal.ofReal (2 * delta)) line ∂nuLine := by
        apply lintegral_mono_ae
        filter_upwards [compl_mem_ae_iff.mpr hnuLineSupport] with line hline
        have hlinePiece : line ∈ selectorLinesOverCarrierPiece selector piece := by
          simpa only [compl_compl] using hline
        by_cases hcap : line ∈ lineDirectionBall (theta : E4) r
        · rw [Set.indicator_of_mem hcap]
          have hsection : Prod.mk line ⁻¹' targetLine =
              markedLineBallFibreSet line x delta := by
            ext t
            simp [targetLine, markedLineBallFibreSet,
              markedLineFibreFrontParam, hcap]
          rw [hsection]
          exact fibreIntervalProbability_markedLineBallFibreSet_le
            (hvalid line hlinePiece.1) x hdelta
        · have hindicator :
              (lineDirectionBall (theta : E4) r).indicator
                  (fun _ ↦ ENNReal.ofReal (2 * delta)) line = 0 := by
            simp [hcap]
          rw [hindicator]
          have hsection : Prod.mk line ⁻¹' targetLine = ∅ := by
            ext t
            simp [targetLine, hcap]
          rw [hsection, measure_empty]
      _ = ENNReal.ofReal (2 * delta) *
          nuLine (lineDirectionBall (theta : E4) r) := by
        exact lintegral_indicator_const
          (measurableSet_lineDirectionBall (theta : E4) r) _
  calc
    nuParam source ≤ nuParam targetFront := measure_mono hsourceTarget
    _ = (nuLine.prod fibre) targetLine := htargetMeasure
    _ ≤ ENNReal.ofReal (2 * delta) *
          nuLine (lineDirectionBall (theta : E4) r) := hproductBound
    _ ≤ ENNReal.ofReal (2 * delta) *
        (carrierPieceDirectionCapConstant selector hmeasurable hvalid
          hselector piece * (ENNReal.ofReal r) ^ 3) := by
      gcongr
      exact markedCarrierPieceLineProbability_lineDirectionBall_upper_bound
        selector hmeasurable hvalid hselector piece hpieceMeasurable
          hpieceCarrier hmass theta hr hrone

theorem markedCarrierPieceFrontParameterProbability_hasFrontDirectionFibreBound
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0) :
    HasFrontDirectionFibreBound selector hmeasurable hvalid hselector
      (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure FrontParameterSpace)
      (carrierPieceDirectionCapConstant selector hmeasurable hvalid
        hselector piece) := by
  intro source theta x r delta hsourceCap hsourceBall hr hrone hdelta
  exact
    markedCarrierPieceFrontParameterProbability_source_le_directionCap_and_ball
      selector hmeasurable hvalid hselector piece hpieceMeasurable hpieceCarrier
        hmass source theta x hsourceCap hsourceBall hr hrone hdelta

/-- Source-hereditary two-probe firewall for the actual packing-piece law. -/
theorem markedCarrierPieceFrontParameterProbability_source_le_of_two_probe_and_ball
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
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
    (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure FrontParameterSpace) source ≤
      ENNReal.ofReal (2 * delta) *
        (carrierPieceDirectionCapConstant selector hmeasurable hvalid
          hselector piece *
            (ENNReal.ofReal (2 * ((Rs + Rt) / g) + eta)) ^ 3) := by
  apply
    markedCarrierPieceFrontParameterProbability_source_le_directionCap_and_ball
      selector hmeasurable hvalid hselector piece hpieceMeasurable hpieceCarrier
        hmass source
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
