import Theorems.Thm_StickyKakeya4_positive_carrier_piece
import Theorems.Thm_StickyKakeya4_marked_carrier_inverse

open MeasureTheory Set

noncomputable section

namespace StickyKakeya4

/-- The canonical selector-carrier measure restricted to a measurable packing
piece, before normalization. -/
noncomputable def selectorCarrierPieceFiniteMeasure
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) : FiniteMeasure (E4 × E4) :=
  ⟨(selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)).restrict piece, inferInstance⟩

/-- Normalize the positive carrier piece.  The definition is total, while the
nonzero hypothesis used downstream selects the genuine normalization branch. -/
noncomputable def normalizedCarrierPieceProbability
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) : ProbabilityMeasure (E4 × E4) :=
  (selectorCarrierPieceFiniteMeasure selector hmeasurable hvalid hselector piece).normalize

/-- The actual marked selector lines whose unmarked carriers lie in a retained
carrier piece. -/
def selectorLinesOverCarrierPiece
    (selector : Set MarkedLine) (piece : Set (E4 × E4)) : Set MarkedLine :=
  selector ∩ Prod.fst ⁻¹' piece

theorem measurable_selectorLinesOverCarrierPiece
    (selector : Set MarkedLine) (piece : Set (E4 × E4))
    (hselector : MeasurableSet selector) (hpiece : MeasurableSet piece) :
    MeasurableSet (selectorLinesOverCarrierPiece selector piece) := by
  exact hselector.inter (hpiece.preimage measurable_fst)

/-- Push the normalized carrier piece through the measurable inverse carrier
parametrization, retaining the affine mark. -/
noncomputable def markedCarrierPieceLineProbability
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) : ProbabilityMeasure MarkedLine :=
  ProbabilityMeasure.map
    (normalizedCarrierPieceProbability selector hmeasurable hvalid hselector piece)
    ((measurable_subtype_coe.comp
      (measurable_selectorLineFromCarrier selector hmeasurable hvalid hselector)).aemeasurable)

/-- The retained carrier piece together with the full affine-fibre interval. -/
noncomputable def markedCarrierPieceParameterProbability
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) :
    ProbabilityMeasure
      ((E4 × E4) × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
  ProbabilityMeasure.prod
    (normalizedCarrierPieceProbability selector hmeasurable hvalid hselector piece)
    fibreIntervalProbability

/-- Push the normalized carrier piece and its affine fibre to physical space.
The inverse carrier parametrization retains the selector line's mark. -/
noncomputable def markedCarrierPieceFrontProbability
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) : ProbabilityMeasure E4 :=
  ProbabilityMeasure.map
    (markedCarrierPieceParameterProbability selector hmeasurable hvalid hselector piece)
    (measurable_markedCarrierFrontParam selector hmeasurable hvalid hselector).aemeasurable

/-- Re-express a carrier--fibre parameter as the canonical direction--fibre
parameter of the uniquely selected marked line.  This is the map needed to
feed a conditioned packing-piece law into the vector-Frostman boundary,
whose domain is the canonical front parameter space. -/
noncomputable def markedCarrierPieceFrontParameterMap
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    ((E4 × E4) × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) →
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
  fun z =>
    let line := selectorLineFromCarrier selector hmeasurable hvalid hselector z.1
    (⟨direction line, (hvalid line line.property).1⟩, z.2)

theorem measurable_markedCarrierPieceFrontParameterMap
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Measurable (markedCarrierPieceFrontParameterMap selector hmeasurable
      hvalid hselector) := by
  have hline : Measurable (fun z :
      (E4 × E4) × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) =>
      ((selectorLineFromCarrier selector hmeasurable hvalid hselector z.1 :
        selector) : MarkedLine)) :=
    measurable_subtype_coe.comp
      ((measurable_selectorLineFromCarrier selector hmeasurable hvalid hselector).comp
        measurable_fst)
  have hdirection : Measurable (fun z :
      (E4 × E4) × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) =>
      direction
        ((selectorLineFromCarrier selector hmeasurable hvalid hselector z.1 :
          selector) : MarkedLine)) := hline.fst.fst
  exact hdirection.subtype_mk.prodMk measurable_snd

/-- The normalized packing-piece law transported to canonical
direction--fibre coordinates. -/
noncomputable def markedCarrierPieceFrontParameterProbability
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) :
    ProbabilityMeasure
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
  ProbabilityMeasure.map
    (markedCarrierPieceParameterProbability selector hmeasurable hvalid hselector piece)
    (measurable_markedCarrierPieceFrontParameterMap selector hmeasurable
      hvalid hselector).aemeasurable

/-- Canonical front parametrization after the preceding coordinate change is
pointwise the marked carrier parametrization.  Selector uniqueness is the
essential step: the line recovered from its direction is the same marked
line, including its affine mark. -/
theorem frontParametrization_markedCarrierPieceFrontParameterMap
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (z : (E4 × E4) × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    frontParametrization selector hmeasurable hvalid hselector
        (markedCarrierPieceFrontParameterMap selector hmeasurable
          hvalid hselector z) =
      markedCarrierFrontParam selector hmeasurable hvalid hselector z := by
  let line := selectorLineFromCarrier selector hmeasurable hvalid hselector z.1
  let theta : {theta : E4 // ‖theta‖ = 1} :=
    ⟨direction line, (hvalid line line.property).1⟩
  obtain ⟨chosen, _hchosen, hunique⟩ :=
    hselector (direction line) (hvalid line line.property).1
  have hsame :
      (selectorLine selector hmeasurable hvalid hselector theta : MarkedLine) =
        (line : MarkedLine) :=
    (hunique _ ⟨(selectorLine selector hmeasurable hvalid hselector theta).property,
      direction_selectorLine selector hmeasurable hvalid hselector theta⟩).trans
      (hunique line ⟨line.property, rfl⟩).symm
  simp [frontParametrization, markedCarrierPieceFrontParameterMap,
    markedCarrierFrontParam, line, theta, hsame]

/-- Pushing the conditioned packing-piece parameter law through the canonical
front parametrization gives exactly the existing packing-piece physical
front probability. -/
theorem map_frontParametrization_markedCarrierPieceFrontParameterProbability
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) :
    Measure.map (frontParametrization selector hmeasurable hvalid hselector)
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure
            ({theta : E4 // ‖theta‖ = 1} ×
              Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) =
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) := by
  rw [markedCarrierPieceFrontParameterProbability,
    ProbabilityMeasure.toMeasure_map,
    markedCarrierPieceFrontProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
    (measurable_frontParametrization selector hmeasurable hvalid hselector)
    (measurable_markedCarrierPieceFrontParameterMap selector hmeasurable
      hvalid hselector)]
  congr 1
  funext z
  exact frontParametrization_markedCarrierPieceFrontParameterMap
    selector hmeasurable hvalid hselector z

/-- The same physical parametrization after first passing from the carrier
piece to its actual marked selector line. -/
def markedLineFibreFrontParam
    (z : MarkedLine × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) : E4 :=
  rawFrontParam (z.1, (z.2 : ℝ))

theorem measurable_markedLineFibreFrontParam :
    Measurable markedLineFibreFrontParam := by
  exact continuous_rawFrontParam.measurable.comp
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

noncomputable def markedCarrierPieceLineFrontProbability
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) : ProbabilityMeasure E4 :=
  ProbabilityMeasure.map
    (ProbabilityMeasure.prod
      (markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece)
      fibreIntervalProbability)
    measurable_markedLineFibreFrontParam.aemeasurable

/-- Passing to the actual marked-line law before adjoining the fibre does not
change the physical front probability.  This identity permits Fubini to be
performed directly over the marked-line cells used by the finite source. -/
theorem markedCarrierPieceLineFrontProbability_eq
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) :
    (markedCarrierPieceLineFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) =
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) := by
  let P : Measure (E4 × E4) :=
    normalizedCarrierPieceProbability selector hmeasurable hvalid hselector piece
  let F : E4 × E4 → MarkedLine := fun carrier =>
    (selectorLineFromCarrier selector hmeasurable hvalid hselector carrier :
      MarkedLine)
  let I : Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    fibreIntervalProbability
  have hF : Measurable F :=
    measurable_subtype_coe.comp
      (measurable_selectorLineFromCarrier selector hmeasurable hvalid hselector)
  change Measure.map markedLineFibreFrontParam
      ((Measure.map F P).prod I) =
    Measure.map
      (markedCarrierFrontParam selector hmeasurable hvalid hselector)
      (P.prod I)
  have hmapId : Measure.map id I = I := Measure.map_id
  have hprod : (Measure.map F P).prod I =
      Measure.map (Prod.map F id) (P.prod I) := by
    calc
      (Measure.map F P).prod I =
          (Measure.map F P).prod (Measure.map id I) :=
        congrArg ((Measure.map F P).prod) hmapId.symm
      _ = Measure.map (Prod.map F id) (P.prod I) :=
        Measure.map_prod_map P I hF measurable_id
  rw [hprod]
  rw [Measure.map_map measurable_markedLineFibreFrontParam
    (hF.prodMap measurable_id)]
  congr 1

/-- The fibre parameters on one marked line that reach a fixed physical
point.  For a valid line this set has at most one element. -/
def markedLinePointFibreSet (line : MarkedLine) (x : E4) :
    Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
  {t | rawFrontParam (line, (t : ℝ)) = x}

theorem measurableSet_markedLinePointFibreSet
    (line : MarkedLine) (x : E4) :
    MeasurableSet (markedLinePointFibreSet line x) := by
  exact measurableSet_singleton x |>.preimage
    (continuous_rawFrontParam.measurable.comp
      (measurable_const.prodMk measurable_subtype_coe))

/-- A fixed physical point has zero affine-fibre probability on every valid
marked line.  This is the one-dimensional non-atomicity used to discard the
zero-diameter part of a Hausdorff cover. -/
theorem fibreIntervalProbability_markedLinePointFibreSet_eq_zero
    {line : MarkedLine} (hvalid : IsValidLine line) (x : E4) :
    (fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
        (markedLinePointFibreSet line x) = 0 := by
  rw [fibreIntervalProbability_apply _
    (measurableSet_markedLinePointFibreSet line x)]
  apply measure_mono_null _ (measure_singleton (fibreProjectionCenter line x))
  rintro _ ⟨t, ht, rfl⟩
  have hz : (t : ℝ) - fibreProjectionCenter line x = 0 := by
    rw [fibre_parameter_sub_projectionCenter hvalid x (t : ℝ), ht,
      sub_self, inner_zero_left]
  exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp hz)

theorem markedCarrierPieceFrontProbability_ball_eq_lintegral
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) (x : E4) (delta : ℝ) :
    (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
        Measure E4) (Metric.ball x delta) =
      ∫⁻ line, (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
          (markedLineBallFibreSet line x delta)
        ∂(markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece :
          Measure MarkedLine) := by
  rw [← markedCarrierPieceLineFrontProbability_eq selector hmeasurable hvalid
    hselector piece]
  rw [markedCarrierPieceLineFrontProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply measurable_markedLineFibreFrontParam
    Metric.isOpen_ball.measurableSet]
  rw [ProbabilityMeasure.toMeasure_prod]
  rw [Measure.prod_apply
    (Metric.isOpen_ball.measurableSet.preimage
      measurable_markedLineFibreFrontParam)]
  rfl

/-- The physical pushforward is supported on every measurable ambient front
containing the selector.  Passing to a compact ambient family is what makes
the target front Borel; no measurability of the selector front is used. -/
theorem markedCarrierPieceFrontProbability_compl_unitFront_eq_zero
    (selector ambient : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hselectorAmbient : selector ⊆ ambient)
    (hfrontMeasurable : MeasurableSet (unitFront ambient)) :
    (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
      Measure E4) (unitFront ambient)ᶜ = 0 := by
  have hfront : unitFront selector ⊆ unitFront ambient := by
    rintro x ⟨line, hline, t, ht, rfl⟩
    exact ⟨line, hselectorAmbient hline, t, ht, rfl⟩
  have hpreimage :
      markedCarrierFrontParam selector hmeasurable hvalid hselector ⁻¹'
          (unitFront ambient)ᶜ = ∅ := by
    ext z
    constructor
    · intro hz
      exact hz (hfront
        (markedCarrierFrontParam_mem_unitFront selector hmeasurable hvalid hselector z))
    · intro hz
      exact False.elim hz
  rw [markedCarrierPieceFrontProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply
    (measurable_markedCarrierFrontParam selector hmeasurable hvalid hselector)
    hfrontMeasurable.compl]
  rw [hpreimage, measure_empty]

/-- On a piece lying in the genuine selector carrier, the inverse
parametrization recovers its exact direction and offset. -/
theorem carrierPiece_selectorLine_exact
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) (hpiece : piece ⊆ lineCarrier selector)
    (carrier : E4 × E4) (hcarrier : carrier ∈ piece) :
    (direction (selectorLineFromCarrier selector hmeasurable hvalid hselector carrier),
      offset (selectorLineFromCarrier selector hmeasurable hvalid hselector carrier)) =
      carrier :=
  carrier_selectorLineFromCarrier selector hmeasurable hvalid hselector carrier
    (hpiece hcarrier)

theorem selectorCarrierPieceFiniteMeasure_ne_zero
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0) :
    selectorCarrierPieceFiniteMeasure selector hmeasurable hvalid hselector piece ≠ 0 := by
  intro hzero
  have hzero' :
      ((selectorCarrierPieceFiniteMeasure selector hmeasurable hvalid hselector piece :
        FiniteMeasure (E4 × E4)) : Measure (E4 × E4)) = 0 := by
    rw [hzero]
    rfl
  apply hmass
  exact Measure.restrict_eq_zero.mp hzero'

/-- Cubic direction-cap constant after conditioning on one positive carrier
piece.  The only new factor is the reciprocal mass of that piece. -/
noncomputable def carrierPieceDirectionCapConstant
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) : ENNReal :=
  (↑((selectorCarrierPieceFiniteMeasure selector hmeasurable hvalid
    hselector piece).mass⁻¹) : ENNReal) * metricSphereCapConstant

theorem carrierPieceDirectionCapConstant_ne_top
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) :
    carrierPieceDirectionCapConstant selector hmeasurable hvalid
      hselector piece ≠ ⊤ := by
  unfold carrierPieceDirectionCapConstant
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top metricSphereCapConstant_ne_top

theorem carrierPieceDirectionCapConstant_ne_zero
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0) :
    carrierPieceDirectionCapConstant selector hmeasurable hvalid
      hselector piece ≠ 0 := by
  have hm : selectorCarrierPieceFiniteMeasure selector hmeasurable hvalid
      hselector piece ≠ 0 :=
    selectorCarrierPieceFiniteMeasure_ne_zero selector hmeasurable hvalid
      hselector piece hmass
  have hmassPos : 0 <
      (selectorCarrierPieceFiniteMeasure selector hmeasurable hvalid
        hselector piece).mass :=
    pos_iff_ne_zero.mpr
      ((selectorCarrierPieceFiniteMeasure selector hmeasurable hvalid
        hselector piece).mass_nonzero_iff.mpr hm)
  have hinv : 0 <
      (selectorCarrierPieceFiniteMeasure selector hmeasurable hvalid
        hselector piece).mass⁻¹ := inv_pos.mpr hmassPos
  have hcap : 0 < metricSphereCapConstant :=
    pos_iff_ne_zero.mpr metricSphereCapConstant_ne_zero
  exact ne_of_gt (by
    unfold carrierPieceDirectionCapConstant
    positivity)

/-- Conditioning the canonical carrier probability on a positive piece
preserves the cubic direction-cap bound, with the explicit reciprocal-mass
normalization above. -/
theorem normalizedCarrierPieceProbability_carrierDirectionBall_upper_bound
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (theta : {theta : E4 // ‖theta‖ = 1}) {r : ℝ}
    (hr : 0 < r) (hrone : r ≤ 1) :
    (normalizedCarrierPieceProbability selector hmeasurable hvalid hselector piece :
      Measure (E4 × E4)) (carrierDirectionBall (theta : E4) r) ≤
      carrierPieceDirectionCapConstant selector hmeasurable hvalid
        hselector piece * (ENNReal.ofReal r) ^ 3 := by
  let Q : Measure (E4 × E4) :=
    selectorCarrierProbability selector hmeasurable hvalid hselector
  let m : FiniteMeasure (E4 × E4) :=
    selectorCarrierPieceFiniteMeasure selector hmeasurable hvalid hselector piece
  have hm : m ≠ 0 := by
    simpa [m] using selectorCarrierPieceFiniteMeasure_ne_zero
      selector hmeasurable hvalid hselector piece hmass
  have hmle : (m : Measure (E4 × E4)) ≤ Q := by
    simpa [m, Q, selectorCarrierPieceFiniteMeasure] using
      (Measure.restrict_le_self (s := piece) (μ := Q))
  change (m.normalize : Measure (E4 × E4))
      (carrierDirectionBall (theta : E4) r) ≤
    carrierPieceDirectionCapConstant selector hmeasurable hvalid
      hselector piece * (ENNReal.ofReal r) ^ 3
  rw [m.toMeasure_normalize_eq_of_nonzero hm, Measure.smul_apply]
  have hcap := selectorCarrierProbability_carrierDirectionBall_upper_bound
    selector hmeasurable hvalid hselector theta hr hrone
  calc
    (↑m.mass⁻¹ : ENNReal) *
          (m : Measure (E4 × E4)) (carrierDirectionBall (theta : E4) r) ≤
        (↑m.mass⁻¹ : ENNReal) *
          Q (carrierDirectionBall (theta : E4) r) := by
      simpa [mul_comm] using
        (mul_le_mul_right (hmle _) (↑m.mass⁻¹ : ENNReal))
    _ ≤ (↑m.mass⁻¹ : ENNReal) *
          (metricSphereCapConstant * (ENNReal.ofReal r) ^ 3) := by
      simpa [mul_comm] using
        (mul_le_mul_right hcap (↑m.mass⁻¹ : ENNReal))
    _ = carrierPieceDirectionCapConstant selector hmeasurable hvalid
          hselector piece * (ENNReal.ofReal r) ^ 3 := by
      simp only [carrierPieceDirectionCapConstant, m]
      ring

/-- After normalizing a positive measurable carrier piece, no mass leaks out
of that piece.  This is the a.e. input for every later finite partition. -/
theorem normalizedCarrierPieceProbability_apply_compl_eq_zero
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0) :
    (normalizedCarrierPieceProbability selector hmeasurable hvalid hselector piece :
      Measure (E4 × E4)) pieceᶜ = 0 := by
  have hfiniteNe :
      selectorCarrierPieceFiniteMeasure selector hmeasurable hvalid hselector piece ≠ 0 :=
    selectorCarrierPieceFiniteMeasure_ne_zero selector hmeasurable hvalid hselector
      piece hmass
  rw [normalizedCarrierPieceProbability,
    FiniteMeasure.toMeasure_normalize_eq_of_nonzero
      (selectorCarrierPieceFiniteMeasure selector hmeasurable hvalid hselector piece)
      hfiniteNe]
  simp [selectorCarrierPieceFiniteMeasure,
    Measure.restrict_apply hpieceMeasurable.compl]

/-- Marked lines whose direction belongs to an ambient Euclidean ball. -/
def lineDirectionBall (theta : E4) (r : ℝ) : Set MarkedLine :=
  direction ⁻¹' Metric.ball theta r

theorem measurableSet_lineDirectionBall (theta : E4) (r : ℝ) :
    MeasurableSet (lineDirectionBall theta r) := by
  exact Metric.isOpen_ball.measurableSet.preimage
    (measurable_fst.comp measurable_fst)

/-- The marked-line lift of a conditioned carrier piece retains the same
cubic cap estimate.  The proof uses exact carrier recovery on the piece and
the zero-mass statement off the piece; no regularity of the affine mark is
needed. -/
theorem markedCarrierPieceLineProbability_lineDirectionBall_upper_bound
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (theta : {theta : E4 // ‖theta‖ = 1}) {r : ℝ}
    (hr : 0 < r) (hrone : r ≤ 1) :
    (markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece :
      Measure MarkedLine) (lineDirectionBall (theta : E4) r) ≤
      carrierPieceDirectionCapConstant selector hmeasurable hvalid
        hselector piece * (ENNReal.ofReal r) ^ 3 := by
  let P : Measure (E4 × E4) :=
    normalizedCarrierPieceProbability selector hmeasurable hvalid hselector piece
  let f : E4 × E4 → MarkedLine := fun carrier =>
    (selectorLineFromCarrier selector hmeasurable hvalid hselector carrier : MarkedLine)
  have hf : Measurable f :=
    measurable_subtype_coe.comp
      (measurable_selectorLineFromCarrier selector hmeasurable hvalid hselector)
  have hpreSubset :
      f ⁻¹' lineDirectionBall (theta : E4) r ⊆
        carrierDirectionBall (theta : E4) r ∪ pieceᶜ := by
    intro carrier hcarrier
    by_cases hp : carrier ∈ piece
    · left
      have hexact := carrierPiece_selectorLine_exact selector hmeasurable hvalid
        hselector piece hpieceCarrier carrier hp
      have hdir : direction (f carrier) = carrier.1 := congrArg Prod.fst hexact
      change dist (direction (f carrier)) (theta : E4) < r at hcarrier
      change dist carrier.1 (theta : E4) < r
      rwa [← hdir]
    · exact Or.inr hp
  have hPcompl : P pieceᶜ = 0 := by
    exact normalizedCarrierPieceProbability_apply_compl_eq_zero
      selector hmeasurable hvalid hselector piece hpieceMeasurable hmass
  rw [markedCarrierPieceLineProbability, ProbabilityMeasure.toMeasure_map]
  change (Measure.map f P) (lineDirectionBall (theta : E4) r) ≤ _
  rw [Measure.map_apply hf (measurableSet_lineDirectionBall (theta : E4) r)]
  calc
    P (f ⁻¹' lineDirectionBall (theta : E4) r) ≤
        P (carrierDirectionBall (theta : E4) r ∪ pieceᶜ) :=
      measure_mono hpreSubset
    _ ≤ P (carrierDirectionBall (theta : E4) r) + P pieceᶜ :=
      measure_union_le _ _
    _ = P (carrierDirectionBall (theta : E4) r) := by rw [hPcompl, add_zero]
    _ ≤ carrierPieceDirectionCapConstant selector hmeasurable hvalid
          hselector piece * (ENNReal.ofReal r) ^ 3 :=
      normalizedCarrierPieceProbability_carrierDirectionBall_upper_bound
        selector hmeasurable hvalid hselector piece hmass theta hr hrone

/-- The marked-line pushforward is supported on the actual selector lines over
the retained carrier piece. -/
theorem markedCarrierPieceLineProbability_apply_compl_eq_zero
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0) :
    (markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece :
      Measure MarkedLine) (selectorLinesOverCarrierPiece selector piece)ᶜ = 0 := by
  let f : E4 × E4 → MarkedLine := fun carrier =>
    (selectorLineFromCarrier selector hmeasurable hvalid hselector carrier : MarkedLine)
  have hf : Measurable f :=
    measurable_subtype_coe.comp
      (measurable_selectorLineFromCarrier selector hmeasurable hvalid hselector)
  have htarget : MeasurableSet (selectorLinesOverCarrierPiece selector piece)ᶜ :=
    (measurable_selectorLinesOverCarrierPiece selector piece hmeasurable
      hpieceMeasurable).compl
  rw [markedCarrierPieceLineProbability, ProbabilityMeasure.toMeasure_map]
  change (Measure.map f
    (normalizedCarrierPieceProbability selector hmeasurable hvalid hselector piece :
      Measure (E4 × E4))) (selectorLinesOverCarrierPiece selector piece)ᶜ = 0
  rw [Measure.map_apply hf htarget]
  apply measure_mono_null _
    (normalizedCarrierPieceProbability_apply_compl_eq_zero selector hmeasurable
      hvalid hselector piece hpieceMeasurable hmass)
  intro carrier hcarrier
  by_contra hcarrierCompl
  have hcarrierPiece : carrier ∈ piece := by simpa using hcarrierCompl
  apply hcarrier
  refine ⟨(selectorLineFromCarrier selector hmeasurable hvalid hselector carrier).property, ?_⟩
  have hexact := carrierPiece_selectorLine_exact selector hmeasurable hvalid
    hselector piece hpieceCarrier carrier hcarrierPiece
  change (f carrier).1 ∈ piece
  change (f carrier).1 = carrier at hexact
  rw [hexact]
  exact hcarrierPiece

/-- The physical front probability on a positive measurable packing piece is
non-atomic.  The line marginal is supported on valid selector lines, and every
fixed line contributes zero fibre mass to a physical singleton. -/
theorem markedCarrierPieceFrontProbability_singleton_eq_zero
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (x : E4) :
    (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
      Measure E4) {x} = 0 := by
  let ν : Measure MarkedLine :=
    markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece
  have hνsupport : ν (selectorLinesOverCarrierPiece selector piece)ᶜ = 0 :=
    markedCarrierPieceLineProbability_apply_compl_eq_zero selector hmeasurable
      hvalid hselector piece hpieceMeasurable hpieceCarrier hmass
  rw [← markedCarrierPieceLineFrontProbability_eq selector hmeasurable hvalid
    hselector piece]
  rw [markedCarrierPieceLineFrontProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply measurable_markedLineFibreFrontParam
    (measurableSet_singleton x)]
  rw [ProbabilityMeasure.toMeasure_prod]
  rw [Measure.prod_apply
    ((measurableSet_singleton x).preimage measurable_markedLineFibreFrontParam)]
  change (∫⁻ line, (fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
        (markedLinePointFibreSet line x) ∂ν) = 0
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [compl_mem_ae_iff.mpr hνsupport] with line hline
  have hlinePiece : line ∈ selectorLinesOverCarrierPiece selector piece := by
    simpa only [compl_compl] using hline
  exact fibreIntervalProbability_markedLinePointFibreSet_eq_zero
    (hvalid line hlinePiece.1) x

/-- The cubic direction-cap estimate also holds for a ball with arbitrary
Euclidean center.  If such a ball has positive retained line mass, choose one
actual supported valid line in it; the supported part of the original ball is
then contained in the sphere-centered ball of twice the radius. -/
theorem markedCarrierPieceLineProbability_arbitrary_directionBall_upper_bound
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (theta : E4) {r : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2) :
    (markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece :
      Measure MarkedLine) (lineDirectionBall theta r) ≤
      carrierPieceDirectionCapConstant selector hmeasurable hvalid hselector piece *
        (ENNReal.ofReal (2 * r)) ^ 3 := by
  let ν : Measure MarkedLine :=
    markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece
  let pieceLines : Set MarkedLine := selectorLinesOverCarrierPiece selector piece
  have hνsupport : ν pieceLinesᶜ = 0 :=
    markedCarrierPieceLineProbability_apply_compl_eq_zero selector hmeasurable
      hvalid hselector piece hpieceMeasurable hpieceCarrier hmass
  by_cases hzero : ν (lineDirectionBall theta r) = 0
  · change ν (lineDirectionBall theta r) ≤ _
    rw [hzero]
    exact bot_le
  · have hinterNonempty :
        (lineDirectionBall theta r ∩ pieceLines).Nonempty := by
      by_contra hempty
      have hsubset : lineDirectionBall theta r ⊆ pieceLinesᶜ := by
        intro line hline hlinePiece
        exact hempty ⟨line, hline, hlinePiece⟩
      exact hzero (measure_mono_null hsubset hνsupport)
    obtain ⟨line0, hline0Ball, hline0Piece⟩ := hinterNonempty
    let theta0 : {u : E4 // ‖u‖ = 1} :=
      ⟨direction line0, (hvalid line0 hline0Piece.1).1⟩
    have hsubset : lineDirectionBall theta r ⊆
        lineDirectionBall (theta0 : E4) (2 * r) ∪ pieceLinesᶜ := by
      intro line hline
      by_cases hlinePiece : line ∈ pieceLines
      · left
        change dist (direction line) (theta0 : E4) < 2 * r
        have hlineTheta : dist (direction line) theta < r := hline
        have hline0Theta : dist (direction line0) theta < r := hline0Ball
        calc
          dist (direction line) (theta0 : E4) ≤
              dist (direction line) theta + dist theta (direction line0) :=
            dist_triangle _ _ _
          _ < r + r := add_lt_add hlineTheta (by simpa [dist_comm] using hline0Theta)
          _ = 2 * r := by ring
      · exact Or.inr hlinePiece
    calc
      ν (lineDirectionBall theta r) ≤
          ν (lineDirectionBall (theta0 : E4) (2 * r) ∪ pieceLinesᶜ) :=
        measure_mono hsubset
      _ ≤ ν (lineDirectionBall (theta0 : E4) (2 * r)) + ν pieceLinesᶜ :=
        measure_union_le _ _
      _ = ν (lineDirectionBall (theta0 : E4) (2 * r)) := by
        rw [hνsupport, add_zero]
      _ ≤ carrierPieceDirectionCapConstant selector hmeasurable hvalid hselector piece *
          (ENNReal.ofReal (2 * r)) ^ 3 := by
        exact markedCarrierPieceLineProbability_lineDirectionBall_upper_bound
          selector hmeasurable hvalid hselector piece hpieceMeasurable
          hpieceCarrier hmass theta0 (by linarith) (by linarith)

/-- A finite marked-line cell family reads a physical ball using only those
cells that actually contain a contributing line.  The factor `2 * delta` is
the exact one-dimensional fibre loss; the three directional powers remain in
the cell masses and are not discarded by this estimate. -/
theorem markedCarrierPieceFrontProbability_ball_le_active_cells
    {n : ℕ}
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (cell : Fin n → Set MarkedLine) (hcellMeasurable : ∀ i, MeasurableSet (cell i))
    (active : Set (Fin n)) (x : E4) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hcaptures : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      (markedLineBallFibreSet line x delta).Nonempty →
        ∃ i, i ∈ active ∧ line ∈ cell i) :
    (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
        Measure E4) (Metric.ball x delta) ≤
      ENNReal.ofReal (2 * delta) *
        (markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece :
          Measure MarkedLine) (⋃ i : {i // i ∈ active}, cell i.1) := by
  classical
  let ν : Measure MarkedLine :=
    markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece
  let activeUnion : Set MarkedLine :=
    ⋃ i : {i // i ∈ active}, cell i.1
  have hactiveUnionMeasurable : MeasurableSet activeUnion := by
    apply MeasurableSet.iUnion
    intro i
    exact hcellMeasurable i.1
  have hνsupport : ν (selectorLinesOverCarrierPiece selector piece)ᶜ = 0 :=
    markedCarrierPieceLineProbability_apply_compl_eq_zero selector hmeasurable
      hvalid hselector piece hpieceMeasurable hpieceCarrier hmass
  rw [markedCarrierPieceFrontProbability_ball_eq_lintegral selector hmeasurable
    hvalid hselector piece x delta]
  change (∫⁻ line, (fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
      (markedLineBallFibreSet line x delta) ∂ν) ≤ _
  calc
    (∫⁻ line, (fibreIntervalProbability :
        Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
        (markedLineBallFibreSet line x delta) ∂ν) ≤
        ∫⁻ line, activeUnion.indicator
          (fun _ => ENNReal.ofReal (2 * delta)) line ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [compl_mem_ae_iff.mpr hνsupport] with line hline
      have hlinePiece : line ∈ selectorLinesOverCarrierPiece selector piece := by
        simpa only [compl_compl] using hline
      by_cases hnonempty : (markedLineBallFibreSet line x delta).Nonempty
      · obtain ⟨i, hiactive, hiline⟩ := hcaptures line hlinePiece hnonempty
        have hlineUnion : line ∈ activeUnion := by
          apply Set.mem_iUnion.2
          exact ⟨⟨i, hiactive⟩, hiline⟩
        rw [Set.indicator_of_mem hlineUnion]
        exact fibreIntervalProbability_markedLineBallFibreSet_le
          (hvalid line hlinePiece.1) x hdelta
      · have hempty : markedLineBallFibreSet line x delta = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hnonempty
        rw [hempty, measure_empty]
        exact bot_le
    _ = ENNReal.ofReal (2 * delta) * ν activeUnion := by
      exact lintegral_indicator_const hactiveUnionMeasurable _

/-- Adding the affine-fibre probability does not change the carrier marginal:
the carrier coordinate of the product parameter lies in the retained piece
almost everywhere. -/
theorem markedCarrierPieceParameterProbability_apply_fst_preimage_compl_eq_zero
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0) :
    (markedCarrierPieceParameterProbability selector hmeasurable hvalid hselector piece :
      Measure ((E4 × E4) × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
        (Prod.fst ⁻¹' pieceᶜ) = 0 := by
  have hbase :=
    normalizedCarrierPieceProbability_apply_compl_eq_zero selector hmeasurable
      hvalid hselector piece hpieceMeasurable hmass
  have hmap :
      ProbabilityMeasure.map
          (markedCarrierPieceParameterProbability selector hmeasurable hvalid hselector piece)
          measurable_fst.aemeasurable =
        normalizedCarrierPieceProbability selector hmeasurable hvalid hselector piece := by
    simp [markedCarrierPieceParameterProbability]
  rw [← hmap] at hbase
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply measurable_fst hpieceMeasurable.compl] at hbase
  exact hbase

end StickyKakeya4
