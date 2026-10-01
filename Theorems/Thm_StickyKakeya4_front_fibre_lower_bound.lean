import Theorems.Thm_StickyKakeya4_carrier_piece_probability

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- If a valid marked segment passes within `delta / 2` of a point at an
interior affine-fibre parameter, then a fibre interval of length `delta`
lies in the physical `delta`-ball.  This is the lower counterpart of
`fibreIntervalProbability_markedLineBallFibreSet_le`; it is the exact factor
which converts a direction-source mass into a marked direction--fibre mass
without discarding the affine mark. -/
theorem fibreIntervalProbability_markedLineBallFibreSet_ge
    {line : MarkedLine} (hvalid : IsValidLine line)
    (x : E4) (t₀ delta : ℝ)
    (hdelta : 0 < delta)
    (ht₀Lower : -(1 / 2 : ℝ) + delta ≤ t₀)
    (ht₀Upper : t₀ ≤ (1 / 2 : ℝ) - delta)
    (hnear : dist (rawFrontParam (line, t₀)) x < delta / 2) :
    ENNReal.ofReal delta ≤
      (fibreIntervalProbability :
        Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
          (markedLineBallFibreSet line x delta) := by
  let A : Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    {t | (t : ℝ) ∈ Set.Ioo (t₀ - delta / 2) (t₀ + delta / 2)}
  have hAMeasurable : MeasurableSet A := by
    exact measurableSet_Ioo.preimage measurable_subtype_coe
  have hAImage :
      ((fun t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) => (t : ℝ)) '' A) =
        Set.Ioo (t₀ - delta / 2) (t₀ + delta / 2) := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro ht
      have htLower : -(1 / 2 : ℝ) ≤ t := by
        have : -(1 / 2 : ℝ) < t₀ - delta / 2 := by linarith
        exact le_of_lt (this.trans (Set.mem_Ioo.mp ht).1)
      have htUpper : t ≤ (1 / 2 : ℝ) := by
        have : t₀ + delta / 2 < (1 / 2 : ℝ) := by linarith
        exact le_of_lt ((Set.mem_Ioo.mp ht).2.trans this)
      exact ⟨⟨t, htLower, htUpper⟩, ht, rfl⟩
  have hASubset : A ⊆ markedLineBallFibreSet line x delta := by
    intro t ht
    have htAbs : |(t : ℝ) - t₀| < delta / 2 := by
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    have hlineDistance :
        dist (rawFrontParam (line, (t : ℝ)))
            (rawFrontParam (line, t₀)) = |(t : ℝ) - t₀| := by
      rw [dist_eq_norm]
      have hid :
          rawFrontParam (line, (t : ℝ)) - rawFrontParam (line, t₀) =
            ((t : ℝ) - t₀) • direction line := by
        simp only [rawFrontParam]
        module
      rw [hid, norm_smul, hvalid.1, mul_one, Real.norm_eq_abs]
    change dist (rawFrontParam (line, (t : ℝ))) x < delta
    calc
      dist (rawFrontParam (line, (t : ℝ))) x ≤
          dist (rawFrontParam (line, (t : ℝ)))
              (rawFrontParam (line, t₀)) +
            dist (rawFrontParam (line, t₀)) x := dist_triangle _ _ _
      _ < delta / 2 + delta / 2 := by
        rw [hlineDistance]
        exact add_lt_add htAbs hnear
      _ = delta := by ring
  calc
    ENNReal.ofReal delta =
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) A := by
      rw [fibreIntervalProbability_apply A hAMeasurable, hAImage,
        Real.volume_Ioo]
      congr 1
      ring
    _ ≤ (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
            (markedLineBallFibreSet line x delta) := measure_mono hASubset

/-- Endpoint-robust form of the affine-fibre lower bound.  A crossing may
occur anywhere on the marked unit segment, including at either endpoint.
One of the two one-sided fibre intervals then contributes length
`delta / 2` to the physical `delta`-ball. -/
theorem fibreIntervalProbability_markedLineBallFibreSet_ge_half
    {line : MarkedLine} (hvalid : IsValidLine line)
    (x : E4) (t₀ delta : ℝ)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (ht₀ : t₀ ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hnear : dist (rawFrontParam (line, t₀)) x < delta / 2) :
    ENNReal.ofReal (delta / 2) ≤
      (fibreIntervalProbability :
        Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
          (markedLineBallFibreSet line x delta) := by
  have hlineDistance : ∀ t : ℝ,
      dist (rawFrontParam (line, t)) (rawFrontParam (line, t₀)) =
        |t - t₀| := by
    intro t
    rw [dist_eq_norm]
    have hid :
        rawFrontParam (line, t) - rawFrontParam (line, t₀) =
          (t - t₀) • direction line := by
      simp only [rawFrontParam]
      module
    rw [hid, norm_smul, hvalid.1, mul_one, Real.norm_eq_abs]
  by_cases htNonpos : t₀ ≤ 0
  · let A : Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
      {t | (t : ℝ) ∈ Set.Ioo t₀ (t₀ + delta / 2)}
    have hAMeasurable : MeasurableSet A :=
      measurableSet_Ioo.preimage measurable_subtype_coe
    have hAImage :
        ((fun t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) => (t : ℝ)) '' A) =
          Set.Ioo t₀ (t₀ + delta / 2) := by
      ext t
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro ht
        have htLower : -(1 / 2 : ℝ) ≤ t :=
          ht₀.1.trans (le_of_lt ht.1)
        have htUpper : t ≤ (1 / 2 : ℝ) := by
          have hcenterUpper : t₀ + delta / 2 ≤ (1 / 2 : ℝ) := by
            linarith
          exact (le_of_lt ht.2).trans hcenterUpper
        exact ⟨⟨t, htLower, htUpper⟩, ht, rfl⟩
    have hASubset : A ⊆ markedLineBallFibreSet line x delta := by
      intro t ht
      have htAbs : |(t : ℝ) - t₀| < delta / 2 := by
        rw [abs_of_pos (sub_pos.mpr ht.1)]
        linarith [ht.2]
      change dist (rawFrontParam (line, (t : ℝ))) x < delta
      calc
        dist (rawFrontParam (line, (t : ℝ))) x ≤
            dist (rawFrontParam (line, (t : ℝ)))
                (rawFrontParam (line, t₀)) +
              dist (rawFrontParam (line, t₀)) x := dist_triangle _ _ _
        _ < delta / 2 + delta / 2 := by
          rw [hlineDistance]
          exact add_lt_add htAbs hnear
        _ = delta := by ring
    calc
      ENNReal.ofReal (delta / 2) =
          (fibreIntervalProbability :
            Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) A := by
        rw [fibreIntervalProbability_apply A hAMeasurable, hAImage,
          Real.volume_Ioo]
        congr 1
        ring
      _ ≤ (fibreIntervalProbability :
            Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
              (markedLineBallFibreSet line x delta) := measure_mono hASubset
  · have htPos : 0 < t₀ := lt_of_not_ge htNonpos
    let A : Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
      {t | (t : ℝ) ∈ Set.Ioo (t₀ - delta / 2) t₀}
    have hAMeasurable : MeasurableSet A :=
      measurableSet_Ioo.preimage measurable_subtype_coe
    have hAImage :
        ((fun t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) => (t : ℝ)) '' A) =
          Set.Ioo (t₀ - delta / 2) t₀ := by
      ext t
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro ht
        have htLower : -(1 / 2 : ℝ) ≤ t := by
          have hcenterLower : -(1 / 2 : ℝ) ≤ t₀ - delta / 2 := by
            linarith
          exact hcenterLower.trans (le_of_lt ht.1)
        have htUpper : t ≤ (1 / 2 : ℝ) :=
          (le_of_lt ht.2).trans ht₀.2
        exact ⟨⟨t, htLower, htUpper⟩, ht, rfl⟩
    have hASubset : A ⊆ markedLineBallFibreSet line x delta := by
      intro t ht
      have htAbs : |(t : ℝ) - t₀| < delta / 2 := by
        rw [abs_of_neg (sub_neg.mpr ht.2)]
        linarith [ht.1]
      change dist (rawFrontParam (line, (t : ℝ))) x < delta
      calc
        dist (rawFrontParam (line, (t : ℝ))) x ≤
            dist (rawFrontParam (line, (t : ℝ)))
                (rawFrontParam (line, t₀)) +
              dist (rawFrontParam (line, t₀)) x := dist_triangle _ _ _
        _ < delta / 2 + delta / 2 := by
          rw [hlineDistance]
          exact add_lt_add htAbs hnear
        _ = delta := by ring
    calc
      ENNReal.ofReal (delta / 2) =
          (fibreIntervalProbability :
            Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) A := by
        rw [fibreIntervalProbability_apply A hAMeasurable, hAImage,
          Real.volume_Ioo]
        congr 1
        ring
      _ ≤ (fibreIntervalProbability :
            Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
              (markedLineBallFibreSet line x delta) := measure_mono hASubset

/-- A line-law mass whose members cross one physical ball through an interior
affine-fibre interval lifts to marked direction--fibre mass with the exact
factor `delta`.  The crossing parameter may depend on the line; hence this
lemma applies to the moving-center sources occurring in the vector Carleson
gate.  No affine mark is forgotten and no cardinality factor is introduced. -/
theorem markedCarrierPieceLineProbability_mul_of_interior_crossing_le_front_ball
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (lines : Set MarkedLine) (hlinesMeasurable : MeasurableSet lines)
    (fibreCenter : MarkedLine → ℝ) (x : E4) (delta : ℝ)
    (hdelta : 0 < delta)
    (hinterior : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines →
        -(1 / 2 : ℝ) + delta ≤ fibreCenter line ∧
        fibreCenter line ≤ (1 / 2 : ℝ) - delta)
    (hcross : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines →
        dist (rawFrontParam (line, fibreCenter line)) x < delta / 2) :
    ENNReal.ofReal delta *
        (markedCarrierPieceLineProbability selector hmeasurable hvalid
          hselector piece : Measure MarkedLine) lines ≤
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball x delta) := by
  let nu : Measure MarkedLine :=
    markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece
  have hnuSupport :
      nu (selectorLinesOverCarrierPiece selector piece)ᶜ = 0 :=
    markedCarrierPieceLineProbability_apply_compl_eq_zero selector hmeasurable
      hvalid hselector piece hpieceMeasurable hpieceCarrier hmass
  rw [markedCarrierPieceFrontProbability_ball_eq_lintegral selector hmeasurable
    hvalid hselector piece x delta]
  change ENNReal.ofReal delta * nu lines ≤
    ∫⁻ line, (fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
        (markedLineBallFibreSet line x delta) ∂nu
  calc
    ENNReal.ofReal delta * nu lines =
        ∫⁻ line, lines.indicator (fun _ => ENNReal.ofReal delta) line ∂nu := by
      exact (lintegral_indicator_const hlinesMeasurable _).symm
    _ ≤ ∫⁻ line, (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
            (markedLineBallFibreSet line x delta) ∂nu := by
      apply lintegral_mono_ae
      filter_upwards [compl_mem_ae_iff.mpr hnuSupport] with line hlineSupport
      have hlinePiece :
          line ∈ selectorLinesOverCarrierPiece selector piece := by
        simpa only [compl_compl] using hlineSupport
      by_cases hline : line ∈ lines
      · rw [Set.indicator_of_mem hline]
        exact fibreIntervalProbability_markedLineBallFibreSet_ge
          (hvalid line hlinePiece.1) x (fibreCenter line) delta hdelta
            (hinterior line hlinePiece hline).1
            (hinterior line hlinePiece hline).2
            (hcross line hlinePiece hline)
      · simp [hline]

/-- Endpoint-robust line-law lift.  It needs only that the crossing parameter
lies on the marked unit segment; the exact one-sided fibre reserve is
`delta / 2`. -/
theorem markedCarrierPieceLineProbability_mul_half_of_crossing_le_front_ball
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (lines : Set MarkedLine) (hlinesMeasurable : MeasurableSet lines)
    (fibreCenter : MarkedLine → ℝ) (x : E4) (delta : ℝ)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsegment : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines →
        fibreCenter line ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hcross : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines →
        dist (rawFrontParam (line, fibreCenter line)) x < delta / 2) :
    ENNReal.ofReal (delta / 2) *
        (markedCarrierPieceLineProbability selector hmeasurable hvalid
          hselector piece : Measure MarkedLine) lines ≤
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball x delta) := by
  let nu : Measure MarkedLine :=
    markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece
  have hnuSupport :
      nu (selectorLinesOverCarrierPiece selector piece)ᶜ = 0 :=
    markedCarrierPieceLineProbability_apply_compl_eq_zero selector hmeasurable
      hvalid hselector piece hpieceMeasurable hpieceCarrier hmass
  rw [markedCarrierPieceFrontProbability_ball_eq_lintegral selector hmeasurable
    hvalid hselector piece x delta]
  change ENNReal.ofReal (delta / 2) * nu lines ≤
    ∫⁻ line, (fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
        (markedLineBallFibreSet line x delta) ∂nu
  calc
    ENNReal.ofReal (delta / 2) * nu lines =
        ∫⁻ line, lines.indicator
          (fun _ => ENNReal.ofReal (delta / 2)) line ∂nu := by
      exact (lintegral_indicator_const hlinesMeasurable _).symm
    _ ≤ ∫⁻ line, (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
            (markedLineBallFibreSet line x delta) ∂nu := by
      apply lintegral_mono_ae
      filter_upwards [compl_mem_ae_iff.mpr hnuSupport] with line hlineSupport
      have hlinePiece :
          line ∈ selectorLinesOverCarrierPiece selector piece := by
        simpa only [compl_compl] using hlineSupport
      by_cases hline : line ∈ lines
      · rw [Set.indicator_of_mem hline]
        exact fibreIntervalProbability_markedLineBallFibreSet_ge_half
          (hvalid line hlinePiece.1) x (fibreCenter line) delta hdelta
            hdeltaOne (hsegment line hlinePiece hline)
            (hcross line hlinePiece hline)
      · simp [hline]

/-- Choice-free public form of the endpoint-robust line-law lift.  A caller
only has to exhibit some marked-segment crossing for each relevant actual
line; the selected fibre center is an internal proof device and does not
become part of the geometric interface. -/
theorem markedCarrierPieceLineProbability_mul_half_of_exists_crossing_le_front_ball
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (lines : Set MarkedLine) (hlinesMeasurable : MeasurableSet lines)
    (x : E4) (delta : ℝ)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hcross : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines →
        ∃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
          dist (rawFrontParam (line, t)) x < delta / 2) :
    ENNReal.ofReal (delta / 2) *
        (markedCarrierPieceLineProbability selector hmeasurable hvalid
          hselector piece : Measure MarkedLine) lines ≤
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball x delta) := by
  classical
  have hexists : ∀ line : MarkedLine, ∃ t : ℝ,
      (line ∈ selectorLinesOverCarrierPiece selector piece ∧
          line ∈ lines) →
        t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ∧
          dist (rawFrontParam (line, t)) x < delta / 2 := by
    intro line
    by_cases hline : line ∈ selectorLinesOverCarrierPiece selector piece ∧
        line ∈ lines
    · obtain ⟨t, ht, hdist⟩ := hcross line hline.1 hline.2
      exact ⟨t, fun _ ↦ ⟨ht, hdist⟩⟩
    · exact ⟨0, fun h ↦ (hline h).elim⟩
  choose fibreCenter hfibreCenter using hexists
  apply markedCarrierPieceLineProbability_mul_half_of_crossing_le_front_ball
    selector hmeasurable hvalid hselector piece hpieceMeasurable
      hpieceCarrier hmass lines hlinesMeasurable fibreCenter x delta
        hdelta hdeltaOne
  · intro line hlinePiece hline
    exact (hfibreCenter line ⟨hlinePiece, hline⟩).1
  · intro line hlinePiece hline
    exact (hfibreCenter line ⟨hlinePiece, hline⟩).2

end StickyKakeya4
