import Theorems.Thm_StickyKakeya4_cover_adapted_wang_zakharov_closure

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

open Filter MeasureTheory Set
open scoped ENNReal Topology Pointwise RealInnerProductSpace

namespace StickyKakeya4

/-- The same cover-adapted packet, now retaining the actual original-line
membership already proved by its geometric source construction. -/
def HasOriginalLineWZPacketsAtExponent (selector : Set MarkedLine) (chi : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta →
  ∀ A : ENNReal, A ≠ 0 → A ≠ ⊤ →
  ∀ deltaZero : ℝ, 0 < deltaZero →
    ∃ (n : ℕ) (D : FiniteScaleSource n) (target : Set E4) (upperConstant : ENNReal),
      0 < D.thickness ∧ D.thickness ≤ deltaZero ∧
      IsWangZakharovNativeFiniteInput D eta ∧ ComesFromSelector D selector ∧
      (⋃ i,D.shading i)⊆target ∧
      upperConstant*(ENNReal.ofReal D.thickness).rpow (chi/2) < A⁻¹ ∧
      coveringNumber target D.thickness ≤
        upperConstant*(ENNReal.ofReal D.thickness).rpow (-4+chi)

/-- Strengthen the actual construction's readback, without changing any
chosen source, line, shading, cover, scale, or normalization. This proof
retains its existing `hDcomes` field rather than postulating compact support. -/
theorem packing_selector_has_original_line_wz_packets_at_exponent
    (ambient selector : Set MarkedLine)
    (hambientCompact : IsCompact ambient)
    (hselectorAmbient : selector ⊆ ambient)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (chi : ℝ) (d : NNReal)
    (hchi : 0 < chi) (hchiFour : chi < 4)
    (hd : (d : ℝ) = 4 - chi)
    (hdim : dimH (unitFront ambient) < (d : ENNReal)) :
    HasOriginalLineWZPacketsAtExponent selector chi := by
  intro eta heta A hAZero hATop deltaRequested hdeltaRequested
  obtain ⟨theta, htheta, hthetaEta, centerBin, piece, hpieceMeasurable,
      hpieceCarrier, hpieceLocalized, hpieceMass, carrierDim, hcarrierDim, hcarrierDimTop,
      carrierCoverConstant, hcarrierCoverConstantTop, hcarrierCover⟩ :=
    packing_selector_extract_piece_with_wz_compatible_slack
      selector hmeasurable hvalid hselector hpacking eta heta
  let cap : ENNReal :=
    carrierPieceDirectionCapConstant selector hmeasurable hvalid hselector piece
  have hcapZero : cap ≠ 0 := by
    dsimp [cap]
    exact carrierPieceDirectionCapConstant_ne_zero selector hmeasurable hvalid
      hselector piece hpieceMass
  have hcapTop : cap ≠ ⊤ := by
    dsimp [cap]
    exact carrierPieceDirectionCapConstant_ne_top selector hmeasurable hvalid
      hselector piece
  obtain ⟨boundaryExponent, hboundaryExponent, hboundaryExponentFour,
      hboundaryPacket⟩ :=
    coherentBoundary_has_arbitrarily_small_carrierPiece_concentration_packet
      selector hmeasurable hvalid hselector hboundary piece
  obtain ⟨boundaryCenter, boundaryRadius, hboundaryRadius,
      hboundaryRadiusSmall, hboundaryLarge⟩ :=
    hboundaryPacket (1 / 4) (by norm_num) (by norm_num)
  let seed : Set E4 := Metric.ball boundaryCenter boundaryRadius
  let boundaryLower : ENNReal :=
    ((ENNReal.ofReal (1 / 4 : ℝ)).rpow
        (4 - boundaryExponent))⁻¹ *
      (ENNReal.ofReal boundaryRadius).rpow (4 - boundaryExponent)
  have hboundaryLowerPos : 0 < boundaryLower := by
    dsimp [boundaryLower]
    have hq : 0 < 4 - boundaryExponent := by linarith
    apply bot_lt_iff_ne_bot.mpr
    exact mul_ne_zero
      (ENNReal.inv_ne_zero.mpr (ne_of_lt
        (ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top)))
      (ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hboundaryRadius)
        ENNReal.ofReal_ne_top))
  have hboundaryLowerTop : boundaryLower ≠ ⊤ := by
    dsimp [boundaryLower]
    finiteness
  have hboundaryLower : boundaryLower <
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) seed := by
    simpa [boundaryLower, seed] using hboundaryLarge
  let prefactor : ENNReal :=
    boundaryLower * ((1 - dyadicMassRatio theta) * (2 : ENNReal)⁻¹)
  have hprefactorZero : prefactor ≠ 0 := by
    dsimp [prefactor]
    exact mul_ne_zero hboundaryLowerPos.ne'
      (mul_ne_zero
        (tsub_pos_iff_lt.mpr (dyadicMassRatio_lt_one htheta)).ne'
        (by norm_num))
  have hprefactorTop : prefactor ≠ ⊤ := by
    dsimp [prefactor]
    exact ENNReal.mul_ne_top hboundaryLowerTop (by finiteness)
  have hprefactorReal : 0 < prefactor.toReal :=
    ENNReal.toReal_pos hprefactorZero hprefactorTop
  have hcapReal : 0 < cap.toReal := ENNReal.toReal_pos hcapZero hcapTop
  let pointConstant : ℝ := prefactor.toReal / (16 * cap.toReal)
  have hpointConstant : 0 < pointConstant := by
    dsimp [pointConstant]
    positivity
  obtain ⟨CAll, hCAllTop, _hcarrierConstant, hcoverAll,
      hcarrierDimReal, pruningZero, hpruningZero, hpruningZeroOne,
      hpruningBound⟩ :=
    carrier_piece_has_uniform_cover_and_cover_adapted_compensation_threshold
      piece carrierCoverConstant carrierDim hcarrierCoverConstantTop
      hcarrierCover theta 8 pointConstant htheta hcarrierDim hcarrierDimTop
      (by norm_num) hpointConstant
  obtain ⟨Ccw, hCcwTop, hconvex⟩ :=
    separated_directions_convex_wolff_specializes_to_half_pruning
      separated_directions_convex_wolff_estimate
      theta pointConstant htheta hpointConstant
  have htwoThetaEta : 2 * theta < eta := by linarith
  obtain ⟨cwZero, hcwZero, hcwZeroOne, hcwBound⟩ :=
    exists_convex_wolff_coefficient_absorption_threshold
      htwoThetaEta Ccw hCcwTop
  let Cactive : ENNReal :=
    4 * (8 * (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))
  have hCactiveTop : Cactive ≠ ⊤ := by
    dsimp [Cactive]
    finiteness
  have hprefactorHalf : 0 < prefactor / 2 :=
    ENNReal.div_pos hprefactorZero (by norm_num)
  obtain ⟨activeZero, hactiveZero, hactiveZeroOne, hactiveBound⟩ :=
    exists_const_mul_two_scale_rpow_threshold
      (eta := 2 * theta) (by positivity) Cactive (prefactor / 2)
        hCactiveTop hprefactorHalf
  obtain ⟨absorbZero, habsorbZero, habsorbZeroOne, habsorbBound⟩ :=
    exists_subpower_absorption_threshold heta
  obtain ⟨Q, hQTop, hQBound⟩ :=
    exists_e4_uniform_inflated_target_covering_bound
  have hdPos : 0 < (d : ℝ) := by rw [hd]; linarith
  obtain ⟨coefficientZero, hcoefficientZero, hcoefficientZeroOne,
      hcoefficientBound⟩ :=
    exists_inflated_target_coefficient_gap_threshold
      Q A hQTop hAZero hATop (d : ℝ) chi hdPos hchi
  let meshZero : ℝ :=
    min deltaRequested
      (min pruningZero
        (min activeZero (min absorbZero (min cwZero coefficientZero))))
  have hmeshZero : 0 < meshZero := by
    dsimp [meshZero]
    exact lt_min hdeltaRequested
      (lt_min hpruningZero
        (lt_min hactiveZero
          (lt_min habsorbZero (lt_min hcwZero hcoefficientZero))))
  have hmeshZeroOne : meshZero ≤ 1 := by
    dsimp [meshZero]
    exact (min_le_right _ _).trans
      ((min_le_left _ _).trans hpruningZeroOne)
  let rho : ENNReal := ENNReal.ofReal (meshZero / 4)
  have hrho : 0 < rho := by
    dsimp [rho]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hrhoQuarter : rho ≤ 1 / 4 := by
    dsimp [rho]
    have hreal : meshZero / 4 ≤ (1 : ℝ) / 4 := by linarith
    simpa using ENNReal.ofReal_le_ofReal hreal
  obtain ⟨cover, _hdiam, _hcoverCost, levelZero, target, _htarget,
      htargetMeasurable, hmassStrict, _hmassPos, _hscale, _hlevelPos,
      hscaleRho, hdeltaPos, hdeltaHalf, _htubeDyadic, hcellDyadic,
      _hlayerFinite, hlayerCost, htargetCover, hretainedPacket, _hactive⟩ :=
    markedCarrierPiece_exists_low_cost_dyadic_target_layer
      ambient selector hambientCompact hselectorAmbient hmeasurable hvalid
      hselector piece hpieceMeasurable hpieceCarrier hpieceMass seed
      Metric.isOpen_ball.measurableSet boundaryLower hboundaryLowerPos
      hboundaryLower hdim hrho hrhoQuarter (epsilon := (1 : ENNReal))
      (by norm_num) htheta
  let delta : ℝ := ((((2 : ENNReal)⁻¹) ^ levelZero).toReal)
  have hchildTop : ((2 : ENNReal)⁻¹) ^ (levelZero + 1) ≠ ⊤ := by
    simp
  have hrhoTop : rho ≠ ⊤ := by
    dsimp [rho]
    exact ENNReal.ofReal_ne_top
  have hchildReal :
      (((2 : ENNReal)⁻¹) ^ (levelZero + 1)).toReal < meshZero / 4 := by
    have h := (ENNReal.toReal_lt_toReal hchildTop hrhoTop).2 hscaleRho
    have hrhoReal : rho.toReal = meshZero / 4 := by
      dsimp [rho]
      exact ENNReal.toReal_ofReal (by positivity)
    rw [hrhoReal] at h
    exact h
  have hdeltaChild :
      delta = 2 * (((2 : ENNReal)⁻¹) ^ (levelZero + 1)).toReal := by
    dsimp [delta]
    rw [pow_succ, ENNReal.toReal_mul]
    norm_num [ENNReal.toReal_inv]
    ring
  have hdeltaMesh : delta ≤ meshZero := by
    rw [hdeltaChild]
    nlinarith
  have hdeltaRequested' : delta ≤ deltaRequested :=
    hdeltaMesh.trans (by dsimp [meshZero]; exact min_le_left _ _)
  have hdeltaPruning : delta ≤ pruningZero :=
    hdeltaMesh.trans (by
      dsimp [meshZero]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hdeltaActive : delta ≤ activeZero :=
    hdeltaMesh.trans (by
      dsimp [meshZero]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hdeltaAbsorb : delta ≤ absorbZero :=
    hdeltaMesh.trans (by
      dsimp [meshZero]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
  have hdeltaCW : delta ≤ cwZero :=
    hdeltaMesh.trans (by
      dsimp [meshZero]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _)))))
  have hdeltaCoefficient : delta ≤ coefficientZero :=
    hdeltaMesh.trans (by
      dsimp [meshZero]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_right _ _)))))
  have hdeltaOne : delta ≤ 1 := hdeltaMesh.trans hmeshZeroOne
  let mass : ENNReal :=
    (markedCarrierPieceFrontProbability selector hmeasurable hvalid
      hselector piece : Measure E4) target
  have hmassPower : prefactor *
      (ENNReal.ofReal delta).rpow theta ≤ mass := by
    dsimp [mass]
    have hscaleOfReal :
        ENNReal.ofReal delta = ((2 : ENNReal)⁻¹) ^ levelZero := by
      dsimp [delta]
      exact ENNReal.ofReal_toReal (by simp)
    rw [hscaleOfReal]
    simpa [prefactor, dyadicMassThreshold_eq_prefactor_mul_scale_rpow,
      mul_assoc] using hmassStrict.le
  obtain ⟨retained, hretainedNonempty, hretainedAll, hseparated,
      hcount, hrealCount⟩ := hretainedPacket
  have hretained : (retained : Set MarkedLine) ⊆
      selectorLinesOverCarrierPiece selector piece := by
    intro line hline
    exact (hretainedAll hline).1
  have hactiveRetained : ∀ line ∈ retained,
      mass / 2 ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
          (markedLineSetFibreSet line target) := by
    intro line hline
    exact (hretainedAll hline).2
  have hvalidRetained : ∀ line ∈ retained, IsValidLine line := by
    intro line hline
    exact hvalid line ((hretainedAll hline).1.1)
  have hpointLower :
      pointConstant * delta ^ (-3 + 2 * theta) ≤
        (retained.card : ℝ) := by
    have hstrong : pointConstant * delta ^ (-3 + theta) ≤
        (retained.card : ℝ) := by
      simpa [pointConstant, prefactor, cap, delta, mass] using hrealCount
    calc
      pointConstant * delta ^ (-3 + 2 * theta) ≤
          pointConstant * delta ^ (-3 + theta) := by
        apply mul_le_mul_of_nonneg_left _ hpointConstant.le
        apply Real.rpow_le_rpow_of_exponent_ge hdeltaPos hdeltaOne
        linarith
      _ ≤ (retained.card : ℝ) := hstrong
  have hpruning :
      (4 * (((CAll.toReal * (4 : ℝ) ^ carrierDim.toReal + 1) * 8)) *
          (2 : ℝ) ^ (theta / 4) /
            ((2 : ℝ) ^ (theta / 4) - 1)) *
        delta ^ (3 * theta - theta / 4 - 2 * theta) ≤ pointConstant :=
    hpruningBound delta hdeltaPos hdeltaPruning
  have hactiveMass :
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal delta).rpow (3 * theta) *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤ mass / 2 := by
    have htwoScale := hactiveBound delta hdeltaPos hdeltaActive
    have hscaleMono :
        (ENNReal.ofReal delta).rpow (2 * theta) ≤
          (ENNReal.ofReal (2 * delta)).rpow (2 * theta) := by
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (by linarith))
        (by positivity)
    have hactiveScale :
        Cactive * (ENNReal.ofReal delta).rpow (2 * theta) ≤ prefactor / 2 := by
      calc
        Cactive * (ENNReal.ofReal delta).rpow (2 * theta) ≤
            Cactive * (ENNReal.ofReal (2 * delta)).rpow (2 * theta) := by gcongr
        _ ≤ prefactor / 2 := htwoScale
    have hsplit :
        (ENNReal.ofReal delta).rpow (3 * theta) =
          (ENNReal.ofReal delta).rpow (2 * theta) *
            (ENNReal.ofReal delta).rpow theta := by
      rw [show 3 * theta = 2 * theta + theta by ring]
      exact ENNReal.rpow_add_of_nonneg (2 * theta) theta
        (by positivity) htheta.le
    have hactiveMass' :
        Cactive * (ENNReal.ofReal delta).rpow (3 * theta) ≤ mass / 2 := by
      rw [hsplit, ← mul_assoc]
      calc
        (Cactive * (ENNReal.ofReal delta).rpow (2 * theta)) *
            (ENNReal.ofReal delta).rpow theta ≤
          (prefactor / 2) * (ENNReal.ofReal delta).rpow theta := by gcongr
        _ = (prefactor * (ENNReal.ofReal delta).rpow theta) / 2 := by
          simp only [div_eq_mul_inv]
          ac_rfl
        _ ≤ mass / 2 := ENNReal.div_le_div_right hmassPower 2
    simpa [Cactive, mul_assoc, mul_left_comm, mul_comm] using hactiveMass'
  have habsorbWZ : (125 : ENNReal) ≤
      (ENNReal.ofReal delta).rpow (-eta) :=
    habsorbBound delta hdeltaPos hdeltaAbsorb
  have hcwAbsorb :
      Ccw * (ENNReal.ofReal delta).rpow (-2 * theta) ≤
        (ENNReal.ofReal delta).rpow (-eta) :=
    by
      convert hcwBound delta hdeltaPos hdeltaCW using 1; ring
  have hnormalized :=
    half_pruned_family_has_normalized_convex_wolff_data
      theta eta delta pointConstant retained hdeltaPos hvalidRetained
      hpointLower Ccw hcwAbsorb
      (fun pruned hpruned hsize hvalidPruned hsep U hU =>
        hconvex delta pruned hdeltaPos hdeltaOne hpruned hsize
          hvalidPruned hsep U hU)
  dsimp only at hnormalized
  obtain ⟨hgeometric, hnormalize⟩ := hnormalized
  obtain ⟨pruned, hprunedNonempty, hprunedSubset, hsepPruned,
      shadingCells, hinput, hinflation⟩ :=
    dyadic_cover_layer_pruning_assembles_wz_finite_input
      selector piece CAll carrierDim theta eta delta pointConstant levelZero
      retained target hretainedNonempty hretained hCAllTop htheta
      (by linarith) hdeltaPos hdeltaOne rfl hcellDyadic
      hpointLower hcarrierDimReal hpruning hcoverAll hvalidRetained hseparated
      hactiveRetained hactiveMass habsorbWZ
      (fun pruned =>
        (Ccw * (ENNReal.ofReal delta).rpow (-2 * theta)) * pruned.card)
      hgeometric hnormalize
  let M : ENNReal :=
    ((positiveDyadicCoverLayerIndices cover levelZero).ncard : ENNReal)
  have hMTop : M ≠ ⊤ := by
    dsimp [M]
    exact ENNReal.natCast_ne_top _
  have hhalfScale :
      ENNReal.ofReal (delta / 2) =
        ((2 : ENNReal)⁻¹) ^ (levelZero + 1) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    dsimp [delta]
    rw [ENNReal.ofReal_toReal (by simp)]
    simp [div_eq_mul_inv, pow_succ]
  have hlayerCost' :
      M * (ENNReal.ofReal (delta / 2)).rpow (d : ℝ) < 1 := by
    simpa [M, hhalfScale] using hlayerCost
  have hinflatedCover :=
    hQBound target M delta hdeltaPos hMTop
      (by simpa [M, delta] using htargetCover)
  let upperConstant : ENNReal :=
    Q * (M + 1) * (ENNReal.ofReal delta).rpow (4 - chi)
  have hupperSmall :
      upperConstant * (ENNReal.ofReal delta).rpow (chi / 2) < A⁻¹ := by
    dsimp [upperConstant]
    rw [← hd]
    exact hcoefficientBound delta M hdeltaPos hdeltaCoefficient hlayerCost'
  have hinflatedPower :
      coveringNumber (⋃ y ∈ target, Metric.ball y delta) delta ≤
        upperConstant * (ENNReal.ofReal delta).rpow (-4 + chi) := by
    simpa [upperConstant] using
      (inflated_target_covering_bound_as_power
        target Q M delta chi hdeltaPos hinflatedCover)
  let D : FiniteScaleSource pruned.card :=
    retainedWZCellSourceAtScales delta (delta / 2) pruned shadingCells
      hdeltaPos hsepPruned
  have hprunedLinePiece : ∀ i,
      retainedIndex pruned i ∈ selectorLinesOverCarrierPiece selector piece := by
    intro i
    exact hretained (hprunedSubset (retainedIndex_mem pruned i))
  have hDcomes : ComesFromSelector D selector := by
    intro i
    change retainedIndex pruned i ∈ selector
    exact (hprunedLinePiece i).1
  have hDlocalized : ∀ i,
      (direction (D.line i), offset (D.line i)) ∈
        northCarrierRegion selector ∩
          carrierMarkedCenterBin selector hmeasurable hvalid hselector centerBin := by
    intro i
    apply hpieceLocalized
    change (direction (retainedIndex pruned i),
      offset (retainedIndex pruned i)) ∈ piece
    exact (hprunedLinePiece i).2
  have hDgraph : HasNormalizedWZGraphSlab D :=
    finiteSource_hasNormalizedWZGraphSlab_of_north_center_bin
      selector hmeasurable hvalid hselector D hDcomes centerBin hDlocalized
  have hDfixed : HasFixedWZGraphNormalization D :=
    hasFixedWZGraphNormalization_of_normalizedSlab D
      (fun i => hvalid (D.line i) (hDcomes i)) hDgraph
  have hnativeInput : IsWangZakharovNativeFiniteInput D eta := by
    refine ⟨?_, hDgraph, hDfixed⟩
    simpa [D] using hinput
  refine ⟨pruned.card, D, ⋃ y ∈ target, Metric.ball y delta,
    upperConstant, ?_, ?_, ?_, hDcomes, ?_, ?_, ?_⟩
  · change 0 < delta
    exact hdeltaPos
  · change delta ≤ deltaRequested
    exact hdeltaRequested'
  · exact hnativeInput
  · simpa [D] using hinflation
  · change upperConstant * (ENNReal.ofReal delta).rpow (chi / 2) < A⁻¹
    exact hupperSmall
  · change coveringNumber (⋃ y ∈ target, Metric.ball y delta) delta ≤
      upperConstant * (ENNReal.ofReal delta).rpow (-4 + chi)
    exact hinflatedPower


end StickyKakeya4
