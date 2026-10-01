import Theorems.Thm_StickyKakeya4_packing_piece_two_probe_firewall
import Theorems.Thm_StickyKakeya4_front_fibre_lower_bound

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace StickyKakeya4

/-- The unit direction represented by a north-chart slope. -/
def northSlopeDirection (a : E3) : {theta : E4 // ‖theta‖ = 1} :=
  ⟨NormedSpace.normalize (northSlopeLift a), by
    apply NormedSpace.norm_normalize
    intro hzero
    have hnorm := northSlopeLift_norm_ge_one a
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm⟩

/-- A line which passes near two prescribed graph points has slope close to
the secant vector joining those points.  The two probe heights may depend on
an external bush label; only their separation enters the estimate. -/
theorem northGraphSlope_sub_probeSecant_le
    (line : MarkedLine) (s t : ℝ) (c y : E3) (Rs Rt g : ℝ)
    (hRs : ‖northGraphEvaluation line s - c‖ ≤ Rs)
    (hRt : ‖northGraphEvaluation line t - y‖ ≤ Rt)
    (hg : 0 < g) (hsep : g ≤ |t - s|) :
    ‖northGraphSlope line - (t - s)⁻¹ • (y - c)‖ ≤
      (Rs + Rt) / g := by
  let a₀ : E3 := (t - s)⁻¹ • (y - c)
  let b₀ : E3 := c - s • a₀
  let alpha : E3 := northGraphSlope line - a₀
  let beta : E3 := northGraphIntercept line - b₀
  have hts : t - s ≠ 0 := by
    intro hzero
    have habs : |t - s| = 0 := by rw [hzero, abs_zero]
    linarith
  have hsecant : (t - s) • a₀ = y - c := by
    dsimp [a₀]
    rw [← mul_smul, mul_inv_cancel₀ hts, one_smul]
  have hfirst : ‖beta + s • alpha‖ ≤ Rs := by
    have hid : beta + s • alpha = northGraphEvaluation line s - c := by
      dsimp [alpha, beta, b₀]
      simp only [northGraphEvaluation]
      module
    rw [hid]
    exact hRs
  have hsecond : ‖beta + t • alpha‖ ≤ Rt := by
    have hid : beta + t • alpha = northGraphEvaluation line t - y := by
      dsimp [alpha, beta, b₀]
      simp only [northGraphEvaluation]
      rw [show y = c + (y - c) by abel, ← hsecant]
      module
    rw [hid]
    exact hRt
  simpa [alpha, a₀] using
    separated_reeb_two_probe_direction_bound alpha beta s t Rs Rt g
      hfirst hsecond hg hsep

/-- Exact moving-center readback.  A line which belongs to a first bush and
whose slope lies in the moving cap centered at `(t-s)⁻¹ • (y-c)` must pass
through the common outer physical ball at height `t`.  Unlike the clustered
lemma below, the secant center is allowed to depend on the bush label. -/
theorem northGraphEvaluation_sub_outerCenter_le_of_slope_near_secant
    (line : MarkedLine) (s t : ℝ) (c y : E3) (Rs R L : ℝ)
    (hfirst : ‖northGraphEvaluation line s - c‖ ≤ Rs)
    (hslope : ‖northGraphSlope line - (t - s)⁻¹ • (y - c)‖ ≤ R)
    (hts : t - s ≠ 0) (hgapUpper : |t - s| ≤ L)
    (hR : 0 ≤ R) :
    ‖northGraphEvaluation line t - y‖ ≤ Rs + L * R := by
  let a₀ : E3 := (t - s)⁻¹ • (y - c)
  have hsecant : (t - s) • a₀ = y - c := by
    dsimp [a₀]
    rw [← mul_smul, mul_inv_cancel₀ hts, one_smul]
  have hid :
      northGraphEvaluation line t - y =
        (northGraphEvaluation line s - c) +
          (t - s) • (northGraphSlope line - a₀) := by
    simp only [northGraphEvaluation]
    rw [show y = c + (y - c) by abel, ← hsecant]
    module
  have hL : 0 ≤ L := (abs_nonneg (t - s)).trans hgapUpper
  rw [hid]
  calc
    ‖(northGraphEvaluation line s - c) +
        (t - s) • (northGraphSlope line - a₀)‖ ≤
        ‖northGraphEvaluation line s - c‖ +
          ‖(t - s) • (northGraphSlope line - a₀)‖ := norm_add_le _ _
    _ = ‖northGraphEvaluation line s - c‖ +
        |t - s| * ‖northGraphSlope line - a₀‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ Rs + L * R := by
      gcongr

/-- At a fixed ambient fourth-coordinate, the full Euclidean distance is
exactly the horizontal graph distance.  This is the bridge between the
moving-center graph calculation and the physical ball used by the marked
front probability. -/
theorem dist_fixedHeightPoint_eq_norm_northGraphEvaluation_sub
    (line : MarkedLine) (s : ℝ) (x : E4)
    (hchart : direction line (3 : Fin 4) ≠ 0)
    (hx : x (3 : Fin 4) = s) :
    dist (fixedHeightPoint line s) x =
      ‖northGraphEvaluation line s - horizontalProjection x‖ := by
  rw [dist_eq_norm]
  have hfourth :
      fixedHeightPoint line s (3 : Fin 4) - x (3 : Fin 4) = 0 := by
    rw [fixedHeightPoint_fourth_coordinate line s hchart, hx, sub_self]
  have hsq :
      ‖fixedHeightPoint line s - x‖ ^ 2 =
        ‖horizontalProjection (fixedHeightPoint line s - x)‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp [horizontalProjection, Fin.sum_univ_succ, hfourth]
  have hhorizontal :
      horizontalProjection (fixedHeightPoint line s - x) =
        northGraphEvaluation line s - horizontalProjection x := by
    rw [horizontalProjection_sub,
      horizontalProjection_fixedHeightPoint line s hchart]
  rw [hhorizontal] at hsq
  nlinarith [norm_nonneg (fixedHeightPoint line s - x),
    norm_nonneg (northGraphEvaluation line s - horizontalProjection x)]

/-- Exact moving-center-to-marked-front lower bound.  Each line may have its
own first bush and therefore its own secant center.  If its slope lies in the
corresponding moving cap, then all such lines cross one common outer ball.
The affine-fibre interval contributes the factor `delta`; the conclusion has
no loss proportional to the number of moving centers. -/
theorem markedCarrierPieceLineProbability_mul_of_moving_secant_crossing_le_front_ball
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
    (firstTime : MarkedLine → ℝ) (firstCenter : MarkedLine → E3)
    (outerTime : ℝ) (outerPoint : E4)
    (Rs R L delta : ℝ)
    (houterTime : outerPoint (3 : Fin 4) = outerTime)
    (hR : 0 ≤ R) (hdelta : 0 < delta)
    (hscale : Rs + L * R < delta / 2)
    (hchart : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines → direction line (3 : Fin 4) ≠ 0)
    (hfirst : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines →
        ‖northGraphEvaluation line (firstTime line) - firstCenter line‖ ≤ Rs)
    (hslope : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines →
        ‖northGraphSlope line -
          (outerTime - firstTime line)⁻¹ •
            (horizontalProjection outerPoint - firstCenter line)‖ ≤ R)
    (htimeNe : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines → outerTime - firstTime line ≠ 0)
    (hgapUpper : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines → |outerTime - firstTime line| ≤ L)
    (hinterior : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines →
        -(1 / 2 : ℝ) + delta ≤
            fixedHeightTime line outerTime - mark line ∧
        fixedHeightTime line outerTime - mark line ≤
            (1 / 2 : ℝ) - delta) :
    ENNReal.ofReal delta *
        (markedCarrierPieceLineProbability selector hmeasurable hvalid
          hselector piece : Measure MarkedLine) lines ≤
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball outerPoint delta) := by
  apply
    markedCarrierPieceLineProbability_mul_of_interior_crossing_le_front_ball
      selector hmeasurable hvalid hselector piece hpieceMeasurable
        hpieceCarrier hmass lines hlinesMeasurable
        (fun line => fixedHeightTime line outerTime - mark line)
          outerPoint delta hdelta
  · exact hinterior
  · intro line hlinePiece hline
    have hhorizontal :
        ‖northGraphEvaluation line outerTime -
            horizontalProjection outerPoint‖ ≤ Rs + L * R :=
      northGraphEvaluation_sub_outerCenter_le_of_slope_near_secant
        line (firstTime line) outerTime (firstCenter line)
          (horizontalProjection outerPoint) Rs R L
          (hfirst line hlinePiece hline) (hslope line hlinePiece hline)
          (htimeNe line hlinePiece hline)
          (hgapUpper line hlinePiece hline) hR
    have hdist :
        dist (fixedHeightPoint line outerTime) outerPoint ≤ Rs + L * R := by
      rw [dist_fixedHeightPoint_eq_norm_northGraphEvaluation_sub
        line outerTime outerPoint (hchart line hlinePiece hline) houterTime]
      exact hhorizontal
    have hraw :
        rawFrontParam
            (line, fixedHeightTime line outerTime - mark line) =
          fixedHeightPoint line outerTime := by
      rw [rawFrontParam, fixedHeightPoint,
        show mark line + (fixedHeightTime line outerTime - mark line) =
          fixedHeightTime line outerTime by ring]
    rw [hraw]
    exact hdist.trans_lt hscale

/-- Endpoint-robust moving-center crossing bound.  Unlike the preceding
interior form, it applies when the common outer crossing reaches either end
of a marked unit segment; the one-sided affine-fibre reserve costs only the
fixed factor two. -/
theorem markedCarrierPieceLineProbability_mul_half_of_moving_secant_crossing_le_front_ball
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
    (firstTime : MarkedLine → ℝ) (firstCenter : MarkedLine → E3)
    (outerTime : ℝ) (outerPoint : E4)
    (Rs R L delta : ℝ)
    (houterTime : outerPoint (3 : Fin 4) = outerTime)
    (hR : 0 ≤ R) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hscale : Rs + L * R < delta / 2)
    (hchart : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines → direction line (3 : Fin 4) ≠ 0)
    (hfirst : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines →
        ‖northGraphEvaluation line (firstTime line) - firstCenter line‖ ≤ Rs)
    (hslope : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines →
        ‖northGraphSlope line -
          (outerTime - firstTime line)⁻¹ •
            (horizontalProjection outerPoint - firstCenter line)‖ ≤ R)
    (htimeNe : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines → outerTime - firstTime line ≠ 0)
    (hgapUpper : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines → |outerTime - firstTime line| ≤ L)
    (hsegment : ∀ line ∈ selectorLinesOverCarrierPiece selector piece,
      line ∈ lines →
        fixedHeightTime line outerTime - mark line ∈
          Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    ENNReal.ofReal (delta / 2) *
        (markedCarrierPieceLineProbability selector hmeasurable hvalid
          hselector piece : Measure MarkedLine) lines ≤
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball outerPoint delta) := by
  apply
    markedCarrierPieceLineProbability_mul_half_of_crossing_le_front_ball
      selector hmeasurable hvalid hselector piece hpieceMeasurable
        hpieceCarrier hmass lines hlinesMeasurable
        (fun line => fixedHeightTime line outerTime - mark line)
          outerPoint delta hdelta hdeltaOne
  · exact hsegment
  · intro line hlinePiece hline
    have hhorizontal :
        ‖northGraphEvaluation line outerTime -
            horizontalProjection outerPoint‖ ≤ Rs + L * R :=
      northGraphEvaluation_sub_outerCenter_le_of_slope_near_secant
        line (firstTime line) outerTime (firstCenter line)
          (horizontalProjection outerPoint) Rs R L
          (hfirst line hlinePiece hline) (hslope line hlinePiece hline)
          (htimeNe line hlinePiece hline)
          (hgapUpper line hlinePiece hline) hR
    have hdist :
        dist (fixedHeightPoint line outerTime) outerPoint ≤ Rs + L * R := by
      rw [dist_fixedHeightPoint_eq_norm_northGraphEvaluation_sub
        line outerTime outerPoint (hchart line hlinePiece hline) houterTime]
      exact hhorizontal
    have hraw :
        rawFrontParam
            (line, fixedHeightTime line outerTime - mark line) =
          fixedHeightPoint line outerTime := by
      rw [rawFrontParam, fixedHeightPoint,
        show mark line + (fixedHeightTime line outerTime - mark line) =
          fixedHeightTime line outerTime by ring]
    rw [hraw]
    exact hdist.trans_lt hscale

/-- Countable coefficient-one moving-center crossing estimate.  The first
bush data may vary from component to component (encoded by the line-dependent
functions below), and the components are summed before the single physical
ball charge is applied.  Thus the right-hand side is not multiplied by the
number of bushes or moving centers. -/
theorem tsum_markedCarrierPieceLineProbability_mul_of_moving_secant_crossing_le_front_ball
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (lines : ℕ → Set MarkedLine)
    (hlinesMeasurable : ∀ e, MeasurableSet (lines e))
    (hlinesDisjoint : Pairwise (fun e e' => Disjoint (lines e) (lines e')))
    (firstTime : MarkedLine → ℝ) (firstCenter : MarkedLine → E3)
    (outerTime : ℝ) (outerPoint : E4)
    (Rs R L delta : ℝ)
    (houterTime : outerPoint (3 : Fin 4) = outerTime)
    (hR : 0 ≤ R) (hdelta : 0 < delta)
    (hscale : Rs + L * R < delta / 2)
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
    (hinterior : ∀ e line,
      line ∈ selectorLinesOverCarrierPiece selector piece →
      line ∈ lines e →
        -(1 / 2 : ℝ) + delta ≤
            fixedHeightTime line outerTime - mark line ∧
        fixedHeightTime line outerTime - mark line ≤
            (1 / 2 : ℝ) - delta) :
    ENNReal.ofReal delta *
        (∑' e, (markedCarrierPieceLineProbability selector hmeasurable
          hvalid hselector piece : Measure MarkedLine) (lines e)) ≤
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball outerPoint delta) := by
  let nu : Measure MarkedLine :=
    markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece
  let totalLines : Set MarkedLine := ⋃ e, lines e
  have htotalMeasurable : MeasurableSet totalLines :=
    MeasurableSet.iUnion hlinesMeasurable
  have hsum : (∑' e, nu (lines e)) = nu totalLines := by
    simpa [totalLines] using
      (measure_iUnion hlinesDisjoint hlinesMeasurable).symm
  change ENNReal.ofReal delta * (∑' e, nu (lines e)) ≤ _
  rw [hsum]
  apply
    markedCarrierPieceLineProbability_mul_of_moving_secant_crossing_le_front_ball
      selector hmeasurable hvalid hselector piece hpieceMeasurable
        hpieceCarrier hmass totalLines htotalMeasurable firstTime firstCenter
        outerTime outerPoint Rs R L delta houterTime hR hdelta hscale
  · intro line hlinePiece hlineTotal
    obtain ⟨e, hline⟩ := Set.mem_iUnion.mp hlineTotal
    exact hchart e line hlinePiece hline
  · intro line hlinePiece hlineTotal
    obtain ⟨e, hline⟩ := Set.mem_iUnion.mp hlineTotal
    exact hfirst e line hlinePiece hline
  · intro line hlinePiece hlineTotal
    obtain ⟨e, hline⟩ := Set.mem_iUnion.mp hlineTotal
    exact hslope e line hlinePiece hline
  · intro line hlinePiece hlineTotal
    obtain ⟨e, hline⟩ := Set.mem_iUnion.mp hlineTotal
    exact htimeNe e line hlinePiece hline
  · intro line hlinePiece hlineTotal
    obtain ⟨e, hline⟩ := Set.mem_iUnion.mp hlineTotal
    exact hgapUpper e line hlinePiece hline
  · intro line hlinePiece hlineTotal
    obtain ⟨e, hline⟩ := Set.mem_iUnion.mp hlineTotal
    exact hinterior e line hlinePiece hline

/-- Endpoint-robust countable coefficient-one moving-center crossing
estimate.  Pairwise-disjoint line components may use different moving
secant centers, while their marked crossings are allowed to occur at either
endpoint of the unit fibre.  The one-sided fibre interval loses only the
fixed factor two, and the common physical ball is still charged once. -/
theorem tsum_markedCarrierPieceLineProbability_mul_half_of_moving_secant_crossing_le_front_ball
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (lines : ℕ → Set MarkedLine)
    (hlinesMeasurable : ∀ e, MeasurableSet (lines e))
    (hlinesDisjoint : Pairwise (fun e e' => Disjoint (lines e) (lines e')))
    (firstTime : MarkedLine → ℝ) (firstCenter : MarkedLine → E3)
    (outerTime : ℝ) (outerPoint : E4)
    (Rs R L delta : ℝ)
    (houterTime : outerPoint (3 : Fin 4) = outerTime)
    (hR : 0 ≤ R) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hscale : Rs + L * R < delta / 2)
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
          Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    ENNReal.ofReal (delta / 2) *
        (∑' e, (markedCarrierPieceLineProbability selector hmeasurable
          hvalid hselector piece : Measure MarkedLine) (lines e)) ≤
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball outerPoint delta) := by
  let nu : Measure MarkedLine :=
    markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece
  let totalLines : Set MarkedLine := ⋃ e, lines e
  have htotalMeasurable : MeasurableSet totalLines :=
    MeasurableSet.iUnion hlinesMeasurable
  have hsum : (∑' e, nu (lines e)) = nu totalLines := by
    simpa [totalLines] using
      (measure_iUnion hlinesDisjoint hlinesMeasurable).symm
  change ENNReal.ofReal (delta / 2) * (∑' e, nu (lines e)) ≤ _
  rw [hsum]
  apply
    markedCarrierPieceLineProbability_mul_half_of_moving_secant_crossing_le_front_ball
      selector hmeasurable hvalid hselector piece hpieceMeasurable
        hpieceCarrier hmass totalLines htotalMeasurable firstTime firstCenter
        outerTime outerPoint Rs R L delta houterTime hR hdelta hdeltaOne
          hscale
  · intro line hlinePiece hlineTotal
    obtain ⟨e, hline⟩ := Set.mem_iUnion.mp hlineTotal
    exact hchart e line hlinePiece hline
  · intro line hlinePiece hlineTotal
    obtain ⟨e, hline⟩ := Set.mem_iUnion.mp hlineTotal
    exact hfirst e line hlinePiece hline
  · intro line hlinePiece hlineTotal
    obtain ⟨e, hline⟩ := Set.mem_iUnion.mp hlineTotal
    exact hslope e line hlinePiece hline
  · intro line hlinePiece hlineTotal
    obtain ⟨e, hline⟩ := Set.mem_iUnion.mp hlineTotal
    exact htimeNe e line hlinePiece hline
  · intro line hlinePiece hlineTotal
    obtain ⟨e, hline⟩ := Set.mem_iUnion.mp hlineTotal
    exact hgapUpper e line hlinePiece hline
  · intro line hlinePiece hlineTotal
    obtain ⟨e, hline⟩ := Set.mem_iUnion.mp hlineTotal
    exact hsegment e line hlinePiece hline

/-- A failure of the unclustered moving-center mass estimate is a genuine
four-dimensional physical-ball concentration.  This is the direction needed
by the boundary stopping: the moving secant centers themselves need not lie
in one slope cap, because their common outer probe is charged before any
direction clustering is attempted. -/
theorem moving_secant_mass_excess_forces_front_ball_excess
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (lines : ℕ → Set MarkedLine)
    (hlinesMeasurable : ∀ e, MeasurableSet (lines e))
    (hlinesDisjoint : Pairwise (fun e e' => Disjoint (lines e) (lines e')))
    (firstTime : MarkedLine → ℝ) (firstCenter : MarkedLine → E3)
    (outerTime : ℝ) (outerPoint : E4)
    (Rs R L delta : ℝ)
    (houterTime : outerPoint (3 : Fin 4) = outerTime)
    (hR : 0 ≤ R) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hscale : Rs + L * R < delta / 2)
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
    (threshold : ENNReal)
    (hexcess : threshold <
      ∑' e, (markedCarrierPieceLineProbability selector hmeasurable
        hvalid hselector piece : Measure MarkedLine) (lines e)) :
    ENNReal.ofReal (delta / 2) * threshold <
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball outerPoint delta) := by
  have hcharge :=
    tsum_markedCarrierPieceLineProbability_mul_half_of_moving_secant_crossing_le_front_ball
      selector hmeasurable hvalid hselector piece hpieceMeasurable
        hpieceCarrier hmass lines hlinesMeasurable hlinesDisjoint
        firstTime firstCenter outerTime outerPoint Rs R L delta houterTime
        hR hdelta hdeltaOne hscale hchart hfirst hslope htimeNe hgapUpper
        hsegment
  have hcoefficientZero : ENNReal.ofReal (delta / 2) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hcoefficientTop : ENNReal.ofReal (delta / 2) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hstrict :
      ENNReal.ofReal (delta / 2) * threshold <
        ENNReal.ofReal (delta / 2) *
          (∑' e, (markedCarrierPieceLineProbability selector hmeasurable
            hvalid hselector piece : Measure MarkedLine) (lines e)) := by
    simpa [mul_comm] using
      (ENNReal.mul_lt_mul_left hcoefficientZero hcoefficientTop hexcess)
  exact hstrict.trans_le hcharge

/-- The missing exponent in the moving-centre estimate is exactly the
physical crossing length.  If the ball radius is at least `kappa * R`, then
the factor `delta / 2` in the front-ball charge upgrades an `R^(3-zeta)`
vector-centre threshold to an `R^(4-zeta)` physical threshold.  This is only
the scale conversion; no clustering of the moving secant centres is used. -/
theorem rpow_four_threshold_lt_of_scale_three_front_charge
    (R delta kappa zeta : ℝ) (Q frontMass : ENNReal)
    (hR : 0 ≤ R) (hkappa : 0 ≤ kappa) (hzeta : zeta ≤ 3)
    (hscaleLower : kappa * R ≤ delta)
    (hcharge :
      ENNReal.ofReal (delta / 2) *
          (Q * (ENNReal.ofReal R).rpow (3 - zeta)) < frontMass) :
    ENNReal.ofReal (kappa / 2) * Q *
        (ENNReal.ofReal R).rpow (4 - zeta) < frontMass := by
  have hkappaHalf : 0 ≤ kappa / 2 := by positivity
  have hcoefficient :
      ENNReal.ofReal (kappa / 2) * ENNReal.ofReal R ≤
        ENNReal.ofReal (delta / 2) := by
    rw [← ENNReal.ofReal_mul hkappaHalf]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have hsplit :
      (ENNReal.ofReal R).rpow (4 - zeta) =
        ENNReal.ofReal R *
          (ENNReal.ofReal R).rpow (3 - zeta) := by
    rw [show 4 - zeta = 1 + (3 - zeta) by ring]
    calc
      (ENNReal.ofReal R).rpow (1 + (3 - zeta)) =
          (ENNReal.ofReal R).rpow 1 *
            (ENNReal.ofReal R).rpow (3 - zeta) := by
        exact ENNReal.rpow_add_of_nonneg 1 (3 - zeta)
          (by norm_num) (by linarith : 0 ≤ 3 - zeta)
      _ = ENNReal.ofReal R *
            (ENNReal.ofReal R).rpow (3 - zeta) := by simp
  calc
    ENNReal.ofReal (kappa / 2) * Q *
          (ENNReal.ofReal R).rpow (4 - zeta) =
        (ENNReal.ofReal (kappa / 2) * ENNReal.ofReal R) *
          (Q * (ENNReal.ofReal R).rpow (3 - zeta)) := by
            rw [hsplit]
            ac_rfl
    _ ≤ ENNReal.ofReal (delta / 2) *
          (Q * (ENNReal.ofReal R).rpow (3 - zeta)) := by gcongr
    _ < frontMass := hcharge

/-- Exact gate-facing form of the preceding two lemmas.  An unclustered
failure at the manuscript's three-dimensional vector-centre threshold
`Q * R^(3-zeta)` forces a four-dimensional front-ball excess of size
`(kappa/2) * Q * R^(4-zeta)` whenever `kappa * R ≤ delta`. -/
theorem moving_secant_rpow_mass_excess_forces_scale_four_front_ball_excess
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
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
        hvalid hselector piece : Measure MarkedLine) (lines e)) :
    ENNReal.ofReal (kappa / 2) * Q *
        (ENNReal.ofReal R).rpow (4 - zeta) <
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball outerPoint delta) := by
  apply rpow_four_threshold_lt_of_scale_three_front_charge
    R delta kappa zeta Q
      ((markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball outerPoint delta))
      hR hkappa hzeta hscaleLower
  exact moving_secant_mass_excess_forces_front_ball_excess
    selector hmeasurable hvalid hselector piece hpieceMeasurable
      hpieceCarrier hmass lines hlinesMeasurable hlinesDisjoint firstTime
      firstCenter outerTime outerPoint Rs R L delta houterTime hR hdelta
      hdeltaOne hscale hchart hfirst hslope htimeNe hgapUpper hsegment
      (Q * (ENNReal.ofReal R).rpow (3 - zeta)) hexcess

/-- The positive north-chart lift is two-Lipschitz from an arbitrary slope
center to the corresponding spherical direction. -/
theorem northGraphSlope_direction_to_center_bound
    (line : MarkedLine) (hvalid : IsValidLine line)
    (hpos : 0 < direction line (3 : Fin 4)) (a : E3) :
    dist (direction line) (northSlopeDirection a : E4) ≤
      2 * ‖northGraphSlope line - a‖ := by
  rw [← normalize_northSlopeLift line hvalid hpos]
  change dist
      (NormedSpace.normalize (northSlopeLift (northGraphSlope line)))
      (NormedSpace.normalize (northSlopeLift a)) ≤ _
  simpa [dist_eq_norm, northSlopeLift_sub_norm] using
    norm_normalize_sub_normalize_le_two_of_one_le
      (northSlopeLift (northGraphSlope line)) (northSlopeLift a)
      (northSlopeLift_norm_ge_one _) (northSlopeLift_norm_ge_one _)

/-- Clustered part of the varying-center problem.  Varying first-bush centers
cause no loss once their secant-vector centers lie in one ball.  Every
component then lies in one common spherical cap.  This hypothesis is not the
full moving-center Carleson gate: in that gate the secant center may vary
freely with the bush label. -/
theorem iUnion_source_subset_frontDirectionCap_of_vector_centers
    {ι : Type*}
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (source : ι → Set FrontParameterSpace)
    (firstTime : ι → ℝ) (firstCenter : ι → E3)
    (outerTime : ℝ) (outerCenter slopeCenter : E3)
    (Rs Rt g Rcenter eta : ℝ)
    (hsourcePos : ∀ e, ∀ z ∈ source e,
      0 < direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4))
    (hfirst : ∀ e, ∀ z ∈ source e,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            (firstTime e) - firstCenter e‖ ≤ Rs)
    (houter : ∀ e, ∀ z ∈ source e,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            outerTime - outerCenter‖ ≤ Rt)
    (hg : 0 < g)
    (hseparated : ∀ e, g ≤ |outerTime - firstTime e|)
    (hcenter : ∀ e,
      ‖(outerTime - firstTime e)⁻¹ •
          (outerCenter - firstCenter e) - slopeCenter‖ ≤ Rcenter)
    (heta : 0 < eta) :
    (⋃ e, source e) ⊆
      frontDirectionCap (northSlopeDirection slopeCenter)
        (2 * ((Rs + Rt) / g + Rcenter) + eta) := by
  intro z hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨e, hze⟩ := hz
  let line := selectorLine selector hmeasurable hvalid hselector z.1
  have hslopeSecant :
      ‖northGraphSlope line -
          (outerTime - firstTime e)⁻¹ •
            (outerCenter - firstCenter e)‖ ≤ (Rs + Rt) / g :=
    northGraphSlope_sub_probeSecant_le line (firstTime e) outerTime
      (firstCenter e) outerCenter Rs Rt g
      (hfirst e z hze) (houter e z hze) hg (hseparated e)
  have hslope : ‖northGraphSlope line - slopeCenter‖ ≤
      (Rs + Rt) / g + Rcenter := by
    calc
      ‖northGraphSlope line - slopeCenter‖ =
          ‖(northGraphSlope line -
              (outerTime - firstTime e)⁻¹ •
                (outerCenter - firstCenter e)) +
            ((outerTime - firstTime e)⁻¹ •
                (outerCenter - firstCenter e) - slopeCenter)‖ := by
        congr 1
        abel
      _ ≤
          ‖northGraphSlope line -
              (outerTime - firstTime e)⁻¹ •
                (outerCenter - firstCenter e)‖ +
            ‖(outerTime - firstTime e)⁻¹ •
                (outerCenter - firstCenter e) - slopeCenter‖ :=
        norm_add_le _ _
      _ ≤ (Rs + Rt) / g + Rcenter :=
        add_le_add hslopeSecant (hcenter e)
  have hdirection :
      dist (direction line) (northSlopeDirection slopeCenter : E4) ≤
        2 * ((Rs + Rt) / g + Rcenter) :=
    (northGraphSlope_direction_to_center_bound line
      (hvalid line line.property) (hsourcePos e z hze) slopeCenter).trans
        (mul_le_mul_of_nonneg_left hslope (by norm_num))
  change dist (z.1 : E4) (northSlopeDirection slopeCenter : E4) <
    2 * ((Rs + Rt) / g + Rcenter) + eta
  rw [← direction_selectorLine selector hmeasurable hvalid hselector z.1]
  exact hdirection.trans_lt (lt_add_of_pos_right _ heta)

/-- Coefficient-one finite *clustered* vector-center estimate.  The component
sources may have different first-bush centers and heights.  Once their
secant-vector centers occupy one ball and all components share one outer
physical probe, their disjoint union is charged by a single cap--fibre bound;
there is no factor equal to the number of bushes. -/
theorem HasFrontDirectionFibreBound.sum_measure_le_of_vector_centers
    {m : ℕ}
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {nu : Measure FrontParameterSpace} {Cfront : ENNReal}
    (hfront : HasFrontDirectionFibreBound selector hmeasurable hvalid
      hselector nu Cfront)
    (source : Fin m → Set FrontParameterSpace)
    (hsourceMeasurable : ∀ e, MeasurableSet (source e))
    (hsourceDisjoint : Pairwise (fun e e' ↦ Disjoint (source e) (source e')))
    (firstTime : Fin m → ℝ) (firstCenter : Fin m → E3)
    (outerTime : ℝ) (outerCenter slopeCenter : E3)
    (outerPoint : E4) (outerRadius : ℝ)
    (Rs Rt g Rcenter eta : ℝ)
    (hsourcePos : ∀ e, ∀ z ∈ source e,
      0 < direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4))
    (hfirst : ∀ e, ∀ z ∈ source e,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            (firstTime e) - firstCenter e‖ ≤ Rs)
    (houter : ∀ e, ∀ z ∈ source e,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            outerTime - outerCenter‖ ≤ Rt)
    (houterBall : ∀ e, source e ⊆
      (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
        Metric.ball outerPoint outerRadius)
    (hRs : 0 ≤ Rs) (hRt : 0 ≤ Rt)
    (hg : 0 < g)
    (hseparated : ∀ e, g ≤ |outerTime - firstTime e|)
    (hcenter : ∀ e,
      ‖(outerTime - firstTime e)⁻¹ •
          (outerCenter - firstCenter e) - slopeCenter‖ ≤ Rcenter)
    (hRcenter : 0 ≤ Rcenter) (heta : 0 < eta)
    (hcapOne : 2 * ((Rs + Rt) / g + Rcenter) + eta ≤ 1)
    (houterRadius : 0 ≤ outerRadius) :
    (∑ e, nu (source e)) ≤
      ENNReal.ofReal (2 * outerRadius) *
        (Cfront *
          (ENNReal.ofReal
            (2 * ((Rs + Rt) / g + Rcenter) + eta)) ^ 3) := by
  classical
  let totalSource : Set FrontParameterSpace := ⋃ e, source e
  have hdisjoint : PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin m))) source := by
    intro e _he e' _he' hne
    exact hsourceDisjoint hne
  have hsum : (∑ e, nu (source e)) = nu totalSource := by
    calc
      (∑ e, nu (source e)) =
          ∑ e ∈ (Finset.univ : Finset (Fin m)), nu (source e) := by simp
      _ = nu (⋃ e ∈ (Finset.univ : Finset (Fin m)), source e) :=
        (measure_biUnion_finset hdisjoint
          (fun e _he ↦ hsourceMeasurable e)).symm
      _ = nu totalSource := by simp [totalSource]
  rw [hsum]
  apply hfront totalSource (northSlopeDirection slopeCenter) outerPoint
    (2 * ((Rs + Rt) / g + Rcenter) + eta) outerRadius
  · exact iUnion_source_subset_frontDirectionCap_of_vector_centers
      selector hmeasurable hvalid hselector source firstTime firstCenter
        outerTime outerCenter slopeCenter Rs Rt g Rcenter eta hsourcePos
        hfirst houter hg hseparated hcenter heta
  · intro z hz
    simp only [totalSource, Set.mem_iUnion] at hz
    obtain ⟨e, hze⟩ := hz
    exact houterBall e hze
  · have hquotient : 0 ≤ (Rs + Rt) / g :=
      div_nonneg (add_nonneg hRs hRt) hg.le
    nlinarith
  · exact hcapOne
  · exact houterRadius

/-- Countable coefficient-one form of the clustered vector-center estimate.
It applies to one cluster of the infinite-progress boundary: countably many
disjoint bush components are first united, and the cap--fibre law is applied
once to their union.  Summing distinct moving-center clusters remains a
separate step. -/
theorem HasFrontDirectionFibreBound.tsum_measure_le_of_vector_centers
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {nu : Measure FrontParameterSpace} {Cfront : ENNReal}
    (hfront : HasFrontDirectionFibreBound selector hmeasurable hvalid
      hselector nu Cfront)
    (source : ℕ → Set FrontParameterSpace)
    (hsourceMeasurable : ∀ e, MeasurableSet (source e))
    (hsourceDisjoint : Pairwise (fun e e' ↦ Disjoint (source e) (source e')))
    (firstTime : ℕ → ℝ) (firstCenter : ℕ → E3)
    (outerTime : ℝ) (outerCenter slopeCenter : E3)
    (outerPoint : E4) (outerRadius : ℝ)
    (Rs Rt g Rcenter eta : ℝ)
    (hsourcePos : ∀ e, ∀ z ∈ source e,
      0 < direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4))
    (hfirst : ∀ e, ∀ z ∈ source e,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            (firstTime e) - firstCenter e‖ ≤ Rs)
    (houter : ∀ e, ∀ z ∈ source e,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            outerTime - outerCenter‖ ≤ Rt)
    (houterBall : ∀ e, source e ⊆
      (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
        Metric.ball outerPoint outerRadius)
    (hRs : 0 ≤ Rs) (hRt : 0 ≤ Rt)
    (hg : 0 < g)
    (hseparated : ∀ e, g ≤ |outerTime - firstTime e|)
    (hcenter : ∀ e,
      ‖(outerTime - firstTime e)⁻¹ •
          (outerCenter - firstCenter e) - slopeCenter‖ ≤ Rcenter)
    (hRcenter : 0 ≤ Rcenter) (heta : 0 < eta)
    (hcapOne : 2 * ((Rs + Rt) / g + Rcenter) + eta ≤ 1)
    (houterRadius : 0 ≤ outerRadius) :
    (∑' e, nu (source e)) ≤
      ENNReal.ofReal (2 * outerRadius) *
        (Cfront *
          (ENNReal.ofReal
            (2 * ((Rs + Rt) / g + Rcenter) + eta)) ^ 3) := by
  let totalSource : Set FrontParameterSpace := ⋃ e, source e
  have hsum : (∑' e, nu (source e)) = nu totalSource := by
    simpa [totalSource] using
      (measure_iUnion hsourceDisjoint hsourceMeasurable).symm
  rw [hsum]
  apply hfront totalSource (northSlopeDirection slopeCenter) outerPoint
    (2 * ((Rs + Rt) / g + Rcenter) + eta) outerRadius
  · exact iUnion_source_subset_frontDirectionCap_of_vector_centers
      selector hmeasurable hvalid hselector source firstTime firstCenter
        outerTime outerCenter slopeCenter Rs Rt g Rcenter eta hsourcePos
        hfirst houter hg hseparated hcenter heta
  · intro z hz
    simp only [totalSource, Set.mem_iUnion] at hz
    obtain ⟨e, hze⟩ := hz
    exact houterBall e hze
  · have hquotient : 0 ≤ (Rs + Rt) / g :=
      div_nonneg (add_nonneg hRs hRt) hg.le
    nlinarith
  · exact hcapOne
  · exact houterRadius

/-- On scales at most one, the fourth-power cap--fibre gain is stronger than
the subcubic exponent required by the vector-center Carleson gate. -/
theorem fourth_power_le_rpow_three_sub
    (R zeta : ℝ) (hR : 0 ≤ R) (hROne : R ≤ 1)
    (hzeta : 0 < zeta) (hzetaThree : zeta < 3) :
    (ENNReal.ofReal R) ^ 4 ≤
      (ENNReal.ofReal R).rpow (3 - zeta) := by
  have hbase : ENNReal.ofReal R ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hROne
  have hexponent : 3 - zeta ≤ (4 : ℝ) := by linarith
  have hfourth :
      (ENNReal.ofReal R) ^ 4 =
        (ENNReal.ofReal R).rpow (4 : ℝ) :=
    (ENNReal.rpow_natCast (ENNReal.ofReal R) 4).symm
  rw [hfourth]
  exact ENNReal.rpow_le_rpow_of_exponent_ge hbase hexponent

/-- Scale-normalized countable clustered vector-center estimate.  The raw
cap--fibre bound contributes one physical power and three directional powers.
For `R ≤ 1` this fourth power pays every requested exponent `3 - zeta`.
The constant is independent of the number of bush components. -/
theorem HasFrontDirectionFibreBound.tsum_measure_le_rpow_of_vector_centers
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {nu : Measure FrontParameterSpace} {Cfront : ENNReal}
    (hfront : HasFrontDirectionFibreBound selector hmeasurable hvalid
      hselector nu Cfront)
    (source : ℕ → Set FrontParameterSpace)
    (hsourceMeasurable : ∀ e, MeasurableSet (source e))
    (hsourceDisjoint : Pairwise (fun e e' ↦ Disjoint (source e) (source e')))
    (firstTime : ℕ → ℝ) (firstCenter : ℕ → E3)
    (outerTime : ℝ) (outerCenter slopeCenter : E3)
    (outerPoint : E4) (outerRadius : ℝ)
    (Rs Rt g Rcenter eta K R zeta : ℝ)
    (hsourcePos : ∀ e, ∀ z ∈ source e,
      0 < direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4))
    (hfirst : ∀ e, ∀ z ∈ source e,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            (firstTime e) - firstCenter e‖ ≤ Rs)
    (houter : ∀ e, ∀ z ∈ source e,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            outerTime - outerCenter‖ ≤ Rt)
    (houterBall : ∀ e, source e ⊆
      (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
        Metric.ball outerPoint outerRadius)
    (hRs : 0 ≤ Rs) (hRt : 0 ≤ Rt)
    (hg : 0 < g)
    (hseparated : ∀ e, g ≤ |outerTime - firstTime e|)
    (hcenter : ∀ e,
      ‖(outerTime - firstTime e)⁻¹ •
          (outerCenter - firstCenter e) - slopeCenter‖ ≤ Rcenter)
    (hRcenter : 0 ≤ Rcenter) (heta : 0 < eta)
    (hcapOne : 2 * ((Rs + Rt) / g + Rcenter) + eta ≤ 1)
    (houterRadius : 0 ≤ outerRadius)
    (houterScale : outerRadius ≤ R)
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hROne : R ≤ 1)
    (hcapScale : 2 * ((Rs + Rt) / g + Rcenter) + eta ≤ K * R)
    (hzeta : 0 < zeta) (hzetaThree : zeta < 3) :
    (∑' e, nu (source e)) ≤
      (2 * Cfront * (ENNReal.ofReal K) ^ 3) *
        (ENNReal.ofReal R).rpow (3 - zeta) := by
  have hraw := hfront.tsum_measure_le_of_vector_centers source
    hsourceMeasurable hsourceDisjoint firstTime firstCenter outerTime
    outerCenter slopeCenter outerPoint outerRadius Rs Rt g Rcenter eta
    hsourcePos hfirst houter houterBall hRs hRt hg hseparated hcenter
    hRcenter heta hcapOne houterRadius
  have houterOfReal :
      ENNReal.ofReal (2 * outerRadius) ≤ 2 * ENNReal.ofReal R := by
    calc
      ENNReal.ofReal (2 * outerRadius) ≤ ENNReal.ofReal (2 * R) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left houterScale (by norm_num))
      _ = 2 * ENNReal.ofReal R := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  have hcapNonneg : 0 ≤ 2 * ((Rs + Rt) / g + Rcenter) + eta := by
    have hquotient : 0 ≤ (Rs + Rt) / g :=
      div_nonneg (add_nonneg hRs hRt) hg.le
    nlinarith
  have hcapOfReal :
      ENNReal.ofReal (2 * ((Rs + Rt) / g + Rcenter) + eta) ≤
        ENNReal.ofReal K * ENNReal.ofReal R := by
    calc
      ENNReal.ofReal (2 * ((Rs + Rt) / g + Rcenter) + eta) ≤
          ENNReal.ofReal (K * R) := ENNReal.ofReal_le_ofReal hcapScale
      _ = ENNReal.ofReal K * ENNReal.ofReal R := by
        exact ENNReal.ofReal_mul hK
  have hfourth := fourth_power_le_rpow_three_sub R zeta hR hROne
    hzeta hzetaThree
  calc
    (∑' e, nu (source e)) ≤
        ENNReal.ofReal (2 * outerRadius) *
          (Cfront *
            (ENNReal.ofReal
              (2 * ((Rs + Rt) / g + Rcenter) + eta)) ^ 3) := hraw
    _ ≤ (2 * ENNReal.ofReal R) *
          (Cfront * (ENNReal.ofReal K * ENNReal.ofReal R) ^ 3) := by
        gcongr
    _ = (2 * Cfront * (ENNReal.ofReal K) ^ 3) *
          (ENNReal.ofReal R) ^ 4 := by
        ring
    _ ≤ (2 * Cfront * (ENNReal.ofReal K) ^ 3) *
          (ENNReal.ofReal R).rpow (3 - zeta) := by
        gcongr

end StickyKakeya4
