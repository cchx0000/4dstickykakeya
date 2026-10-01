import Theorems.Thm_StickyKakeya4_common_height_collision_time_routing
import Theorems.Thm_StickyKakeya4_four_probe_cauchy_extraction

open scoped RealInnerProductSpace

noncomputable section

namespace StickyKakeya4

/-- The analytic collision time on one oriented edge of a four-cycle. -/
def fourCycleCollisionTime
    (line : Fin 4 → MarkedLine) (i : Fin 4) : ℝ :=
  collisionTime (fourCycleEdgeSecant line i).1
    (fourCycleEdgeSecant line i).2

/-- A separated analytic four-cycle packet together with the common physical
height from which its collision-time control was obtained.  Retaining this
height is what makes the packet coherent enough for the next scale; the older
`NormalizedMarkedFourCyclePacket` deliberately forgets it. -/
structure CommonHeightAnalyticFourCyclePacket
    (selector : Set MarkedLine) (timeGap residualBound : ℝ) where
  line : Fin 4 → MarkedLine
  lineInjective : Function.Injective line
  line_mem_selector : ∀ i, line i ∈ selector
  chartNonzero : ∀ i, direction (line i) (3 : Fin 4) ≠ 0
  commonHeight : ℝ
  edgeSlopeNonzero : ∀ i, (fourCycleEdgeSecant line i).1 ≠ 0
  commonHeightResidual : ∀ i,
    ‖(fourCycleEdgeSecant line i).2 +
        commonHeight • (fourCycleEdgeSecant line i).1‖ ≤ residualBound
  timeSeparated : ∀ i j, i ≠ j →
    timeGap ≤
      |fourCycleCollisionTime line i - fourCycleCollisionTime line j|

/-- Forget the common-height witness after converting the minimizing contact
residual to the normalized Maslov residual. -/
noncomputable def CommonHeightAnalyticFourCyclePacket.toNormalized
    {selector : Set MarkedLine} {timeGap residualBound : ℝ}
    (packet : CommonHeightAnalyticFourCyclePacket selector timeGap
      residualBound) :
    NormalizedMarkedFourCyclePacket selector timeGap residualBound where
  line := packet.line
  lineInjective := packet.lineInjective
  line_mem_selector := packet.line_mem_selector
  chartNonzero := packet.chartNonzero
  approxTime := fourCycleCollisionTime packet.line
  timeSeparated := packet.timeSeparated
  physicalCycleResidual := fun i ↦ by
    apply normalized_fourCycleResidual_le
    exact (collisionResidual_norm_le_contact_norm
      (fourCycleEdgeSecant packet.line i).1
      (fourCycleEdgeSecant packet.line i).2
      (packet.edgeSlopeNonzero i) packet.commonHeight).trans
        (packet.commonHeightResidual i)

private theorem four_time_separation_from_six
    (time : Fin 4 → ℝ) (gap : ℝ)
    (hsep : gap < |time 0 - time 1| ∧
      gap < |time 0 - time 2| ∧
      gap < |time 0 - time 3| ∧
      gap < |time 1 - time 2| ∧
      gap < |time 1 - time 3| ∧
      gap < |time 2 - time 3|) :
    ∀ i j, i ≠ j → gap ≤ |time i - time j| := by
  obtain ⟨h₀₁, h₀₂, h₀₃, h₁₂, h₁₃, h₂₃⟩ := hsep
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact le_of_lt h₀₁
  · exact le_of_lt h₀₂
  · exact le_of_lt h₀₃
  · calc
      gap ≤ |time 0 - time 1| := le_of_lt h₀₁
      _ = |time 1 - time 0| := abs_sub_comm _ _
  · exact (hij rfl).elim
  · exact le_of_lt h₁₂
  · exact le_of_lt h₁₃
  · calc
      gap ≤ |time 0 - time 2| := le_of_lt h₀₂
      _ = |time 2 - time 0| := abs_sub_comm _ _
  · calc
      gap ≤ |time 1 - time 2| := le_of_lt h₁₂
      _ = |time 2 - time 1| := abs_sub_comm _ _
  · exact (hij rfl).elim
  · exact le_of_lt h₂₃
  · calc
      gap ≤ |time 0 - time 3| := le_of_lt h₀₃
      _ = |time 3 - time 0| := abs_sub_comm _ _
  · calc
      gap ≤ |time 1 - time 3| := le_of_lt h₁₃
      _ = |time 3 - time 1| := abs_sub_comm _ _
  · calc
      gap ≤ |time 2 - time 3| := le_of_lt h₂₃
      _ = |time 3 - time 2| := abs_sub_comm _ _
  · exact (hij rfl).elim

/-- Pure four-line common-height dichotomy with all coherence data retained.
The first branch remembers the comparison height; the second branch records
the same analytic collision times in three literal packets. -/
theorem commonHeightAnalyticFourCyclePacket_or_threePackets
    (selector : Set MarkedLine) (line : Fin 4 → MarkedLine)
    (commonHeight timeGap residualBound : ℝ)
    (hlineInjective : Function.Injective line)
    (hlineSelector : ∀ i, line i ∈ selector)
    (hchart : ∀ i, direction (line i) (3 : Fin 4) ≠ 0)
    (hedge : ∀ i, (fourCycleEdgeSecant line i).1 ≠ 0)
    (hcommon : ∀ i,
      ‖(fourCycleEdgeSecant line i).2 +
          commonHeight • (fourCycleEdgeSecant line i).1‖ ≤ residualBound) :
    Nonempty (CommonHeightAnalyticFourCyclePacket selector timeGap
      residualBound) ∨
      ∃ approxTime : Fin 4 → ℝ,
        approxTime = fourCycleCollisionTime line ∧
        (∀ i,
          ‖(fourCycleEdgeSecant line i).2 +
              approxTime i • (fourCycleEdgeSecant line i).1‖ ≤
            residualBound) ∧
        FourTimesLieInThreePackets approxTime timeGap := by
  let time : Fin 4 → ℝ := fourCycleCollisionTime line
  have hmin : ∀ i,
      ‖(fourCycleEdgeSecant line i).2 +
          time i • (fourCycleEdgeSecant line i).1‖ ≤ residualBound := by
    intro i
    exact (collisionResidual_norm_le_contact_norm
      (fourCycleEdgeSecant line i).1
      (fourCycleEdgeSecant line i).2 (hedge i) commonHeight).trans
        (hcommon i)
  rcases four_reeb_times_separated_or_three_packets
      (time 0) (time 1) (time 2) (time 3) timeGap with hsep | hthree
  · left
    exact ⟨⟨line, hlineInjective, hlineSelector, hchart, commonHeight,
      hedge, hcommon, four_time_separation_from_six time timeGap hsep⟩⟩
  · right
    refine ⟨time, rfl, hmin, ?_⟩
    obtain ⟨t₀, t₁, t₂, h₀, h₁, h₂, h₃⟩ := hthree
    exact ⟨t₀, t₁, t₂, fun i ↦ by fin_cases i <;> assumption⟩

/-- The pointwise source cycle produces the coherent, common-height version
of the analytic collision packet.  In particular, the first branch now
retains exactly the datum needed to derive interscale collision-time motion. -/
theorem sourcePointCommonHeightCycle_has_coherentCollisionTimePacket_or_threePackets
    {n : ℕ} {R : FiniteScaleSource n} {x : E4}
    {selector : Set MarkedLine} {timeGap eta residualBound : ℝ}
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (cycle : SourcePointFourMarkedCommonHeightCycle
      R x selector timeGap eta)
    (hpos : ∀ k, 0 < direction (R.line (cycle.index k)) (3 : Fin 4))
    (hbound : ∀ i,
      (|(direction (R.line (cycle.index i)) (3 : Fin 4))⁻¹| +
          |(direction
            (R.line (cycle.index (fourCycleNext i))) (3 : Fin 4))⁻¹| + 2) *
        (R.thickness + eta) ≤ residualBound) :
    Nonempty (CommonHeightAnalyticFourCyclePacket selector timeGap
      residualBound) ∨
      ∃ (line : Fin 4 → MarkedLine) (approxTime : Fin 4 → ℝ),
        Function.Injective line ∧
        (∀ i, line i ∈ selector) ∧
        (∀ i, direction (line i) (3 : Fin 4) ≠ 0) ∧
        (∀ i,
          ‖(fourCycleEdgeSecant line i).2 +
              approxTime i • (fourCycleEdgeSecant line i).1‖ ≤ residualBound) ∧
        FourTimesLieInThreePackets approxTime timeGap := by
  let line : Fin 4 → MarkedLine := fun k ↦ R.line (cycle.index k)
  have hlineInjective : Function.Injective line :=
    R.line_injective.comp cycle.index_injective
  have hlineSelector : ∀ i, line i ∈ selector := cycle.line_mem_selector
  have hchart : ∀ i, direction (line i) (3 : Fin 4) ≠ 0 :=
    fun i ↦ (hpos i).ne'
  have hedge : ∀ i, (fourCycleEdgeSecant line i).1 ≠ 0 := by
    intro i
    have hnext : fourCycleNext i ≠ i := by
      fin_cases i <;> decide
    have hlines : line (fourCycleNext i) ≠ line i := by
      intro heq
      exact hnext (hlineInjective heq)
    exact sub_ne_zero.mpr
      (northGraphSlope_ne_of_selectorLines_ne hvalid hselector
        (hlineSelector (fourCycleNext i)) (hlineSelector i)
        (hpos (fourCycleNext i)) (hpos i) hlines)
  have hcommon : ∀ i,
      ‖(fourCycleEdgeSecant line i).2 +
          x (3 : Fin 4) • (fourCycleEdgeSecant line i).1‖ ≤ residualBound := by
    intro i
    exact (le_of_lt (by simpa [line] using cycle.commonHeightResidual i)).trans
      (hbound i)
  rcases commonHeightAnalyticFourCyclePacket_or_threePackets
      selector line (x (3 : Fin 4)) timeGap residualBound
      hlineInjective hlineSelector hchart hedge hcommon with hpacket | hthree
  · exact Or.inl hpacket
  · obtain ⟨approxTime, _htime, hresidual, hpackets⟩ := hthree
    exact Or.inr ⟨line, approxTime, hlineInjective, hlineSelector,
      hchart, hresidual, hpackets⟩

/-- Coherence-preserving pointwise stopping output.  Compared with
`SourcePointCollisionTimeOrAffineThreePacketAlternative`, the four-probe
branch retains its common physical height instead of forgetting it. -/
def SourcePointCoherentCollisionTimeOrAffineThreePacketAlternative {n : ℕ}
    (R : FiniteScaleSource n) (x : E4) (selector : Set MarkedLine)
    (timeGap eta : ℝ) (current : ENNReal) : Prop :=
  Nonempty (CommonHeightAnalyticFourCyclePacket selector timeGap
      (6 * (R.thickness + eta))) ∨
    (∃ (line : Fin 4 → MarkedLine) (approxTime : Fin 4 → ℝ),
      Function.Injective line ∧
      (∀ i, line i ∈ selector) ∧
      (∀ i, direction (line i) (3 : Fin 4) ≠ 0) ∧
      (∀ i,
        ‖(fourCycleEdgeSecant line i).2 +
            approxTime i • (fourCycleEdgeSecant line i).1‖ ≤
          6 * (R.thickness + eta)) ∧
      FourTimesLieInThreePackets approxTime timeGap) ∨
    ∃ a b c, ∃ removed continuing : ENNReal,
      removed = current * ENNReal.ofReal
        (finiteThreePacketsMass (sourcePointNormalizedWeight R x)
          R.fibreMark timeGap a b c) ∧
      continuing = current * ENNReal.ofReal
        (finiteOutsideThreePacketsMass (sourcePointNormalizedWeight R x)
          R.fibreMark timeGap a b c) ∧
      current = removed + continuing ∧
      current ≤ removed + removed

/-- Upgrade the original common-height/affine-mark stopping route without
discarding the common height in the analytic four-probe branch. -/
theorem sourcePointContactCycleOrThreePacket_to_coherentCollisionTime_or_affineThreePacket
    {n : ℕ} {R : FiniteScaleSource n} {x : E4}
    {selector : Set MarkedLine} {timeGap eta : ℝ} {current : ENNReal}
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hnorth : ∀ i, (1 / 2 : ℝ) ≤
      direction (R.line i) (3 : Fin 4))
    (hscale : 0 ≤ R.thickness + eta)
    (hroute : SourcePointContactCycleOrThreePacketAlternative
      R x selector timeGap eta current) :
    SourcePointCoherentCollisionTimeOrAffineThreePacketAlternative
      R x selector timeGap eta current := by
  unfold SourcePointContactCycleOrThreePacketAlternative at hroute
  unfold SourcePointCoherentCollisionTimeOrAffineThreePacketAlternative
  rcases hroute with hcycle | hthree
  · obtain ⟨cycle⟩ := hcycle
    have hpos : ∀ k,
        0 < direction (R.line (cycle.index k)) (3 : Fin 4) := by
      intro k
      exact lt_of_lt_of_le (by norm_num) (hnorth (cycle.index k))
    have hinv : ∀ k,
        |(direction (R.line (cycle.index k)) (3 : Fin 4))⁻¹| ≤ 2 := by
      intro k
      have hkpos := hpos k
      rw [abs_of_pos (inv_pos.mpr hkpos), inv_eq_one_div]
      exact (div_le_iff₀ hkpos).2 (by nlinarith [hnorth (cycle.index k)])
    have hbound : ∀ i,
        (|(direction (R.line (cycle.index i)) (3 : Fin 4))⁻¹| +
            |(direction
              (R.line (cycle.index (fourCycleNext i))) (3 : Fin 4))⁻¹| + 2) *
          (R.thickness + eta) ≤ 6 * (R.thickness + eta) := by
      intro i
      apply mul_le_mul_of_nonneg_right _ hscale
      nlinarith [hinv i, hinv (fourCycleNext i)]
    rcases
        sourcePointCommonHeightCycle_has_coherentCollisionTimePacket_or_threePackets
          hvalid hselector cycle hpos hbound with hpacket | hcollisionThree
    · exact Or.inl hpacket
    · exact Or.inr (Or.inl hcollisionThree)
  · exact Or.inr (Or.inr hthree)

/-- Two approximate collisions, possibly for different secants, have nearby
analytic collision times whenever their comparison heights are nearby and
both slope secants stay quantitatively nonzero.  No continuity assumption on
`collisionTime` is used: this follows directly from the exact collision
identity at the two comparison heights. -/
theorem collisionTime_dist_le_of_common_height_returns
    (α β α' β' : E3) (s s' R R' τ : ℝ)
    (hα : α ≠ 0) (hα' : α' ≠ 0)
    (hR : ‖β + s • α‖ ≤ R) (hR' : ‖β' + s' • α'‖ ≤ R')
    (hRnonneg : 0 ≤ R) (hR'nonneg : 0 ≤ R')
    (hτ : 0 < τ) (hαlower : τ ≤ ‖α‖) (hα'lower : τ ≤ ‖α'‖) :
    dist (collisionTime α β) (collisionTime α' β') ≤
      R / τ + dist s s' + R' / τ := by
  obtain ⟨htime, _⟩ := collision_time_local_and_residual_bound
    α β hα s R τ hR hRnonneg hτ hαlower
  obtain ⟨htime', _⟩ := collision_time_local_and_residual_bound
    α' β' hα' s' R' τ hR' hR'nonneg hτ hα'lower
  calc
    dist (collisionTime α β) (collisionTime α' β') ≤
        dist (collisionTime α β) s +
          dist s (collisionTime α' β') := dist_triangle _ _ _
    _ ≤ dist (collisionTime α β) s +
          (dist s s' + dist s' (collisionTime α' β')) :=
      add_le_add (le_refl _)
        (dist_triangle s s' (collisionTime α' β'))
    _ ≤ R / τ + (dist s s' + R' / τ) := by
      gcongr
      · simpa [Real.dist_eq] using htime
      · simpa [Real.dist_eq, abs_sub_comm] using htime'
    _ = R / τ + dist s s' + R' / τ := by ring

/-- Uniform noncollapse of the anchored horizontal frame controls every
actual cyclic slope secant from below.  This is the missing conversion from
the Maslov tower's matrix condition to the denominator bound required by the
analytic collision time. -/
theorem fourCycleEdgeSecant_norm_ge_of_horizontalNoncollapse
    (line : Fin 4 → MarkedLine) (i : Fin 4) (kappa : ℝ)
    (hnoncollapse : ∀ c : E3,
      kappa * ‖c‖ ≤
        ‖horizontalFrameVector (anchoredCycleA line) c‖) :
    kappa ≤ ‖(fourCycleEdgeSecant line i).1‖ := by
  have hframe := congrArg Prod.fst
    (anchoredCycleFrame_coeff_eq_normalized_edge line i)
  have hnormalized :
      horizontalFrameVector (anchoredCycleA line) (fourCycleCoeff i) =
        ‖rawFourCycleCoeff i‖⁻¹ • (fourCycleEdgeSecant line i).1 := by
    simpa [horizontalFrameVector, matrixVectorE3] using hframe
  have hnon := hnoncollapse (fourCycleCoeff i)
  rw [fourCycleCoeff_norm, mul_one, hnormalized, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)] at hnon
  calc
    kappa ≤ ‖rawFourCycleCoeff i‖⁻¹ *
        ‖(fourCycleEdgeSecant line i).1‖ := hnon
    _ ≤ 1 * ‖(fourCycleEdgeSecant line i).1‖ :=
      mul_le_mul_of_nonneg_right (inv_norm_rawFourCycleCoeff_le_one i)
        (norm_nonneg _)
    _ = ‖(fourCycleEdgeSecant line i).1‖ := one_mul _

/-- Common-height four-cycle returns automatically provide the `motionTime`
estimate of the compactness tower in its uniformly noncollapsed branch.  The
bound uses the genuine analytic collision times on the two cycles; affine
fibre marks do not occur in this statement. -/
theorem fourCycleCollisionTime_motion_of_noncollapsed_commonHeight_returns
    (line line' : Fin 4 → MarkedLine)
    (s s' R R' kappa : ℝ)
    (hR : 0 ≤ R) (hR' : 0 ≤ R') (hkappa : 0 < kappa)
    (hnoncollapse : ∀ c : E3,
      kappa * ‖c‖ ≤
        ‖horizontalFrameVector (anchoredCycleA line) c‖)
    (hnoncollapse' : ∀ c : E3,
      kappa * ‖c‖ ≤
        ‖horizontalFrameVector (anchoredCycleA line') c‖)
    (hreturn : ∀ i,
      ‖(fourCycleEdgeSecant line i).2 +
          s • (fourCycleEdgeSecant line i).1‖ ≤ R)
    (hreturn' : ∀ i,
      ‖(fourCycleEdgeSecant line' i).2 +
          s' • (fourCycleEdgeSecant line' i).1‖ ≤ R') :
    ∀ i, dist (fourCycleCollisionTime line i)
        (fourCycleCollisionTime line' i) ≤
      R / kappa + dist s s' + R' / kappa := by
  intro i
  have hlower := fourCycleEdgeSecant_norm_ge_of_horizontalNoncollapse
    line i kappa hnoncollapse
  have hlower' := fourCycleEdgeSecant_norm_ge_of_horizontalNoncollapse
    line' i kappa hnoncollapse'
  have hne : (fourCycleEdgeSecant line i).1 ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (hkappa.trans_le hlower))
  have hne' : (fourCycleEdgeSecant line' i).1 ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (hkappa.trans_le hlower'))
  exact collisionTime_dist_le_of_common_height_returns
    (fourCycleEdgeSecant line i).1 (fourCycleEdgeSecant line i).2
    (fourCycleEdgeSecant line' i).1 (fourCycleEdgeSecant line' i).2
    s s' R R' kappa hne hne' (hreturn i) (hreturn' i)
    hR hR' hkappa hlower hlower'

end StickyKakeya4
