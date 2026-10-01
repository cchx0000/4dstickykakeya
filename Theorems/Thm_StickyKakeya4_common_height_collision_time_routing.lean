import Theorems.Thm_StickyKakeya4_source_point_contact_cycle_routing
import Theorems.Thm_StickyKakeya4_actual_source_collision_packet
import Theorems.Thm_StickyKakeya4_front_two_probe_direction_firewall

open Set

noncomputable section

namespace StickyKakeya4

/-- Two lines of a direction selector with the same oriented direction are
literally the same marked line. -/
theorem selectorLine_eq_of_direction_eq
    {selector : Set MarkedLine}
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    {line line' : MarkedLine}
    (hline : line ∈ selector) (hline' : line' ∈ selector)
    (hdir : direction line = direction line') :
    line = line' := by
  obtain ⟨chosen, _hchosen, hunique⟩ :=
    hselector (direction line) (hvalid line hline).1
  exact (hunique line ⟨hline, rfl⟩).trans
    (hunique line' ⟨hline', hdir.symm⟩).symm

/-- Distinct selector lines in the positive north chart have distinct graph
slopes.  This is the nondegeneracy needed to use the analytic collision time
on every edge. -/
theorem northGraphSlope_ne_of_selectorLines_ne
    {selector : Set MarkedLine}
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    {line line' : MarkedLine}
    (hline : line ∈ selector) (hline' : line' ∈ selector)
    (hpos : 0 < direction line (3 : Fin 4))
    (hpos' : 0 < direction line' (3 : Fin 4))
    (hne : line ≠ line') :
    northGraphSlope line ≠ northGraphSlope line' := by
  intro hslope
  have hdir : direction line = direction line' := by
    rw [← normalize_northSlopeLift line (hvalid line hline) hpos,
      ← normalize_northSlopeLift line' (hvalid line' hline') hpos']
    rw [hslope]
  exact hne (selectorLine_eq_of_direction_eq hvalid hselector
    hline hline' hdir)

/-- At the minimizing collision time the contact residual is no larger than
at any prescribed comparison height.  This is the monotone part of the exact
collision identity and requires only a nonzero slope secant. -/
theorem collisionResidual_norm_le_contact_norm
    (alpha beta : E3) (halpha : alpha ≠ 0) (s : ℝ) :
    ‖collisionResidual alpha beta‖ ≤ ‖beta + s • alpha‖ := by
  have hid := exact_collision_identity alpha beta halpha s
  have hterm : 0 ≤ ‖alpha‖ ^ 2 * |s - collisionTime alpha beta| ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith [norm_nonneg (collisionResidual alpha beta),
    norm_nonneg (beta + s • alpha)]

/-- A common-height cycle of four actual selector lines has an honest
collision-time output.  The times are the analytic minimizers of the four
edge contact residuals, not the affine fibre marks.  They either form the
separated four-probe packet consumed by the Maslov tower, or lie in three
literal collision-time packets.

The caller supplies only a common uniform residual bound; the pointwise
cycle already contains the sharper edge-dependent bounds. -/
theorem sourcePointCommonHeightCycle_has_collisionTime_packet_or_threePackets
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
    Nonempty (NormalizedMarkedFourCyclePacket selector timeGap residualBound) ∨
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
  have hchartNonzero : ∀ i, direction (line i) (3 : Fin 4) ≠ 0 :=
    fun i ↦ (hpos i).ne'
  have hedgeNonzero : ∀ i, (fourCycleEdgeSecant line i).1 ≠ 0 := by
    intro i
    have hnext : fourCycleNext i ≠ i := by
      fin_cases i <;> decide
    have hlines : line (fourCycleNext i) ≠ line i := by
      intro heq
      exact hnext (hlineInjective heq)
    have hslope := northGraphSlope_ne_of_selectorLines_ne hvalid hselector
      (hlineSelector (fourCycleNext i)) (hlineSelector i)
      (hpos (fourCycleNext i)) (hpos i) hlines
    exact sub_ne_zero.mpr hslope
  let approxTime : Fin 4 → ℝ := fun i ↦
    collisionTime (fourCycleEdgeSecant line i).1
      (fourCycleEdgeSecant line i).2
  have hresidual : ∀ i,
      ‖(fourCycleEdgeSecant line i).2 +
          approxTime i • (fourCycleEdgeSecant line i).1‖ ≤ residualBound := by
    intro i
    have hmin := collisionResidual_norm_le_contact_norm
      (fourCycleEdgeSecant line i).1 (fourCycleEdgeSecant line i).2
      (hedgeNonzero i) (x (3 : Fin 4))
    have hcommon :
        ‖(fourCycleEdgeSecant line i).2 +
            x (3 : Fin 4) • (fourCycleEdgeSecant line i).1‖ <
          (|(direction (R.line (cycle.index i)) (3 : Fin 4))⁻¹| +
              |(direction
                (R.line (cycle.index (fourCycleNext i))) (3 : Fin 4))⁻¹| + 2) *
            (R.thickness + eta) := by
      simpa [line] using cycle.commonHeightResidual i
    calc
      ‖(fourCycleEdgeSecant line i).2 +
          approxTime i • (fourCycleEdgeSecant line i).1‖ =
          ‖collisionResidual (fourCycleEdgeSecant line i).1
            (fourCycleEdgeSecant line i).2‖ := by
              rfl
      _ ≤ ‖(fourCycleEdgeSecant line i).2 +
          x (3 : Fin 4) • (fourCycleEdgeSecant line i).1‖ := hmin
      _ ≤ residualBound := (le_of_lt hcommon).trans (hbound i)
  rcases four_reeb_times_separated_or_three_packets
      (approxTime 0) (approxTime 1) (approxTime 2) (approxTime 3)
      timeGap with hsep | hthree
  · left
    refine ⟨⟨line, hlineInjective, hlineSelector, hchartNonzero,
      approxTime, ?_, ?_⟩⟩
    · intro i j hij
      obtain ⟨h₀₁, h₀₂, h₀₃, h₁₂, h₁₃, h₂₃⟩ := hsep
      have h₀₁' := le_of_lt h₀₁
      have h₀₂' := le_of_lt h₀₂
      have h₀₃' := le_of_lt h₀₃
      have h₁₂' := le_of_lt h₁₂
      have h₁₃' := le_of_lt h₁₃
      have h₂₃' := le_of_lt h₂₃
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact h₀₁'
      · exact h₀₂'
      · exact h₀₃'
      · calc
          timeGap ≤ |approxTime 0 - approxTime 1| := h₀₁'
          _ = |approxTime 1 - approxTime 0| := abs_sub_comm _ _
      · exact (hij rfl).elim
      · exact h₁₂'
      · exact h₁₃'
      · calc
          timeGap ≤ |approxTime 0 - approxTime 2| := h₀₂'
          _ = |approxTime 2 - approxTime 0| := abs_sub_comm _ _
      · calc
          timeGap ≤ |approxTime 1 - approxTime 2| := h₁₂'
          _ = |approxTime 2 - approxTime 1| := abs_sub_comm _ _
      · exact (hij rfl).elim
      · exact h₂₃'
      · calc
          timeGap ≤ |approxTime 0 - approxTime 3| := h₀₃'
          _ = |approxTime 3 - approxTime 0| := abs_sub_comm _ _
      · calc
          timeGap ≤ |approxTime 1 - approxTime 3| := h₁₃'
          _ = |approxTime 3 - approxTime 1| := abs_sub_comm _ _
      · calc
          timeGap ≤ |approxTime 2 - approxTime 3| := h₂₃'
          _ = |approxTime 3 - approxTime 2| := abs_sub_comm _ _
      · exact (hij rfl).elim
    · intro i
      exact normalized_fourCycleResidual_le i _ residualBound (hresidual i)
  · right
    refine ⟨line, approxTime, hlineInjective, hlineSelector,
      hchartNonzero, hresidual, ?_⟩
    obtain ⟨t₀, t₁, t₂, h₀, h₁, h₂, h₃⟩ := hthree
    refine ⟨t₀, t₁, t₂, ?_⟩
    intro i
    fin_cases i <;> assumption

/-- Honest three-way output after combining the pointwise weighted stopping
with analytic collision times.  The first two branches use edge collision
times.  The last branch deliberately retains affine fibre marks and its exact
coefficient-one mass split; the two kinds of labels are not identified. -/
def SourcePointCollisionTimeOrAffineThreePacketAlternative {n : ℕ}
    (R : FiniteScaleSource n) (x : E4) (selector : Set MarkedLine)
    (timeGap eta : ℝ) (current : ENNReal) : Prop :=
  Nonempty (NormalizedMarkedFourCyclePacket selector timeGap
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

/-- Upgrade the honest common-height/affine-packet route to the collision-time
trichotomy on a uniformly positive north chart.  The constant six is exactly
`2 + 2 + 2`: two inverse chart factors and the two fixed residual units. -/
theorem sourcePointContactCycleOrThreePacket_to_collisionTime_or_affineThreePacket
    {n : ℕ} {R : FiniteScaleSource n} {x : E4}
    {selector : Set MarkedLine} {timeGap eta : ℝ} {current : ENNReal}
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hnorth : ∀ i, (1 / 2 : ℝ) ≤
      direction (R.line i) (3 : Fin 4))
    (hscale : 0 ≤ R.thickness + eta)
    (hroute : SourcePointContactCycleOrThreePacketAlternative
      R x selector timeGap eta current) :
    SourcePointCollisionTimeOrAffineThreePacketAlternative
      R x selector timeGap eta current := by
  unfold SourcePointContactCycleOrThreePacketAlternative at hroute
  unfold SourcePointCollisionTimeOrAffineThreePacketAlternative
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
      rw [abs_of_pos (inv_pos.mpr hkpos)]
      rw [inv_eq_one_div]
      exact (div_le_iff₀ hkpos).2 (by
        nlinarith [hnorth (cycle.index k)])
    have hbound : ∀ i,
        (|(direction (R.line (cycle.index i)) (3 : Fin 4))⁻¹| +
            |(direction
              (R.line (cycle.index (fourCycleNext i))) (3 : Fin 4))⁻¹| + 2) *
          (R.thickness + eta) ≤ 6 * (R.thickness + eta) := by
      intro i
      apply mul_le_mul_of_nonneg_right _ hscale
      nlinarith [hinv i, hinv (fourCycleNext i)]
    rcases sourcePointCommonHeightCycle_has_collisionTime_packet_or_threePackets
        hvalid hselector cycle hpos hbound with hpacket | hcollisionThree
    · exact Or.inl hpacket
    · exact Or.inr (Or.inl hcollisionThree)
  · exact Or.inr (Or.inr hthree)

end StickyKakeya4
