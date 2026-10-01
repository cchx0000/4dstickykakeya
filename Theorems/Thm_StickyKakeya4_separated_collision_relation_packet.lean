import Theorems.Thm_StickyKakeya4_dense_relation_marked_four_cycle

open Set

noncomputable section

namespace StickyKakeya4

/-- The four left-to-right bipartite relation edges associated with the
cyclic marked-line order `left₀, right₀, left₁, right₁`. -/
def markedCycleRelationEdge (line : Fin 4 → MarkedLine) :
    Fin 4 → (MarkedLine × MarkedLine) :=
  ![(line 0, line 1), (line 2, line 1),
    (line 2, line 3), (line 0, line 3)]

/-- Contact residual norm of an oriented marked-line pair. -/
def markedPairContactResidualNorm
    (pair : MarkedLine × MarkedLine) (time : ℝ) : ℝ :=
  ‖(northGraphIntercept pair.2 - northGraphIntercept pair.1) +
      time • (northGraphSlope pair.2 - northGraphSlope pair.1)‖

theorem markedPairContactResidualNorm_swap
    (line line' : MarkedLine) (time : ℝ) :
    markedPairContactResidualNorm (line, line') time =
      markedPairContactResidualNorm (line', line) time := by
  have hvec :
      (northGraphIntercept line - northGraphIntercept line') +
          time • (northGraphSlope line - northGraphSlope line') =
        -((northGraphIntercept line' - northGraphIntercept line) +
          time • (northGraphSlope line' - northGraphSlope line)) := by
    module
  rw [markedPairContactResidualNorm, markedPairContactResidualNorm, hvec,
    norm_neg]

/-- The four relation edges are distinct whenever the four marked lines are
pairwise distinct. -/
theorem markedCycleRelationEdge_injective
    {line : Fin 4 → MarkedLine} (hline : Function.Injective line) :
    Function.Injective (markedCycleRelationEdge line) := by
  have h02 : line 0 ≠ line 2 := by
    intro h
    have hindex : (0 : Fin 4) = 2 := hline h
    have : (0 : ℕ) = 2 := congrArg Fin.val hindex
    norm_num at this
  have h13 : line 1 ≠ line 3 := by
    intro h
    have hindex : (1 : Fin 4) = 3 := hline h
    have : (1 : ℕ) = 3 := congrArg Fin.val hindex
    norm_num at this
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [markedCycleRelationEdge, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue] at hij ⊢ <;>
    simp_all

/-- A time label on relation edges induces four labels on the selected
cycle. -/
def markedCycleRelationTime
    (edgeTime : (MarkedLine × MarkedLine) → ℝ)
    (line : Fin 4 → MarkedLine) (i : Fin 4) : ℝ :=
  edgeTime (markedCycleRelationEdge line i)

/-- A dense physical collision relation with separated edge labels produces
one marked four-cycle packet carrying exactly the fields needed at a return
tower node, except for the horizontal noncollapse estimate.  Both residual
orientations are stated only to make the cyclic readback literal; they are
equivalent by `markedPairContactResidualNorm_swap`. -/
theorem dense_bipartite_has_separated_marked_four_cycle_packet
    (selector : Set MarkedLine)
    (X Y : Finset MarkedLine) (hXY : Disjoint X Y)
    (hX : X.Nonempty) (hY : Y.Nonempty)
    (hXselector : ∀ line ∈ X, line ∈ selector)
    (hYselector : ∀ line ∈ Y, line ∈ selector)
    (E : Finset (MarkedLine × MarkedLine)) (hE_sub : E ⊆ X ×ˢ Y)
    (c : ℝ) (hc_pos : 0 < c) (hc_le : c ≤ 1)
    (hE_dense : c * (X.card : ℝ) * (Y.card : ℝ) ≤ (E.card : ℝ))
    (hX_large : 4 ≤ c * (X.card : ℝ))
    (hY_large : 8 < c ^ 2 * (Y.card : ℝ))
    (edgeTime : (MarkedLine × MarkedLine) → ℝ)
    (timeGap : ℝ) (_htimeGap : 0 < timeGap)
    (hEdgeTimeSeparated : ∀ p ∈ E, ∀ q ∈ E, p ≠ q →
      timeGap ≤ |edgeTime p - edgeTime q|)
    (residualBound : ℝ)
    (hEdgeResidual : ∀ p ∈ E,
      markedPairContactResidualNorm p (edgeTime p) ≤ residualBound ∧
      markedPairContactResidualNorm (p.2, p.1) (edgeTime p) ≤ residualBound)
    (hchartX : ∀ line ∈ X, direction line (3 : Fin 4) ≠ 0)
    (hchartY : ∀ line ∈ Y, direction line (3 : Fin 4) ≠ 0) :
    ∃ (line : Fin 4 → MarkedLine) (approxTime : Fin 4 → ℝ),
      Function.Injective line ∧
      (∀ i, line i ∈ selector) ∧
      (∀ i, direction (line i) (3 : Fin 4) ≠ 0) ∧
      (∀ i j, i ≠ j →
        timeGap ≤ |approxTime i - approxTime j|) ∧
      (∀ i,
        ‖(fourCycleEdgeSecant line i).2 +
            approxTime i • (fourCycleEdgeSecant line i).1‖ ≤ residualBound) := by
  obtain ⟨line, hlineInjective, hlineSelector,
      hedge01, hedge21, hedge23, hedge03⟩ :=
    dense_bipartite_has_marked_four_cycle selector X Y hXY hX hY
      hXselector hYselector E hE_sub c hc_pos hc_le hE_dense
      hX_large hY_large
  let approxTime : Fin 4 → ℝ := markedCycleRelationTime edgeTime line
  have hedge : ∀ i, markedCycleRelationEdge line i ∈ E := by
    intro i
    fin_cases i <;>
      simp [markedCycleRelationEdge, hedge01, hedge21, hedge23, hedge03]
  have hedgeInjective : Function.Injective (markedCycleRelationEdge line) :=
    markedCycleRelationEdge_injective hlineInjective
  have hedge01Sub : line 0 ∈ X ∧ line 1 ∈ Y := by
    simpa using hE_sub hedge01
  have hedge21Sub : line 2 ∈ X ∧ line 1 ∈ Y := by
    simpa using hE_sub hedge21
  have hedge23Sub : line 2 ∈ X ∧ line 3 ∈ Y := by
    simpa using hE_sub hedge23
  refine ⟨line, approxTime, hlineInjective, hlineSelector,
    ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hchartX _ hedge01Sub.1
    · exact hchartY _ hedge01Sub.2
    · exact hchartX _ hedge21Sub.1
    · exact hchartY _ hedge23Sub.2
  · intro i j hij
    exact hEdgeTimeSeparated
      (markedCycleRelationEdge line i) (hedge i)
      (markedCycleRelationEdge line j) (hedge j)
      (hedgeInjective.ne hij)
  · intro i
    have hres := hEdgeResidual (markedCycleRelationEdge line i) (hedge i)
    fin_cases i
    · simpa [approxTime, markedCycleRelationTime, markedCycleRelationEdge,
        fourCycleEdgeSecant, fourCycleNext,
        markedPairContactResidualNorm] using hres.1
    · simpa [approxTime, markedCycleRelationTime, markedCycleRelationEdge,
        fourCycleEdgeSecant, fourCycleNext,
        markedPairContactResidualNorm] using hres.2
    · simpa [approxTime, markedCycleRelationTime, markedCycleRelationEdge,
        fourCycleEdgeSecant, fourCycleNext,
        markedPairContactResidualNorm] using hres.1
    · simpa [approxTime, markedCycleRelationTime, markedCycleRelationEdge,
        fourCycleEdgeSecant, fourCycleNext,
        markedPairContactResidualNorm] using hres.2

end StickyKakeya4
