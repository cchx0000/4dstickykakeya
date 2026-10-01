import Theorems.Thm_StickyKakeya4_separated_collision_relation_packet

open Set

noncomputable section

namespace StickyKakeya4

/-- Each raw four-cycle coefficient contains a coordinate of absolute value
one, hence its Euclidean norm is at least one. -/
theorem one_le_norm_rawFourCycleCoeff (i : Fin 4) :
    1 ≤ ‖rawFourCycleCoeff i‖ := by
  fin_cases i
  · have h := PiLp.norm_apply_le
        (rawFourCycleCoeff (0 : Fin 4)) (0 : Fin 3)
    simpa [rawFourCycleCoeff, cycleBasis, PiLp.single_apply] using h
  · have h := PiLp.norm_apply_le
        (rawFourCycleCoeff (1 : Fin 4)) (1 : Fin 3)
    simpa [rawFourCycleCoeff, cycleBasis, PiLp.single_apply] using h
  · have h := PiLp.norm_apply_le
        (rawFourCycleCoeff (2 : Fin 4)) (2 : Fin 3)
    simpa [rawFourCycleCoeff, cycleBasis, PiLp.single_apply] using h
  · have h := PiLp.norm_apply_le
        (rawFourCycleCoeff (3 : Fin 4)) (2 : Fin 3)
    simpa [rawFourCycleCoeff, cycleBasis, PiLp.single_apply] using h

theorem inv_norm_rawFourCycleCoeff_le_one (i : Fin 4) :
    ‖rawFourCycleCoeff i‖⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_norm_rawFourCycleCoeff i)

/-- Forgetting the `L²` wrapper can only decrease the norm: the target
function space has the coordinatewise supremum norm. -/
theorem norm_ofLp_le_norm_E3 (v : E3) : ‖v.ofLp‖ ≤ ‖v‖ := by
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2
    (fun j ↦ PiLp.norm_apply_le v j)

/-- The normalization used by the Maslov pencil neither enlarges a physical
contact residual nor loses the function-space norm required by the return
tower. -/
theorem normalized_fourCycleResidual_le
    (i : Fin 4) (v : E3) (R : ℝ) (hR : ‖v‖ ≤ R) :
    ‖(‖rawFourCycleCoeff i‖⁻¹ • v).ofLp‖ ≤ R := by
  calc
    ‖(‖rawFourCycleCoeff i‖⁻¹ • v).ofLp‖ ≤
        ‖‖rawFourCycleCoeff i‖⁻¹ • v‖ :=
      norm_ofLp_le_norm_E3 _
    _ = ‖rawFourCycleCoeff i‖⁻¹ * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
      positivity
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right
      (inv_norm_rawFourCycleCoeff_le_one i) (norm_nonneg v)
    _ ≤ R := by simpa using hR

/-- Exact node packet consumed by `PrunedMarkedFourCycleReturnTower`.  The
residual is already normalized and measured after forgetting the `L²`
wrapper, so no analytic conversion remains at the tower interface. -/
structure NormalizedMarkedFourCyclePacket
    (selector : Set MarkedLine) (timeGap residualBound : ℝ) where
  line : Fin 4 → MarkedLine
  lineInjective : Function.Injective line
  line_mem_selector : ∀ i, line i ∈ selector
  chartNonzero : ∀ i, direction (line i) (3 : Fin 4) ≠ 0
  approxTime : Fin 4 → ℝ
  timeSeparated : ∀ i j, i ≠ j →
    timeGap ≤ |approxTime i - approxTime j|
  physicalCycleResidual : ∀ i,
    ‖(‖rawFourCycleCoeff i‖⁻¹ •
        ((fourCycleEdgeSecant line i).2 +
          approxTime i • (fourCycleEdgeSecant line i).1)).ofLp‖ ≤
      residualBound

/-- Formalpedia's dependent-random-choice extraction, followed by the exact
contact-coordinate and normalization lemmas, produces a tower-ready packet
from one dense separated collision relation. -/
theorem dense_bipartite_has_normalized_marked_four_cycle_packet
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
    (timeGap : ℝ) (htimeGap : 0 < timeGap)
    (hEdgeTimeSeparated : ∀ p ∈ E, ∀ q ∈ E, p ≠ q →
      timeGap ≤ |edgeTime p - edgeTime q|)
    (residualBound : ℝ)
    (hEdgeResidual : ∀ p ∈ E,
      markedPairContactResidualNorm p (edgeTime p) ≤ residualBound ∧
      markedPairContactResidualNorm (p.2, p.1) (edgeTime p) ≤ residualBound)
    (hchartX : ∀ line ∈ X, direction line (3 : Fin 4) ≠ 0)
    (hchartY : ∀ line ∈ Y, direction line (3 : Fin 4) ≠ 0) :
    Nonempty (NormalizedMarkedFourCyclePacket selector timeGap residualBound) := by
  obtain ⟨line, approxTime, hlineInjective, hlineSelector, hchartLine,
      htimeSeparated, hresidual⟩ :=
    dense_bipartite_has_separated_marked_four_cycle_packet
      selector X Y hXY hX hY hXselector hYselector E hE_sub c hc_pos
      hc_le hE_dense hX_large hY_large edgeTime timeGap htimeGap
      hEdgeTimeSeparated residualBound hEdgeResidual hchartX hchartY
  refine ⟨⟨line, hlineInjective, hlineSelector, hchartLine, approxTime,
    htimeSeparated, ?_⟩⟩
  intro i
  exact normalized_fourCycleResidual_le i _ residualBound (hresidual i)

end StickyKakeya4
