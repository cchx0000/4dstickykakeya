import Theorems.Thm_StickyKakeya4_north_graph_contact_coordinates

open Set

noncomputable section

namespace StickyKakeya4

/-- The three anchored contact secants determined by four marked lines. -/
def anchoredCycleSecant (line : Fin 4 → MarkedLine) (j : Fin 3) : E3 × E3 :=
  (northGraphSlope (line j.succ) - northGraphSlope (line 0),
    northGraphIntercept (line j.succ) - northGraphIntercept (line 0))

/-- Horizontal frame matrix whose columns are the three anchored slope
secants. -/
def anchoredCycleA (line : Fin 4 → MarkedLine) : Mat3 :=
  fun i j => (anchoredCycleSecant line j).1 i

/-- Vertical frame matrix whose columns are the three anchored intercept
secants. -/
def anchoredCycleB (line : Fin 4 → MarkedLine) : Mat3 :=
  fun i j => (anchoredCycleSecant line j).2 i

/-- Euclidean-space readback of a matrix acting on frame coefficients. -/
def matrixVectorE3 (M : Mat3) (c : E3) : E3 :=
  WithLp.toLp 2 (M.mulVec c.ofLp)

theorem matrixVectorE3_anchoredCycleA
    (line : Fin 4 → MarkedLine) (c : E3) :
    matrixVectorE3 (anchoredCycleA line) c =
      ∑ j : Fin 3, c j • (anchoredCycleSecant line j).1 := by
  ext i
  simp [matrixVectorE3, anchoredCycleA, Matrix.mulVec, dotProduct, mul_comm]

theorem matrixVectorE3_anchoredCycleB
    (line : Fin 4 → MarkedLine) (c : E3) :
    matrixVectorE3 (anchoredCycleB line) c =
      ∑ j : Fin 3, c j • (anchoredCycleSecant line j).2 := by
  ext i
  simp [matrixVectorE3, anchoredCycleB, Matrix.mulVec, dotProduct, mul_comm]

/-- Standard coefficient vector in the anchored three-secant frame. -/
def cycleBasis (j : Fin 3) : E3 := EuclideanSpace.single j 1

/-- Raw coefficients of the four oriented edges
`z₁-z₀`, `z₂-z₁`, `z₃-z₂`, `z₀-z₃` in the anchored frame. -/
def rawFourCycleCoeff (i : Fin 4) : E3 :=
  if i = 0 then cycleBasis 0
  else if i = 1 then cycleBasis 1 - cycleBasis 0
  else if i = 2 then cycleBasis 2 - cycleBasis 1
  else -cycleBasis 2

/-- Cyclic successor on four vertices. -/
def fourCycleNext (i : Fin 4) : Fin 4 :=
  ⟨(i.val + 1) % 4, Nat.mod_lt _ (by norm_num)⟩

/-- Oriented contact secant of the corresponding four-cycle edge. -/
def fourCycleEdgeSecant (line : Fin 4 → MarkedLine) (i : Fin 4) : E3 × E3 :=
  (northGraphSlope (line (fourCycleNext i)) - northGraphSlope (line i),
    northGraphIntercept (line (fourCycleNext i)) - northGraphIntercept (line i))

theorem rawFourCycleCoeff_ne_zero (i : Fin 4) :
    rawFourCycleCoeff i ≠ 0 := by
  fin_cases i
  · intro h
    have hk := congrArg (fun c : E3 => c (0 : Fin 3)) h
    simpa [rawFourCycleCoeff, cycleBasis, PiLp.single_apply] using hk
  · intro h
    have hk := congrArg (fun c : E3 => c (1 : Fin 3)) h
    simpa [rawFourCycleCoeff, cycleBasis, PiLp.single_apply] using hk
  · intro h
    have hk := congrArg (fun c : E3 => c (2 : Fin 3)) h
    simpa [rawFourCycleCoeff, cycleBasis, PiLp.single_apply] using hk
  · intro h
    have hk := congrArg (fun c : E3 => c (2 : Fin 3)) h
    simpa [rawFourCycleCoeff, cycleBasis, PiLp.single_apply] using hk

/-- Unit coefficient attached to a four-cycle edge. -/
def fourCycleCoeff (i : Fin 4) : E3 :=
  ‖rawFourCycleCoeff i‖⁻¹ • rawFourCycleCoeff i

theorem fourCycleCoeff_norm (i : Fin 4) : ‖fourCycleCoeff i‖ = 1 := by
  rw [fourCycleCoeff, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (rawFourCycleCoeff_ne_zero i)

/-- The raw four-cycle coefficients recover the four actual contact secants
from the three anchored columns. -/
theorem anchoredCycleFrame_rawCoeff_eq_edge
    (line : Fin 4 → MarkedLine) (i : Fin 4) :
    (matrixVectorE3 (anchoredCycleA line) (rawFourCycleCoeff i),
      matrixVectorE3 (anchoredCycleB line) (rawFourCycleCoeff i)) =
        fourCycleEdgeSecant line i := by
  fin_cases i <;>
    ext k <;>
    simp [matrixVectorE3_anchoredCycleA,
      matrixVectorE3_anchoredCycleB, anchoredCycleSecant,
      rawFourCycleCoeff, cycleBasis, fourCycleEdgeSecant,
      fourCycleNext, PiLp.single_apply, Fin.sum_univ_succ] <;>
    ring

theorem matrixVectorE3_smul (M : Mat3) (a : ℝ) (c : E3) :
    matrixVectorE3 M (a • c) = a • matrixVectorE3 M c := by
  ext i
  simp [matrixVectorE3, Matrix.mulVec, Finset.mul_sum, mul_assoc,
    mul_comm, mul_left_comm]

/-- Exact normalized version used by the four-probe boundary structure. -/
theorem anchoredCycleFrame_coeff_eq_normalized_edge
    (line : Fin 4 → MarkedLine) (i : Fin 4) :
    (matrixVectorE3 (anchoredCycleA line) (fourCycleCoeff i),
      matrixVectorE3 (anchoredCycleB line) (fourCycleCoeff i)) =
        ‖rawFourCycleCoeff i‖⁻¹ • fourCycleEdgeSecant line i := by
  rw [fourCycleCoeff, matrixVectorE3_smul, matrixVectorE3_smul]
  rw [← Prod.smul_mk]
  exact congrArg (fun z => ‖rawFourCycleCoeff i‖⁻¹ • z)
    (anchoredCycleFrame_rawCoeff_eq_edge line i)

/-- Matrix-pencil residual of a normalized cycle edge is exactly the
normalized physical contact residual of that same edge. -/
theorem anchoredCycle_pencil_coeff_eq_contactResidual
    (line : Fin 4 → MarkedLine) (time : Fin 4 → ℝ) (i : Fin 4) :
    matrixVectorE3 (pencil (anchoredCycleA line) (anchoredCycleB line)
        (time i)) (fourCycleCoeff i) =
      ‖rawFourCycleCoeff i‖⁻¹ •
        ((fourCycleEdgeSecant line i).2 +
          time i • (fourCycleEdgeSecant line i).1) := by
  have hframe := anchoredCycleFrame_coeff_eq_normalized_edge line i
  have hA :
      matrixVectorE3 (anchoredCycleA line) (fourCycleCoeff i) =
        ‖rawFourCycleCoeff i‖⁻¹ • (fourCycleEdgeSecant line i).1 := by
    simpa using congrArg Prod.fst hframe
  have hB :
      matrixVectorE3 (anchoredCycleB line) (fourCycleCoeff i) =
        ‖rawFourCycleCoeff i‖⁻¹ • (fourCycleEdgeSecant line i).2 := by
    simpa using congrArg Prod.snd hframe
  rw [pencil]
  simp only [matrixVectorE3, Matrix.add_mulVec, Matrix.smul_mulVec]
  change matrixVectorE3 (anchoredCycleB line) (fourCycleCoeff i) +
      time i • matrixVectorE3 (anchoredCycleA line) (fourCycleCoeff i) = _
  rw [hA, hB]
  module

/-- Function-space form of the preceding identity.  This is definitionally
the residual type used by `FourProbeConcentrationLimit` and the fresh-return
tower. -/
theorem anchoredCycle_pencil_coeff_raw_eq_contactResidual
    (line : Fin 4 → MarkedLine) (time : Fin 4 → ℝ) (i : Fin 4) :
    (pencil (anchoredCycleA line) (anchoredCycleB line) (time i)).mulVec
        (fourCycleCoeff i).ofLp =
      (‖rawFourCycleCoeff i‖⁻¹ •
        ((fourCycleEdgeSecant line i).2 +
          time i • (fourCycleEdgeSecant line i).1)).ofLp := by
  have h := congrArg WithLp.ofLp
    (anchoredCycle_pencil_coeff_eq_contactResidual line time i)
  simpa [matrixVectorE3] using h

end StickyKakeya4
