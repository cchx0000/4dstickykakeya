import Theorems.Thm_StickyKakeya4_exact_collision_identity

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace StickyKakeya4

/-- Projection onto the first three Euclidean coordinates. -/
def horizontalProjection (x : E4) : E3 :=
  WithLp.toLp 2 (fun i : Fin 3 => x i.castSucc)

@[simp] theorem horizontalProjection_apply (x : E4) (i : Fin 3) :
    horizontalProjection x i = x i.castSucc := rfl

theorem horizontalProjection_add (x y : E4) :
    horizontalProjection (x + y) =
      horizontalProjection x + horizontalProjection y := by
  ext i
  simp [horizontalProjection]

theorem horizontalProjection_sub (x y : E4) :
    horizontalProjection (x - y) =
      horizontalProjection x - horizontalProjection y := by
  ext i
  simp [horizontalProjection]

theorem horizontalProjection_smul (c : ℝ) (x : E4) :
    horizontalProjection (c • x) = c • horizontalProjection x := by
  ext i
  simp [horizontalProjection]

/-- Slope of an oriented affine line in the graph chart whose distinguished
coordinate is the fourth Euclidean coordinate. -/
def northGraphSlope (line : MarkedLine) : E3 :=
  (direction line (3 : Fin 4))⁻¹ • horizontalProjection (direction line)

/-- Horizontal intercept of an oriented affine line at fourth coordinate
zero in the north graph chart. -/
def northGraphIntercept (line : MarkedLine) : E3 :=
  horizontalProjection (offset line) -
    offset line (3 : Fin 4) • northGraphSlope line

/-- Contact graph point attached to an actual marked line.  The affine mark is
not discarded from the line; it is simply irrelevant to the unmarked graph
coordinates `(a,b)`. -/
def northContactGraphPoint (line : MarkedLine) : E3 × E3 :=
  (northGraphSlope line, northGraphIntercept line)

/-- Horizontal evaluation of the graph line at fourth-coordinate time `s`. -/
def northGraphEvaluation (line : MarkedLine) (s : ℝ) : E3 :=
  northGraphIntercept line + s • northGraphSlope line

/-- Affine-line parameter at which the fourth Euclidean coordinate equals
`s`. -/
def fixedHeightTime (line : MarkedLine) (s : ℝ) : ℝ :=
  (s - offset line (3 : Fin 4)) / direction line (3 : Fin 4)

/-- Actual point on the underlying affine line with prescribed fourth
coordinate. -/
def fixedHeightPoint (line : MarkedLine) (s : ℝ) : E4 :=
  offset line + fixedHeightTime line s • direction line

theorem fixedHeightPoint_fourth_coordinate
    (line : MarkedLine) (s : ℝ)
    (hchart : direction line (3 : Fin 4) ≠ 0) :
    fixedHeightPoint line s (3 : Fin 4) = s := by
  simp only [fixedHeightPoint, fixedHeightTime, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  field_simp [hchart]
  ring

/-- Exact contact-chart identity: the horizontal part of the actual affine
line point at height `s` is `b + s a`. -/
theorem horizontalProjection_fixedHeightPoint
    (line : MarkedLine) (s : ℝ)
    (hchart : direction line (3 : Fin 4) ≠ 0) :
    horizontalProjection (fixedHeightPoint line s) =
      northGraphEvaluation line s := by
  ext i
  simp only [horizontalProjection_apply, fixedHeightPoint, fixedHeightTime,
    northGraphEvaluation, northGraphIntercept, northGraphSlope,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [hchart]
  ring

/-- Direction and intercept secants of two actual marked lines in the fixed
graph chart. -/
def northGraphSecant (line line' : MarkedLine) : E3 × E3 :=
  (northGraphSlope line - northGraphSlope line',
    northGraphIntercept line - northGraphIntercept line')

/-- The physical horizontal separation of two lines at common height is the
contact expression `beta + s alpha` for their graph secant. -/
theorem northGraphEvaluation_sub_eq_secant
    (line line' : MarkedLine) (s : ℝ) :
    northGraphEvaluation line s - northGraphEvaluation line' s =
      (northGraphSecant line line').2 +
        s • (northGraphSecant line line').1 := by
  simp only [northGraphEvaluation, northGraphSecant]
  module

/-- Fully physical version of the exact collision identity in the north
graph chart.  Both sides are built from actual marked lines; no abstract
matrix or external Kakeya theorem is assumed. -/
theorem northGraph_exact_collision_identity
    (line line' : MarkedLine)
    (hsecant : (northGraphSecant line line').1 ≠ 0) (s : ℝ) :
    ‖northGraphEvaluation line s - northGraphEvaluation line' s‖ ^ 2 =
      ‖collisionResidual (northGraphSecant line line').1
          (northGraphSecant line line').2‖ ^ 2 +
        ‖(northGraphSecant line line').1‖ ^ 2 *
          |s - collisionTime (northGraphSecant line line').1
            (northGraphSecant line line').2| ^ 2 := by
  rw [northGraphEvaluation_sub_eq_secant]
  exact exact_collision_identity
    (northGraphSecant line line').1
    (northGraphSecant line line').2 hsecant s

/-- A common physical collision packet at two separated graph heights controls
the actual slope secant of the two marked lines. -/
theorem northGraph_two_probe_slope_secant_bound
    (line line' : MarkedLine) (s t Rs Rt g : ℝ)
    (hRs : ‖northGraphEvaluation line s -
      northGraphEvaluation line' s‖ ≤ Rs)
    (hRt : ‖northGraphEvaluation line t -
      northGraphEvaluation line' t‖ ≤ Rt)
    (hg : 0 < g) (hsep : g ≤ |t - s|) :
    ‖(northGraphSecant line line').1‖ ≤ (Rs + Rt) / g := by
  rw [northGraphEvaluation_sub_eq_secant] at hRs hRt
  exact separated_reeb_two_probe_direction_bound
    (northGraphSecant line line').1
    (northGraphSecant line line').2 s t Rs Rt g hRs hRt hg hsep

end StickyKakeya4
