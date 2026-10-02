import Theorems.Thm_StickyKakeya4_actual_slope_source_bounds

/-!
Actual residual-shell edges are close in the original direction--offset
carrier. The estimate keeps the original closest collision time and residual.
It is the physical input for localizing a graph in the fixed reference nets;
no carrier-proximity certificate is assumed.
-/

open scoped RealInnerProductSpace

namespace StickyKakeya4

theorem offset_eq_fixedHeightPoint_sub_projection
    (line : MarkedLine) (hvalid : IsValidLine line) (s : ℝ) :
    offset line = fixedHeightPoint line s -
      inner ℝ (fixedHeightPoint line s) (direction line) • direction line := by
  have hinner : inner ℝ (fixedHeightPoint line s) (direction line) =
      fixedHeightTime line s := by
    simp only [fixedHeightPoint, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hvalid.1, hvalid.2]
    ring
  rw [hinner, fixedHeightPoint]
  module

/-- Orthogonal offsets vary continuously with both a point on the line and
its unit direction, with an explicit bound valid for the original lines. -/
theorem offset_dist_le_point_direction_dist
    (line line' : MarkedLine) (hvalid : IsValidLine line)
    (hvalid' : IsValidLine line') (s : ℝ) :
    dist (offset line) (offset line') ≤
      2 * dist (fixedHeightPoint line s) (fixedHeightPoint line' s) +
      2 * ‖fixedHeightPoint line' s‖ * dist (direction line) (direction line') := by
  let x := fixedHeightPoint line s
  let y := fixedHeightPoint line' s
  let d := direction line
  let e := direction line'
  have hd : ‖d‖ = 1 := hvalid.1
  have he : ‖e‖ = 1 := hvalid'.1
  have hvec : offset line - offset line' =
      (x - y) - inner ℝ (x - y) d • d -
        inner ℝ y (d - e) • d - inner ℝ y e • (d - e) := by
    rw [offset_eq_fixedHeightPoint_sub_projection line hvalid s,
      offset_eq_fixedHeightPoint_sub_projection line' hvalid' s]
    dsimp only [x, y, d, e]
    simp only [inner_sub_left, inner_sub_right, sub_smul, smul_sub]
    module
  have h1 : ‖inner ℝ (x - y) d • d‖ ≤ ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, hd, mul_one]
    simpa only [hd, mul_one] using abs_real_inner_le_norm (x - y) d
  have h2 : ‖inner ℝ y (d - e) • d‖ ≤ ‖y‖ * ‖d - e‖ := by
    rw [norm_smul, Real.norm_eq_abs, hd, mul_one]
    exact abs_real_inner_le_norm y (d - e)
  have h3 : ‖inner ℝ y e • (d - e)‖ ≤ ‖y‖ * ‖d - e‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [he, mul_one] using abs_real_inner_le_norm y e)
      (norm_nonneg _)
  rw [dist_eq_norm, hvec]
  have hbound₁ := norm_sub_le (x - y) (inner ℝ (x - y) d • d)
  have hbound₂ := norm_sub_le ((x - y) - inner ℝ (x - y) d • d)
    (inner ℝ y (d - e) • d)
  have hbound₃ := norm_sub_le ((x - y) - inner ℝ (x - y) d • d -
    inner ℝ y (d - e) • d) (inner ℝ y e • (d - e))
  change _ ≤ 2 * ‖x - y‖ + 2 * ‖y‖ * ‖d - e‖
  linarith

theorem fixedHeightPoint_norm_le_offset_height_bound
    (line : MarkedLine) (hvalid : IsValidLine line)
    (hchart : (1 / 2 : ℝ) ≤ direction line (3 : Fin 4))
    (R S s : ℝ) (hoffset : ‖offset line‖ ≤ R) (hs : |s| ≤ S) :
    ‖fixedHeightPoint line s‖ ≤ 3 * R + 2 * S := by
  have hdirpos : 0 < direction line (3 : Fin 4) := by linarith
  have hR : 0 ≤ R := (norm_nonneg _).trans hoffset
  have hS : 0 ≤ S := (abs_nonneg _).trans hs
  have hcoordNorm : |offset line (3 : Fin 4)| ≤ ‖offset line‖ := by
    simpa only [Real.norm_eq_abs] using
      PiLp.norm_apply_le (offset line) (3 : Fin 4)
  have hcoord : |offset line (3 : Fin 4)| ≤ R := hcoordNorm.trans hoffset
  have htime : |fixedHeightTime line s| ≤ 2 * (S + R) := by
    rw [fixedHeightTime, abs_div, abs_of_pos hdirpos]
    apply (div_le_iff₀ hdirpos).2
    calc
      |s - offset line (3 : Fin 4)| ≤ |s| + |offset line (3 : Fin 4)| :=
        abs_sub _ _
      _ ≤ S + R := add_le_add hs hcoord
      _ ≤ 2 * (S + R) * direction line (3 : Fin 4) := by nlinarith
  calc
    ‖fixedHeightPoint line s‖ ≤ ‖offset line‖ +
        ‖fixedHeightTime line s • direction line‖ := norm_add_le _ _
    _ = ‖offset line‖ + |fixedHeightTime line s| := by
      rw [norm_smul, Real.norm_eq_abs, hvalid.1, mul_one]
    _ ≤ R + 2 * (S + R) := add_le_add hoffset htime
    _ = 3 * R + 2 * S := by ring

/-- A literal residual edge at angular scale `tau` is close in the original
carrier, rather than merely in an auxiliary source label space. -/
theorem residual_shell_carrier_dist_le
    (line line' : MarkedLine) (hvalid : IsValidLine line)
    (hvalid' : IsValidLine line')
    (hchart : (1 / 2 : ℝ) ≤ direction line (3 : Fin 4))
    (hchart' : (1 / 2 : ℝ) ≤ direction line' (3 : Fin 4))
    (R S tau rho : ℝ) (htau : 0 ≤ tau)
    (hoffset : ‖offset line'‖ ≤ R)
    (hangle : ‖(northGraphSecant line line').1‖ ≤ 2 * tau)
    (hrho : rho ≤ tau)
    (hresidual : ‖collisionResidual (northGraphSecant line line').1
      (northGraphSecant line line').2‖ ≤ rho)
    (htime : |collisionTime (northGraphSecant line line').1
      (northGraphSecant line line').2| ≤ S) :
    dist (direction line, offset line) (direction line', offset line') ≤
      (6 + 24 * R + 16 * S) * tau := by
  let s := collisionTime (northGraphSecant line line').1
    (northGraphSecant line line').2
  have hp : 0 < direction line (3 : Fin 4) := by linarith
  have hp' : 0 < direction line' (3 : Fin 4) := by linarith
  have hR : 0 ≤ R := (norm_nonneg _).trans hoffset
  have hS : 0 ≤ S := (abs_nonneg _).trans htime
  have hd : dist (direction line) (direction line') ≤ 4 * tau := by
    have h := northGraphSlope_direction_bound line line' hvalid hvalid' hp hp'
    change dist (direction line) (direction line') ≤
      2 * ‖(northGraphSecant line line').1‖ at h
    linarith
  have hpoint : dist (fixedHeightPoint line s) (fixedHeightPoint line' s) ≤ rho := by
    rw [dist_fixedHeightPoint_eq_norm_northGraphEvaluation_sub line s
      (fixedHeightPoint line' s) hp.ne'
      (fixedHeightPoint_fourth_coordinate line' s hp'.ne'),
      horizontalProjection_fixedHeightPoint line' s hp'.ne',
      northGraphEvaluation_sub_eq_secant]
    exact hresidual
  have hnorm := fixedHeightPoint_norm_le_offset_height_bound line' hvalid'
    hchart' R S s hoffset htime
  have hoff := offset_dist_le_point_direction_dist line line' hvalid hvalid' s
  have hoff' : dist (offset line) (offset line') ≤
      2 * rho + 2 * (3 * R + 2 * S) * (4 * tau) := by
    apply hoff.trans
    gcongr
  rw [Prod.dist_eq]
  apply max_le
  · nlinarith [mul_nonneg hR htau, mul_nonneg hS htau]
  · nlinarith

end StickyKakeya4
