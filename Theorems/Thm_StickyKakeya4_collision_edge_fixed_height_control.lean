import Theorems.Thm_StickyKakeya4_collision_flow_overlap_witness
import Theorems.Thm_StickyKakeya4_north_graph_contact_coordinates

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace StickyKakeya4

/-- Moving a marked-segment point along its underlying line to a prescribed
fourth coordinate has this exact correction vector. -/
theorem fixedHeightPoint_eq_rawFrontParam_add_verticalCorrection
    (line : MarkedLine) (hchart : direction line (3 : Fin 4) ≠ 0)
    (s t : ℝ) :
    fixedHeightPoint line s = rawFrontParam (line, t) +
      ((s - rawFrontParam (line, t) (3 : Fin 4)) /
        direction line (3 : Fin 4)) • direction line := by
  ext k
  simp only [fixedHeightPoint, fixedHeightTime, rawFrontParam,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [hchart]
  ring

/-- A coordinate difference is bounded by the ambient Euclidean distance. -/
theorem abs_coordinate_sub_le_dist_E4 (x y : E4) (i : Fin 4) :
    |x i - y i| ≤ dist x y := by
  have h := PiLp.norm_apply_le (x - y) i
  simpa [dist_eq_norm, PiLp.sub_apply, Real.norm_eq_abs] using h

/-- At the fourth coordinate of `x`, moving an actual point of a valid line
to the graph-chart representative increases its distance from `x` by at most
the explicit chart amplification `1 + |d₄⁻¹|`. -/
theorem dist_fixedHeightPoint_le_chartAmplification_mul_dist_rawFrontParam
    (line : MarkedLine) (hvalid : IsValidLine line)
    (hchart : direction line (3 : Fin 4) ≠ 0)
    (x : E4) (t : ℝ) :
    dist (fixedHeightPoint line (x (3 : Fin 4))) x ≤
      (|(direction line (3 : Fin 4))⁻¹| + 1) *
        dist x (rawFrontParam (line, t)) := by
  let y : E4 := rawFrontParam (line, t)
  have hcoordinate : |x (3 : Fin 4) - y (3 : Fin 4)| ≤ dist x y :=
    abs_coordinate_sub_le_dist_E4 x y (3 : Fin 4)
  have hcorrection :
      |(x (3 : Fin 4) - y (3 : Fin 4)) /
          direction line (3 : Fin 4)| ≤
        |(direction line (3 : Fin 4))⁻¹| * dist x y := by
    calc
      |(x (3 : Fin 4) - y (3 : Fin 4)) /
          direction line (3 : Fin 4)| =
          |x (3 : Fin 4) - y (3 : Fin 4)| *
            |(direction line (3 : Fin 4))⁻¹| := by
        rw [div_eq_mul_inv, abs_mul]
      _ ≤ dist x y * |(direction line (3 : Fin 4))⁻¹| :=
        mul_le_mul_of_nonneg_right hcoordinate (abs_nonneg _)
      _ = |(direction line (3 : Fin 4))⁻¹| * dist x y := by ring
  have hmove :
      dist (fixedHeightPoint line (x (3 : Fin 4))) y ≤
        |(direction line (3 : Fin 4))⁻¹| * dist x y := by
    calc
      dist (fixedHeightPoint line (x (3 : Fin 4))) y =
          ‖((x (3 : Fin 4) - y (3 : Fin 4)) /
              direction line (3 : Fin 4)) • direction line‖ := by
        rw [fixedHeightPoint_eq_rawFrontParam_add_verticalCorrection
          line hchart (x (3 : Fin 4)) t]
        simp [y, dist_eq_norm]
      _ = |(x (3 : Fin 4) - y (3 : Fin 4)) /
              direction line (3 : Fin 4)| * ‖direction line‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = |(x (3 : Fin 4) - y (3 : Fin 4)) /
              direction line (3 : Fin 4)| := by rw [hvalid.1, mul_one]
      _ ≤ |(direction line (3 : Fin 4))⁻¹| * dist x y := hcorrection
  calc
    dist (fixedHeightPoint line (x (3 : Fin 4))) x ≤
        dist (fixedHeightPoint line (x (3 : Fin 4))) y + dist y x :=
      dist_triangle _ _ _
    _ ≤ |(direction line (3 : Fin 4))⁻¹| * dist x y + dist y x :=
      add_le_add hmove le_rfl
    _ = (|(direction line (3 : Fin 4))⁻¹| + 1) * dist x y := by
      rw [dist_comm y x]
      ring
    _ = (|(direction line (3 : Fin 4))⁻¹| + 1) *
        dist x (rawFrontParam (line, t)) := by rfl

/-- Strict version used with the positive slack supplied by `infDist`. -/
theorem dist_fixedHeightPoint_lt_chartAmplification_mul_of_rawFrontParam_near
    (line : MarkedLine) (hvalid : IsValidLine line)
    (hchart : direction line (3 : Fin 4) ≠ 0)
    (x : E4) (t rho : ℝ)
    (hnear : dist x (rawFrontParam (line, t)) < rho) :
    dist (fixedHeightPoint line (x (3 : Fin 4))) x <
      (|(direction line (3 : Fin 4))⁻¹| + 1) * rho := by
  refine (dist_fixedHeightPoint_le_chartAmplification_mul_dist_rawFrontParam
    line hvalid hchart x t).trans_lt ?_
  exact mul_lt_mul_of_pos_left hnear (by positivity)

/-- Admissibility and fractional restriction preserve validity of every
actual marked line. -/
theorem fractionalSourceRestriction_line_valid
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D) (i : Fin n) :
    IsValidLine (R.line i) := by
  have hline : R.line i = D.line i := congrFun hR.2.1 i
  simpa [hline] using hD.2.2.2.2.1 i

/-- Each physical collision-support edge gives two graph-chart points at the
same fourth-coordinate time, both quantitatively close to the common shading
point.  This is the exact local input for contact residual control. -/
theorem sourceCollisionSupport_has_common_height_control
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D) {i j : Fin n}
    (hedge : (i, j) ∈ sourceCollisionSupport R)
    (hchart_i : direction (R.line i) (3 : Fin 4) ≠ 0)
    (hchart_j : direction (R.line j) (3 : Fin 4) ≠ 0)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ (x : E4) (ti tj : ℝ),
      x ∈ R.shading i ∧ x ∈ R.shading j ∧
      ti ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ∧
      tj ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ∧
      dist (fixedHeightPoint (R.line i) (x (3 : Fin 4))) x <
        (|(direction (R.line i) (3 : Fin 4))⁻¹| + 1) *
          (R.thickness + eta) ∧
      dist (fixedHeightPoint (R.line j) (x (3 : Fin 4))) x <
        (|(direction (R.line j) (3 : Fin 4))⁻¹| + 1) *
          (R.thickness + eta) := by
  obtain ⟨x, ti, tj, hxi, hxj, hti, htj, hiNear, hjNear⟩ :=
    sourceCollisionSupport_has_front_parameter_overlap hD hR hedge heta
  refine ⟨x, ti, tj, hxi, hxj, hti, htj, ?_, ?_⟩
  · exact dist_fixedHeightPoint_lt_chartAmplification_mul_of_rawFrontParam_near
      (R.line i) (fractionalSourceRestriction_line_valid hD hR i)
      hchart_i x ti (R.thickness + eta) hiNear
  · exact dist_fixedHeightPoint_lt_chartAmplification_mul_of_rawFrontParam_near
      (R.line j) (fractionalSourceRestriction_line_valid hD hR j)
      hchart_j x tj (R.thickness + eta) hjNear

end StickyKakeya4
