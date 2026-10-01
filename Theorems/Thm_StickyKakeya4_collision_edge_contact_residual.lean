import Theorems.Thm_StickyKakeya4_collision_edge_fixed_height_control
import Theorems.Thm_StickyKakeya4_separated_collision_relation_packet

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace StickyKakeya4

/-- Dropping the fourth Euclidean coordinate is norm nonincreasing. -/
theorem norm_horizontalProjection_le (x : E4) :
    ‖horizontalProjection x‖ ≤ ‖x‖ := by
  have hsq : ‖horizontalProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp [horizontalProjection, Fin.sum_univ_succ]
    positivity
  nlinarith [norm_nonneg (horizontalProjection x), norm_nonneg x]

/-- At a common graph height, the contact residual of two marked lines is at
most the ambient distance between their actual fixed-height points. -/
theorem markedPairContactResidualNorm_le_fixedHeightPoint_dist
    (line line' : MarkedLine)
    (hchart : direction line (3 : Fin 4) ≠ 0)
    (hchart' : direction line' (3 : Fin 4) ≠ 0)
    (s : ℝ) :
    markedPairContactResidualNorm (line, line') s ≤
      dist (fixedHeightPoint line s) (fixedHeightPoint line' s) := by
  calc
    markedPairContactResidualNorm (line, line') s =
        ‖northGraphEvaluation line' s - northGraphEvaluation line s‖ := by
      rw [markedPairContactResidualNorm,
        northGraphEvaluation_sub_eq_secant]
      rfl
    _ = ‖horizontalProjection
        (fixedHeightPoint line' s - fixedHeightPoint line s)‖ := by
      rw [horizontalProjection_sub,
        horizontalProjection_fixedHeightPoint line' s hchart',
        horizontalProjection_fixedHeightPoint line s hchart]
    _ ≤ ‖fixedHeightPoint line' s - fixedHeightPoint line s‖ :=
      norm_horizontalProjection_le _
    _ = dist (fixedHeightPoint line s) (fixedHeightPoint line' s) := by
      rw [dist_eq_norm]
      simpa using
        (norm_sub_rev (fixedHeightPoint line' s) (fixedHeightPoint line s))

/-- Every support edge in a locally valid north chart carries an actual
contact residual at the common physical height.  The residual tends to zero
with the source thickness, up to the explicit chart amplification factors;
the same bound holds in the reverse orientation. -/
theorem sourceCollisionSupport_has_contact_residual_control
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D) {i j : Fin n}
    (hedge : (i, j) ∈ sourceCollisionSupport R)
    (hchart_i : direction (R.line i) (3 : Fin 4) ≠ 0)
    (hchart_j : direction (R.line j) (3 : Fin 4) ≠ 0)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ s : ℝ,
      markedPairContactResidualNorm (R.line i, R.line j) s <
        (|(direction (R.line i) (3 : Fin 4))⁻¹| +
          |(direction (R.line j) (3 : Fin 4))⁻¹| + 2) *
            (R.thickness + eta) ∧
      markedPairContactResidualNorm (R.line j, R.line i) s <
        (|(direction (R.line i) (3 : Fin 4))⁻¹| +
          |(direction (R.line j) (3 : Fin 4))⁻¹| + 2) *
            (R.thickness + eta) := by
  obtain ⟨x, ti, tj, hxi, hxj, hti, htj, hi, hj⟩ :=
    sourceCollisionSupport_has_common_height_control
      hD hR hedge hchart_i hchart_j heta
  let s : ℝ := x (3 : Fin 4)
  have hfixed :
      dist (fixedHeightPoint (R.line i) s)
          (fixedHeightPoint (R.line j) s) <
        (|(direction (R.line i) (3 : Fin 4))⁻¹| +
          |(direction (R.line j) (3 : Fin 4))⁻¹| + 2) *
            (R.thickness + eta) := by
    calc
      dist (fixedHeightPoint (R.line i) s)
          (fixedHeightPoint (R.line j) s) ≤
        dist (fixedHeightPoint (R.line i) s) x +
          dist x (fixedHeightPoint (R.line j) s) := dist_triangle _ _ _
      _ < (|(direction (R.line i) (3 : Fin 4))⁻¹| + 1) *
            (R.thickness + eta) +
          (|(direction (R.line j) (3 : Fin 4))⁻¹| + 1) *
            (R.thickness + eta) := by
        exact add_lt_add (by simpa [s] using hi) (by simpa [s, dist_comm] using hj)
      _ = (|(direction (R.line i) (3 : Fin 4))⁻¹| +
          |(direction (R.line j) (3 : Fin 4))⁻¹| + 2) *
            (R.thickness + eta) := by ring
  have hforward :
      markedPairContactResidualNorm (R.line i, R.line j) s <
        (|(direction (R.line i) (3 : Fin 4))⁻¹| +
          |(direction (R.line j) (3 : Fin 4))⁻¹| + 2) *
            (R.thickness + eta) :=
    (markedPairContactResidualNorm_le_fixedHeightPoint_dist
      (R.line i) (R.line j) hchart_i hchart_j s).trans_lt hfixed
  refine ⟨s, hforward, ?_⟩
  simpa [markedPairContactResidualNorm_swap] using hforward

/-- A literal common point of two positive retained shadings already gives
the same contact-residual control as a collision-support edge.  Unlike the
support lemma above, this statement does not require the shading intersection
to have positive volume; it is therefore the correct bridge from pointwise
high multiplicity to the contact chart. -/
theorem commonShadingPoint_has_contact_residual_control
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D) {i j : Fin n}
    (x : E4) (hxi : x ∈ R.shading i) (hxj : x ∈ R.shading j)
    (hchart_i : direction (R.line i) (3 : Fin 4) ≠ 0)
    (hchart_j : direction (R.line j) (3 : Fin 4) ≠ 0)
    {eta : ℝ} (heta : 0 < eta) :
    markedPairContactResidualNorm (R.line i, R.line j) (x (3 : Fin 4)) <
        (|(direction (R.line i) (3 : Fin 4))⁻¹| +
          |(direction (R.line j) (3 : Fin 4))⁻¹| + 2) *
            (R.thickness + eta) ∧
    markedPairContactResidualNorm (R.line j, R.line i) (x (3 : Fin 4)) <
        (|(direction (R.line i) (3 : Fin 4))⁻¹| +
          |(direction (R.line j) (3 : Fin 4))⁻¹| + 2) *
            (R.thickness + eta) := by
  have hxiD : x ∈ D.shading i := hR.2.2.2.2.2.1 i hxi
  have hxjD : x ∈ D.shading j := hR.2.2.2.2.2.1 j hxj
  have hiTube : Metric.infDist x (unitFront {R.line i}) ≤ R.thickness := by
    rw [hR.1, hR.2.1]
    exact hD.2.2.2.2.2.2.2.1 i x hxiD
  have hjTube : Metric.infDist x (unitFront {R.line j}) ≤ R.thickness := by
    rw [hR.1, hR.2.1]
    exact hD.2.2.2.2.2.2.2.1 j x hxjD
  obtain ⟨ti, _hti, hiNear⟩ :=
    exists_rawFrontParam_dist_lt_of_infDist_le (R.line i) x hiTube heta
  obtain ⟨tj, _htj, hjNear⟩ :=
    exists_rawFrontParam_dist_lt_of_infDist_le (R.line j) x hjTube heta
  have hi :=
    dist_fixedHeightPoint_lt_chartAmplification_mul_of_rawFrontParam_near
      (R.line i) (fractionalSourceRestriction_line_valid hD hR i)
      hchart_i x ti (R.thickness + eta) hiNear
  have hj :=
    dist_fixedHeightPoint_lt_chartAmplification_mul_of_rawFrontParam_near
      (R.line j) (fractionalSourceRestriction_line_valid hD hR j)
      hchart_j x tj (R.thickness + eta) hjNear
  have hfixed :
      dist (fixedHeightPoint (R.line i) (x (3 : Fin 4)))
          (fixedHeightPoint (R.line j) (x (3 : Fin 4))) <
        (|(direction (R.line i) (3 : Fin 4))⁻¹| +
          |(direction (R.line j) (3 : Fin 4))⁻¹| + 2) *
            (R.thickness + eta) := by
    calc
      dist (fixedHeightPoint (R.line i) (x (3 : Fin 4)))
          (fixedHeightPoint (R.line j) (x (3 : Fin 4))) ≤
        dist (fixedHeightPoint (R.line i) (x (3 : Fin 4))) x +
          dist x (fixedHeightPoint (R.line j) (x (3 : Fin 4))) :=
        dist_triangle _ _ _
      _ < (|(direction (R.line i) (3 : Fin 4))⁻¹| + 1) *
            (R.thickness + eta) +
          (|(direction (R.line j) (3 : Fin 4))⁻¹| + 1) *
            (R.thickness + eta) :=
        add_lt_add hi (by simpa [dist_comm] using hj)
      _ = (|(direction (R.line i) (3 : Fin 4))⁻¹| +
          |(direction (R.line j) (3 : Fin 4))⁻¹| + 2) *
            (R.thickness + eta) := by ring
  have hforward :=
    (markedPairContactResidualNorm_le_fixedHeightPoint_dist
      (R.line i) (R.line j) hchart_i hchart_j (x (3 : Fin 4))).trans_lt hfixed
  exact ⟨hforward, by
    simpa [markedPairContactResidualNorm_swap] using hforward⟩

end StickyKakeya4
