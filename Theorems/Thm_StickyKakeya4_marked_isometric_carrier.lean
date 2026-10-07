import Theorems.Thm_StickyKakeya4_marked_isometric_chart

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace MarkedIsometricCarrier
open Classical StickyKakeya4
open scoped RealInnerProductSpace

/-- The carrier metric records direction and perpendicular offset; the
affine mark remains separately present in the actual marked line. -/
def carrier (l : MarkedLine) : E4 × E4 := (direction l, offset l)

lemma projection_correction_dist (c u v : E4) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    dist ((inner ℝ c u) • u) ((inner ℝ c v) • v) ≤ 2 * ‖c‖ * dist u v := by
  have he : (inner ℝ c u) • u - (inner ℝ c v) • v =
      (inner ℝ c u) • (u - v) + (inner ℝ c (u - v)) • v := by
    rw [inner_sub_right]
    module
  have ha : |inner ℝ c u| ≤ ‖c‖ := by
    simpa only [hu, mul_one] using abs_real_inner_le_norm c u
  have hb : |inner ℝ c (u - v)| ≤ ‖c‖ * ‖u - v‖ := abs_real_inner_le_norm c (u - v)
  rw [dist_eq_norm, he]
  calc
    _ ≤ ‖(inner ℝ c u) • (u - v)‖ + ‖(inner ℝ c (u - v)) • v‖ := norm_add_le _ _
    _ = |inner ℝ c u| * ‖u - v‖ + |inner ℝ c (u - v)| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hv, mul_one]
    _ ≤ ‖c‖ * ‖u - v‖ + ‖c‖ * ‖u - v‖ :=
      add_le_add (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) hb
    _ = _ := by rw [dist_eq_norm]; ring

lemma chart_offset_dist (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (l l' : MarkedLine)
    (hl : IsValidLine l) (hl' : IsValidLine l') :
    dist (offset (MarkedIsometricChart.line O c l)) (offset (MarkedIsometricChart.line O c l')) ≤
      dist (offset l) (offset l') + 2 * ‖c‖ * dist (direction l) (direction l') := by
  change dist (O (offset l - c + (inner ℝ c (direction l)) • direction l))
    (O (offset l' - c + (inner ℝ c (direction l')) • direction l')) ≤ _
  rw [LinearIsometryEquiv.dist_map, dist_eq_norm]
  have he : (offset l - c + (inner ℝ c (direction l)) • direction l) -
      (offset l' - c + (inner ℝ c (direction l')) • direction l') =
        (offset l - offset l') +
          ((inner ℝ c (direction l)) • direction l - (inner ℝ c (direction l')) • direction l') := by
    abel
  rw [he]
  calc
    _ ≤ ‖offset l - offset l'‖ +
        ‖(inner ℝ c (direction l)) • direction l - (inner ℝ c (direction l')) • direction l'‖ :=
      norm_add_le _ _
    _ ≤ _ := by
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact add_le_add le_rfl (projection_correction_dist c (direction l) (direction l') hl.1 hl'.1)

/-- Actual carrier distortion of the marked isometric chart. -/
theorem chart_carrier_dist_le (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (l l' : MarkedLine)
    (hl : IsValidLine l) (hl' : IsValidLine l') :
    dist (carrier (MarkedIsometricChart.line O c l)) (carrier (MarkedIsometricChart.line O c l')) ≤
      (1 + 2 * ‖c‖) * dist (carrier l) (carrier l') := by
  have hdir : dist (direction (MarkedIsometricChart.line O c l))
      (direction (MarkedIsometricChart.line O c l')) = dist (direction l) (direction l') :=
    O.dist_map _ _
  have hleft : dist (direction l) (direction l') ≤ dist (carrier l) (carrier l') := le_max_left _ _
  have hright : dist (offset l) (offset l') ≤ dist (carrier l) (carrier l') := le_max_right _ _
  have hoff := chart_offset_dist O c l l' hl hl'
  change max (dist (direction (MarkedIsometricChart.line O c l))
    (direction (MarkedIsometricChart.line O c l')))
    (dist (offset (MarkedIsometricChart.line O c l)) (offset (MarkedIsometricChart.line O c l'))) ≤ _
  rw [hdir]
  apply max_le
  · exact hleft.trans (le_mul_of_one_le_left dist_nonneg (by nlinarith [norm_nonneg c]))
  · calc
      _ ≤ dist (offset l) (offset l') + 2 * ‖c‖ * dist (direction l) (direction l') := hoff
      _ ≤ dist (carrier l) (carrier l') + 2 * ‖c‖ * dist (carrier l) (carrier l') :=
        add_le_add hright (mul_le_mul_of_nonneg_left hleft (by positivity))
      _ = _ := by ring

/-- The inverse chart recovers direction, offset, and the affine mark
exactly. Its translation is -O c. -/
theorem line_inverse (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (l : MarkedLine) :
    MarkedIsometricChart.line O.symm (-O c) (MarkedIsometricChart.line O c l) = l := by
  apply Prod.ext
  · apply Prod.ext
    · exact O.symm_apply_apply _
    · change O.symm (O (offset l - c + (inner ℝ c (direction l)) • direction l) - (-O c) +
        (inner ℝ (-O c) (O (direction l))) • O (direction l)) = offset l
      rw [inner_neg_left, LinearIsometryEquiv.inner_map_map]
      simp only [map_add, map_sub, map_neg, map_smul, LinearIsometryEquiv.symm_apply_apply]
      module
  · change mark l - inner ℝ c (direction l) - inner ℝ (-O c) (O (direction l)) = mark l
    rw [inner_neg_left, LinearIsometryEquiv.inner_map_map]
    ring

/-- The same explicit coefficient bounds reverse carrier distortion. -/
theorem carrier_dist_le_chart (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (l l' : MarkedLine)
    (hl : IsValidLine l) (hl' : IsValidLine l') :
    dist (carrier l) (carrier l') ≤ (1 + 2 * ‖c‖) *
      dist (carrier (MarkedIsometricChart.line O c l)) (carrier (MarkedIsometricChart.line O c l')) := by
  have hh := chart_carrier_dist_le O.symm (-O c)
    (MarkedIsometricChart.line O c l) (MarkedIsometricChart.line O c l')
    (MarkedIsometricChart.valid_line O c l hl) (MarkedIsometricChart.valid_line O c l' hl')
  simpa only [line_inverse, norm_neg, LinearIsometryEquiv.norm_map] using hh

/-- A chart centered within norm 1/2 distorts actual carrier distances
by at most two in both directions. No direction separation is used. -/
theorem carrier_dist_two_sided (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (hc : ‖c‖ ≤ 1 / 2)
    (l l' : MarkedLine) (hl : IsValidLine l) (hl' : IsValidLine l') :
    dist (carrier (MarkedIsometricChart.line O c l)) (carrier (MarkedIsometricChart.line O c l')) ≤
      2 * dist (carrier l) (carrier l') ∧
    dist (carrier l) (carrier l') ≤
      2 * dist (carrier (MarkedIsometricChart.line O c l)) (carrier (MarkedIsometricChart.line O c l')) := by
  have hcost : 1 + 2 * ‖c‖ ≤ 2 := by linarith only [hc]
  exact ⟨(chart_carrier_dist_le O c l l' hl hl').trans
      (mul_le_mul_of_nonneg_right hcost dist_nonneg),
    (carrier_dist_le_chart O c l l' hl hl').trans
      (mul_le_mul_of_nonneg_right hcost dist_nonneg)⟩

end MarkedIsometricCarrier
