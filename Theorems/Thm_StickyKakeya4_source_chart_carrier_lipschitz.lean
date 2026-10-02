import Theorems.Thm_StickyKakeya4_actual_slope_source_bounds
import Theorems.Thm_StickyKakeya4_north_slope_direction_density
import Theorems.Thm_StickyKakeya4_actual_packing_reference_source

/-!
The original carrier metric controls both actual slope and intercept
differences on the selected bounded chart. These estimates give uniform
bounded support after recentering a localized carrier block; they do not
assume regularity of the measurable selector as a function of direction.
-/

namespace StickyKakeya4.ActualSlopeSource

theorem northGraphIntercept_sub_le_carrier_components
    (line line' : MarkedLine) (hslope : ‖northGraphSlope line‖ ≤ 1)
    (R : ℝ) (hoffset : ‖offset line'‖ ≤ R) :
    ‖northGraphIntercept line - northGraphIntercept line'‖ ≤
      2 * ‖offset line - offset line'‖ +
      R * ‖northGraphSlope line - northGraphSlope line'‖ := by
  have heq : northGraphIntercept line - northGraphIntercept line' =
      horizontalProjection (offset line - offset line') -
        (offset line (3 : Fin 4) - offset line' (3 : Fin 4)) • northGraphSlope line -
        offset line' (3 : Fin 4) • (northGraphSlope line - northGraphSlope line') := by
    rw [horizontalProjection_sub]
    simp only [northGraphIntercept, sub_smul, smul_sub]
    module
  have hdiff : |offset line (3 : Fin 4) - offset line' (3 : Fin 4)| ≤
      ‖offset line - offset line'‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
      PiLp.norm_apply_le (offset line - offset line') (3 : Fin 4)
  have hcoord : |offset line' (3 : Fin 4)| ≤ R := by
    have h : |offset line' (3 : Fin 4)| ≤ ‖offset line'‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (offset line') (3 : Fin 4)
    exact h.trans hoffset
  have hfirst : ‖(offset line (3 : Fin 4) - offset line' (3 : Fin 4)) •
      northGraphSlope line‖ ≤ ‖offset line - offset line'‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ ‖offset line - offset line'‖ * 1 :=
        mul_le_mul hdiff hslope (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_one _
  have hsecond : ‖offset line' (3 : Fin 4) •
      (northGraphSlope line - northGraphSlope line')‖ ≤
      R * ‖northGraphSlope line - northGraphSlope line'‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hcoord (norm_nonneg _)
  rw [heq]
  have h₁ := norm_sub_le (horizontalProjection (offset line - offset line'))
    ((offset line (3 : Fin 4) - offset line' (3 : Fin 4)) • northGraphSlope line)
  have h₂ := norm_sub_le (horizontalProjection (offset line - offset line') -
      (offset line (3 : Fin 4) - offset line' (3 : Fin 4)) • northGraphSlope line)
    (offset line' (3 : Fin 4) • (northGraphSlope line - northGraphSlope line'))
  have hhor := norm_horizontalProjection_le (offset line - offset line')
  linarith

theorem actual_source_chart_dist_le_carrier
    (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (a a₀ : E3) (ha : ‖a‖ ≤ 1) (ha₀ : ‖a₀‖ ≤ 1)
    (R : ℝ) (hoffset : ‖offset (slopeLine selector hmeas hvalid hselector a₀)‖ ≤ R) :
    ‖a - a₀‖ ≤ 6 * dist (slopeCarrierMap selector hmeas hvalid hselector a)
      (slopeCarrierMap selector hmeas hvalid hselector a₀) ∧
    ‖intercept selector hmeas hvalid hselector a -
      intercept selector hmeas hvalid hselector a₀‖ ≤
      (2 + 6 * R) * dist (slopeCarrierMap selector hmeas hvalid hselector a)
        (slopeCarrierMap selector hmeas hvalid hselector a₀) := by
  let l := slopeLine selector hmeas hvalid hselector a
  let l₀ := slopeLine selector hmeas hvalid hselector a₀
  let d := dist (slopeCarrierMap selector hmeas hvalid hselector a)
    (slopeCarrierMap selector hmeas hvalid hselector a₀)
  have hR : 0 ≤ R := (norm_nonneg _).trans hoffset
  have hdir : dist (northSlopeDirection a : E4) (northSlopeDirection a₀ : E4) ≤ d := by
    change dist (northSlopeDirection a : E4) (northSlopeDirection a₀ : E4) ≤
      max (dist (direction l) (direction l₀)) (dist (offset l) (offset l₀))
    dsimp only [l, l₀]
    rw [direction_slopeLine, direction_slopeLine]
    exact le_max_left _ _
  have hoff : ‖offset l - offset l₀‖ ≤ d := by
    change ‖offset l - offset l₀‖ ≤
      max (dist (direction l) (direction l₀)) (dist (offset l) (offset l₀))
    rw [← dist_eq_norm]
    exact le_max_right _ _
  have hslope : ‖a - a₀‖ ≤ 6 * d := by
    have h := northSlopeDirection_inverse_dist_le_six_mul ha ha₀
    rw [dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdir (by norm_num))
  refine ⟨hslope, ?_⟩
  have hl : ‖northGraphSlope l‖ ≤ 1 := by
    simpa only [l, slope_slopeLine] using ha
  have h := northGraphIntercept_sub_le_carrier_components l l₀ hl R hoffset
  change ‖intercept selector hmeas hvalid hselector a -
      intercept selector hmeas hvalid hselector a₀‖ ≤ _ at h
  rw [show northGraphSlope l = a by exact slope_slopeLine _ _ _ _ _,
    show northGraphSlope l₀ = a₀ by exact slope_slopeLine _ _ _ _ _] at h
  calc
    _ ≤ 2 * ‖offset l - offset l₀‖ + R * ‖a - a₀‖ := h
    _ ≤ 2 * d + R * (6 * d) := by gcongr
    _ = (2 + 6 * R) * d := by ring

end StickyKakeya4.ActualSlopeSource
