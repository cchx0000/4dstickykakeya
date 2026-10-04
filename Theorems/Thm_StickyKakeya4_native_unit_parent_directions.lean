import Theorems.Thm_StickyKakeya4_native_unit_parent_normalization
import Theorems.Thm_StickyKakeya4_native_original_slope_cube_packing
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeUnitParentDirections
open Classical StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeUnitParentNormalization NativeOriginalSlopeCubePacking

lemma slope_newLine (line : MarkedLine) (m : ℝ) (k : ℤ) (p : Parent) (j : Fin 3) :
    slope (newLine line m k p) j=newSlope line p j := by
  unfold NativeOriginalCellChartGeometry.slope newLine
  rw [NativeGraphMarkedLine.direction_castSucc,NativeGraphMarkedLine.direction_fourth]
  have hn : ‖northSlopeLift (newSlope line p)‖ ≠ 0 :=
    (zero_lt_one.trans_le (northSlopeLift_norm_ge_one _)).ne'
  field_simp

/-- Direction coordinates alone control the chart slope, independently of
absolute affine marks or carrier offsets. -/
lemma slope_sub_le_direction_dist (line line' : MarkedLine) (hv : IsValidLine line')
    (hc : (1/2:ℝ) ≤ direction line (3:Fin 4))
    (hc' : (1/2:ℝ) ≤ direction line' (3:Fin 4)) (j : Fin 3) :
    |slope line j-slope line' j| ≤ 6*dist (direction line) (direction line') := by
  have hip : 0 < direction line (3:Fin 4) := by linarith
  have hkp : 0 < direction line' (3:Fin 4) := by linarith
  have hs := slope_bound line' hv hc' j
  have hx : |direction line j.castSucc-direction line' j.castSucc| ≤ dist (direction line) (direction line') := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le (direction line) (direction line') j.castSucc
  have ht : |direction line' (3:Fin 4)-direction line (3:Fin 4)| ≤ dist (direction line) (direction line') := by
    simpa only [Real.dist_eq,abs_sub_comm] using PiLp.dist_apply_le (direction line) (direction line') (3:Fin 4)
  have he : slope line j-slope line' j=
      ((direction line j.castSucc-direction line' j.castSucc)+
        slope line' j*(direction line' (3:Fin 4)-direction line (3:Fin 4)))/direction line (3:Fin 4) := by
    unfold NativeOriginalCellChartGeometry.slope
    field_simp
    ring
  rw [he,abs_div,abs_of_pos hip,div_le_iff₀ hip]
  have hm : |slope line' j*(direction line' (3:Fin 4)-direction line (3:Fin 4))| ≤ 
      2*dist (direction line) (direction line') := by
    rw [abs_mul]
    exact mul_le_mul hs ht (abs_nonneg _) (by norm_num)
  have hb := (abs_add_le (direction line j.castSucc-direction line' j.castSucc)
    (slope line' j*(direction line' (3:Fin 4)-direction line (3:Fin 4)))).trans (add_le_add hx hm)
  nlinarith [dist_nonneg (x:=direction line) (y:=direction line')]

/-- The chosen original parent retains true direction separation with a
fixed explicit chart cost. It is not asserted at the wider delta/2 tube scale. -/
theorem normalized_direction_separation {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (p : Parent) (i j : Fin n)
    (hi : parentLabel D a 1 i=p) (hj : parentLabel D a 1 j=p) (hne : i ≠ j) :
    D.thickness/48 ≤ dist
      (direction (newLine (D.line i) (mesh D) (shift D a) p))
      (direction (newLine (D.line j) (mesh D) (shift D a) p)) := by
  obtain ⟨_hvi,hci,_hsi⟩ := padded_line_common_slab D a p i hi
  obtain ⟨hvj,hcj,_hsj⟩ := padded_line_common_slab D a p j hj
  have hs : dist (slope (D.line i)) (slope (D.line j)) ≤ 
      6*dist (direction (newLine (D.line i) (mesh D) (shift D a) p))
        (direction (newLine (D.line j) (mesh D) (shift D a) p)) := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro k
    have hh := slope_sub_le_direction_dist _ _ hvj hci hcj k
    rw [slope_newLine,slope_newLine] at hh
    change |(slope (D.line i) k-(p.1 k:ℝ))-(slope (D.line j) k-(p.1 k:ℝ))| ≤ _ at hh
    simpa only [Real.dist_eq,sub_sub_sub_cancel_right] using hh
  have hd := direction_dist_le_eight_slope_dist (D.line i) (D.line j)
    (h.1.2.2.2.2.1 i) (h.1.2.2.2.2.1 j) (h.2.1.1 i) (h.2.1.1 j)
  have hsep := h.1.2.2.2.2.2.2.2.2.2.1 i j hne
  linarith
end NativeUnitParentDirections
