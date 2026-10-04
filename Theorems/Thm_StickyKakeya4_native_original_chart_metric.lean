import Theorems.Thm_StickyKakeya4_native_original_parent_physical_data
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeOriginalChartMetric
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection

lemma carrier_coordinate_le {n : ℕ} (D : FiniteScaleSource n) (i k : Fin n) (j : Fin 4) :
    |direction (D.line i) j - direction (D.line k) j| ≤
      dist (wzCarrierPoint D i) (wzCarrierPoint D k) ∧
    |offset (D.line i) j - offset (D.line k) j| ≤
      dist (wzCarrierPoint D i) (wzCarrierPoint D k) := by
  have hd : dist (direction (D.line i)) (direction (D.line k)) ≤
      dist (wzCarrierPoint D i) (wzCarrierPoint D k) := by
    exact le_max_left _ _
  have hb : dist (offset (D.line i)) (offset (D.line k)) ≤
      dist (wzCarrierPoint D i) (wzCarrierPoint D k) := by
    exact le_max_right _ _
  have hdc : |direction (D.line i) j-direction (D.line k) j| ≤ dist (direction (D.line i)) (direction (D.line k)) := by
    simpa [Real.dist_eq] using PiLp.dist_apply_le (direction (D.line i)) (direction (D.line k)) j
  have hbc : |offset (D.line i) j-offset (D.line k) j| ≤ dist (offset (D.line i)) (offset (D.line k)) := by
    simpa [Real.dist_eq] using PiLp.dist_apply_le (offset (D.line i)) (offset (D.line k)) j
  exact ⟨hdc.trans hd, hbc.trans hb⟩

lemma slope_sub_le {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (i k : Fin n) (j : Fin 3) :
    |slope (D.line i) j - slope (D.line k) j| ≤
      6 * dist (wzCarrierPoint D i) (wzCarrierPoint D k) := by
  let r := dist (wzCarrierPoint D i) (wzCarrierPoint D k)
  have hi := h.2.1.1 i
  have hk := h.2.1.1 k
  have hip : 0 < direction (D.line i) (3 : Fin 4) := by linarith
  have hkp : 0 < direction (D.line k) (3 : Fin 4) := by linarith
  have hs := slope_bound (D.line k) (h.1.2.2.2.2.1 k) hk j
  have hx := (carrier_coordinate_le D i k j.castSucc).1
  have ht := (carrier_coordinate_le D i k (3 : Fin 4)).1
  have he : slope (D.line i) j - slope (D.line k) j =
      ((direction (D.line i) j.castSucc - direction (D.line k) j.castSucc) +
        slope (D.line k) j * (direction (D.line k) (3 : Fin 4) - direction (D.line i) (3 : Fin 4))) /
          direction (D.line i) (3 : Fin 4) := by
    unfold NativeOriginalCellChartGeometry.slope
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hip, div_le_iff₀ hip]
  have hb : |(direction (D.line i) j.castSucc - direction (D.line k) j.castSucc) +
        slope (D.line k) j * (direction (D.line k) (3 : Fin 4) - direction (D.line i) (3 : Fin 4))| ≤ 3*r := by
    calc
      _ ≤ |direction (D.line i) j.castSucc - direction (D.line k) j.castSucc| +
        |slope (D.line k) j| * |direction (D.line k) (3 : Fin 4) - direction (D.line i) (3 : Fin 4)| := by
          simpa [abs_mul] using abs_add_le
            (direction (D.line i) j.castSucc - direction (D.line k) j.castSucc)
            (slope (D.line k) j * (direction (D.line k) (3 : Fin 4) - direction (D.line i) (3 : Fin 4)))
      _ ≤ r + 2*r := add_le_add hx (mul_le_mul hs (by simpa [abs_sub_comm] using ht)
        (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have hr : 0 ≤ r := dist_nonneg
  nlinarith

/-- The height displacement from the original perpendicular offset is kept
explicit. A common marked slab alone does not bound this displacement. -/
lemma shiftedIntercept_sub_le {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (i k : Fin n) (a : ℝ) (j : Fin 3) :
    |shiftedIntercept (D.line i) (mesh D) (shift D a) j -
      shiftedIntercept (D.line k) (mesh D) (shift D a) j| ≤
      (3 + 6*|((shift D a : ℤ) : ℝ)*mesh D - offset (D.line k) (3 : Fin 4)|)/4 *
        dist (wzCarrierPoint D i) (wzCarrierPoint D k) := by
  let r := dist (wzCarrierPoint D i) (wzCarrierPoint D k)
  let s := ((shift D a : ℤ) : ℝ)*mesh D
  have hs := slope_bound (D.line i) (h.1.2.2.2.2.1 i) (h.2.1.1 i) j
  have hd := slope_sub_le h i k j
  have hx := (carrier_coordinate_le D i k j.castSucc).2
  have ht := (carrier_coordinate_le D i k (3 : Fin 4)).2
  have he : shiftedIntercept (D.line i) (mesh D) (shift D a) j -
      shiftedIntercept (D.line k) (mesh D) (shift D a) j =
      ((offset (D.line i) j.castSucc-offset (D.line k) j.castSucc) +
        slope (D.line i) j * (offset (D.line k) (3 : Fin 4)-offset (D.line i) (3 : Fin 4)) +
        (slope (D.line i) j-slope (D.line k) j)*(s-offset (D.line k) (3 : Fin 4)))/4 := by
    dsimp [shiftedIntercept, intercept, s]
    ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0:ℝ)<4)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<4)).mpr
  have hb : |(offset (D.line i) j.castSucc-offset (D.line k) j.castSucc) +
        slope (D.line i) j * (offset (D.line k) (3 : Fin 4)-offset (D.line i) (3 : Fin 4)) +
        (slope (D.line i) j-slope (D.line k) j)*(s-offset (D.line k) (3 : Fin 4))| ≤
      r + 2*r + (6*r)*|s-offset (D.line k) (3 : Fin 4)| := by
    calc
      _ ≤ |offset (D.line i) j.castSucc-offset (D.line k) j.castSucc| +
        |slope (D.line i) j| * |offset (D.line k) (3 : Fin 4)-offset (D.line i) (3 : Fin 4)| +
        |slope (D.line i) j-slope (D.line k) j| * |s-offset (D.line k) (3 : Fin 4)| := by
          have habc := (abs_add_le
            ((offset (D.line i) j.castSucc-offset (D.line k) j.castSucc) +
              slope (D.line i) j * (offset (D.line k) (3 : Fin 4)-offset (D.line i) (3 : Fin 4)))
            ((slope (D.line i) j-slope (D.line k) j)*(s-offset (D.line k) (3 : Fin 4)))).trans
            (add_le_add (abs_add_le _ _) le_rfl)
          simpa only [abs_mul] using habc
      _ ≤ _ := add_le_add (add_le_add hx (mul_le_mul hs
        (by simpa [abs_sub_comm] using ht) (abs_nonneg _) (by norm_num)))
          (mul_le_mul_of_nonneg_right hd (abs_nonneg _))
  dsimp [s,r] at hb ⊢
  nlinarith

end NativeOriginalChartMetric
