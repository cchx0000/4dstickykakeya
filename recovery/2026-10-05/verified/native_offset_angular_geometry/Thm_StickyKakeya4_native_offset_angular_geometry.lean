import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_linear
import Theorems.Thm_StickyKakeya4_native_incident_affine_anchor_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000
noncomputable section
namespace NativeOffsetAngularGeometry
open Classical Finset StickyKakeya4 NativeHorizontalGrainSlice NativeHorizontalGraphCoordinates
open NativeGrainQuotientInjection NativeReferenceXYGridLinear
open scoped BigOperators Matrix.Norms.Elementwise

/-- A true Euclidean action bound from the elementwise matrix norm. -/
theorem matrix_action_general (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (x : EuclideanSpace ℝ (Fin (ell-1))) :
    ‖M.toEuclideanLin x‖ ≤ 4*‖M‖*‖x‖ := by
  have hout (i : Fin (4-ell)) : |M.toEuclideanLin x i| ≤ ((ell-1:ℕ):ℝ)*‖M‖*‖x‖ := by
    change |∑j : Fin (ell-1),M i j*x j| ≤ _
    calc
      _ ≤ ∑j : Fin (ell-1),|M i j*x j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑_j : Fin (ell-1),‖M‖*‖x‖ := by
        apply sum_le_sum
        intro j _
        rw [abs_mul]
        apply mul_le_mul _ _ (abs_nonneg _) (norm_nonneg _)
        · simpa only [Real.norm_eq_abs] using (Matrix.norm_le_iff (norm_nonneg M)).mp (le_refl ‖M‖) i j
        · simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
      _ = _ := by simp; ring
  have hab : (((ell-1:ℕ):ℝ))*((4-ell:ℕ):ℝ) ≤ 4 := by
    exact_mod_cast (show (ell-1)*(4-ell) ≤ 4 by interval_cases ell <;> norm_num)
  have hh := mul_le_mul_of_nonneg_right hab (mul_nonneg (norm_nonneg M) (norm_nonneg x))
  calc
    _ ≤ ∑i : Fin (4-ell),|M.toEuclideanLin x i| := euclidean_norm_le_sum _
    _ ≤ ∑_i : Fin (4-ell),((ell-1:ℕ):ℝ)*‖M‖*‖x‖ := sum_le_sum (fun i _ => hout i)
    _ ≤ _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; nlinarith only [hh]

/-- Comparing two literal affine graph residuals. Different point labels may
have different matrices; their variation is charged explicitly. -/
theorem quotient_difference (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M N : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (x y : E4) :
    ‖quotientMap P hP ell hell hell4 hd M x-quotientMap P hP ell hell hell4 hd N y‖ ≤
      2*‖x-y‖+4*‖M-N‖*‖y‖ := by
  have he : quotientMap P hP ell hell hell4 hd M x-quotientMap P hP ell hell hell4 hd N y=
      quotientMap P hP ell hell hell4 hd M (x-y)-
        (M-N).toEuclideanLin (tangentCoordinates P ell hd y) := by
    simp only [quotientMap,LinearMap.sub_apply,LinearMap.comp_apply,map_sub]
    abel
  rw [he]
  have h1 := quotient_norm_le P hP ell hell hell4 hd M hM (x-y)
  have h2 := matrix_action_general ell hell hell4 (M-N) (tangentCoordinates P ell hd y)
  have h3 := mul_le_mul_of_nonneg_left (tangent_norm_le P ell hd y)
    (show 0 ≤ 4*‖M-N‖ by positivity)
  exact (norm_sub_le _ _).trans (add_le_add h1 (h2.trans h3))

/-- If two retained tubes have the same coarse angular label, their point
anchor offsets are close. The affine relation is only needed on those actual
incidences, and the slope-field variation remains explicit. -/
theorem incident_offsets_close (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M N : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (x y : E4) (xi eta : EuclideanSpace ℝ (Fin (4-ell)))
    (error angular variation : ℝ) (hy : ‖y‖ ≤ 2)
    (hx : ‖quotientMap P hP ell hell hell4 hd M x-xi‖ ≤ error)
    (he : ‖quotientMap P hP ell hell hell4 hd N y-eta‖ ≤ error)
    (hang : ‖x-y‖ ≤ angular) (hvar : ‖M-N‖ ≤ variation) :
    ‖xi-eta‖ ≤ 2*error+2*angular+8*variation := by
  have hv : 0 ≤ variation := (norm_nonneg _).trans hvar
  have hq := quotient_difference P hP ell hell hell4 hd M N hM x y
  have hscale : 4*‖M-N‖*‖y‖ ≤ 8*variation := by
    have hprod := mul_le_mul hvar hy (norm_nonneg _) hv
    nlinarith only [hprod]
  have hid : xi-eta=(xi-quotientMap P hP ell hell hell4 hd M x)+
      (quotientMap P hP ell hell hell4 hd M x-quotientMap P hP ell hell hell4 hd N y)+
      (quotientMap P hP ell hell hell4 hd N y-eta) := by abel
  have hn := (norm_add_le (xi-quotientMap P hP ell hell hell4 hd M x+
      (quotientMap P hP ell hell hell4 hd M x-quotientMap P hP ell hell hell4 hd N y))
      (quotientMap P hP ell hell hell4 hd N y-eta)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  rw [←hid] at hn
  have hxr : ‖xi-quotientMap P hP ell hell hell4 hd M x‖ ≤ error := by
    rw [norm_sub_rev]; exact hx
  linarith only [hn,hxr,he,hq,hscale,hang]

end NativeOffsetAngularGeometry
