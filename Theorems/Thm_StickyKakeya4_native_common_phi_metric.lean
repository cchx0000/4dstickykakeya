import Theorems.Thm_StickyKakeya4_native_offset_angular_geometry
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_angular_cap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeCommonPhiMetric
open Classical Finset StickyKakeya4 NativeHorizontalGrainSlice NativeGrainQuotientInjection
open NativeReferenceXYGridLinear NativeOffsetAngularGeometry
open scoped Matrix.Norms.Elementwise

/-- Freeze both the field and affine offset at one actual anchor. The
matrix norm is elementwise; its Euclidean action costs the explicit factor8. -/
theorem frozen_residual (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F F0 : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF0 : ‖F0‖ ≤ (1/4:ℝ))
    (w : E4) (hw : ‖w‖ ≤ 2)
    (xi xi0 : EuclideanSpace ℝ (Fin (4-ell))) (error variation offset : ℝ)
    (hres : ‖quotientMap P hP ell hell hell4 hd F w-xi‖ ≤ error)
    (hvar : ‖F-F0‖ ≤ variation) (hoff : ‖xi-xi0‖ ≤ offset) :
    ‖quotientMap P hP ell hell hell4 hd F0 w-xi0‖ ≤ error+8*variation+offset := by
  have hv : 0 ≤ variation := (norm_nonneg _).trans hvar
  have hdiff := quotient_difference P hP ell hell hell4 hd F0 F hF0 w w
  simp only [sub_self,norm_zero,mul_zero,zero_add] at hdiff
  rw [norm_sub_rev F0 F] at hdiff
  have hprod := mul_le_mul hvar hw (norm_nonneg _) hv
  have h1 := norm_sub_le_norm_sub_add_norm_sub
    (quotientMap P hP ell hell hell4 hd F0 w) (quotientMap P hP ell hell hell4 hd F w) xi0
  have h2 := norm_sub_le_norm_sub_add_norm_sub
    (quotientMap P hP ell hell hell4 hd F w) xi xi0
  linarith only [h1,h2,hdiff,hprod,hres,hoff]

/-- Literal proximity to the common graph in the fixed orthonormal frame. -/
lemma normal_graph_error (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (w : E4) (xi : EuclideanSpace ℝ (Fin (4-ell))) :
    ‖NativeReferenceXYGridLinear.normalCoordinates P hP ell hell hell4 hd w-
      (xi+F.toEuclideanLin (tangentCoordinates P ell hd w))‖=
      ‖quotientMap P hP ell hell hell4 hd F w-xi‖ := by
  congr 1
  simp only [quotientMap,LinearMap.sub_apply,LinearMap.comp_apply]
  abel

/-- Forward comparison needs no graph assumption: the fixed tangent
coordinate map is a contraction on all original directions. -/
lemma tangent_distance (P : Submodule ℝ E4) (ell : ℕ) (hd : Module.finrank ℝ P=ell-1)
    (x y : E4) :
    ‖tangentCoordinates P ell hd x-tangentCoordinates P ell hd y‖ ≤ ‖x-y‖ := by
  rw [←map_sub]
  exact tangent_norm_le P ell hd (x-y)

/-- Full directions are controlled by tangent separation plus the actual
normal error about one fixed affine graph. -/
theorem full_distance (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ‖F‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (x y : E4)
    (hx : x∈heightKernel) (hy : y∈heightKernel) (B : ℝ)
    (hxr : ‖quotientMap P hP ell hell hell4 hd F x-xi‖ ≤ B)
    (hyr : ‖quotientMap P hP ell hell hell4 hd F y-xi‖ ≤ B) :
    ‖x-y‖ ≤ 2*‖tangentCoordinates P ell hd x-tangentCoordinates P ell hd y‖+2*B := by
  have hq := norm_sub_le_norm_sub_add_norm_sub
    (quotientMap P hP ell hell hell4 hd F x) xi (quotientMap P hP ell hell hell4 hd F y)
  rw [norm_sub_rev xi] at hq
  have hh := horizontal_inverse P hP ell hell hell4 hd F hF (heightKernel.sub_mem hx hy)
  rw [map_sub,map_sub] at hh
  linarith only [hh,hq,hxr,hyr]

/-- A tangent sigma-ball centered at an actual direction is contained in
a full angular ball with the displayed fixed loss when sigma≥rho. -/
theorem tangent_ball_inverse (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ‖F‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (x y : E4)
    (hx : x∈heightKernel) (hy : y∈heightKernel) (rho sigma E : ℝ)
    (hE : 0 ≤ E) (hrs : rho ≤ sigma)
    (hxr : ‖quotientMap P hP ell hell hell4 hd F x-xi‖ ≤ E*rho)
    (hyr : ‖quotientMap P hP ell hell hell4 hd F y-xi‖ ≤ E*rho)
    (hball : ‖tangentCoordinates P ell hd x-tangentCoordinates P ell hd y‖ ≤ sigma) :
    ‖x-y‖ ≤ (2+2*E)*sigma := by
  have hh := full_distance P hP ell hell hell4 hd F hF xi x y hx hy (E*rho) hxr hyr
  have hs := mul_le_mul_of_nonneg_left hrs hE
  nlinarith only [hh,hball,hs]

/-- For an arbitrary tangent-ball center, choose any occupied direction
inside it; all other occupied directions lie in this full angular ball. -/
theorem tangent_ball_pair_inverse (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ‖F‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (x y : E4)
    (hx : x∈heightKernel) (hy : y∈heightKernel) (rho sigma E : ℝ)
    (hE : 0 ≤ E) (hrs : rho ≤ sigma)
    (hxr : ‖quotientMap P hP ell hell hell4 hd F x-xi‖ ≤ E*rho)
    (hyr : ‖quotientMap P hP ell hell hell4 hd F y-xi‖ ≤ E*rho)
    (center : EuclideanSpace ℝ (Fin (ell-1)))
    (hballx : ‖tangentCoordinates P ell hd x-center‖ ≤ sigma)
    (hbally : ‖tangentCoordinates P ell hd y-center‖ ≤ sigma) :
    ‖x-y‖ ≤ (4+2*E)*sigma := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (tangentCoordinates P ell hd x) center
    (tangentCoordinates P ell hd y)
  rw [norm_sub_rev center] at ht
  have hh := full_distance P hP ell hell hell4 hd F hF xi x y hx hy (E*rho) hxr hyr
  have hs := mul_le_mul_of_nonneg_left hrs hE
  nlinarith only [hh,ht,hballx,hbally,hs]

end NativeCommonPhiMetric
