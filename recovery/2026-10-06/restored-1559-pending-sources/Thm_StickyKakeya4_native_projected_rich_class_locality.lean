import Theorems.Thm_StickyKakeya4_native_common_phi_source
import Theorems.Thm_StickyKakeya4_native_slab_grid_pullback

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeProjectedRichClassLocality
open StickyKakeya4 NativeOriginalParentSelection NativeHorizontalGrainSlice
open NativeGrainQuotientInjection NativeReferenceXYGridLinear NativeCommonPhiMetric NativeCommonPhiGrid
open NativeCommonPhiSource NativeSlabGridPullback NativeIncidentAffineAnchorGeometry
open NativeNormalizedCellAngularMenu

lemma phiCenter_distance {d : ℕ} {rho : ℝ} (hrho : 0< rho)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖phiCenter rho x-phiCenter rho y‖≤ ‖x-y‖+(d:ℝ)*rho := by
  have hx := phiCenter_error hrho x
  have hy := phiCenter_error hrho y
  have h1 := norm_sub_le (phiCenter rho x) x (phiCenter rho y)
  have h2 := norm_sub_le x y (phiCenter rho y)
  rw [norm_sub_rev (phiCenter rho x) x] at h1
  linarith only [hx,hy,h1,h2]

/-- Every literal rich sigma angular class lies near its actual surviving
anchor after tangent projection and rho-grid realization. This step uses
neither spatial offset coherence nor an angular AD premise. -/
theorem same_angular_cell_centers {n : ℕ} (D : FiniteScaleSource n) (N M : ℕ)
    (hM : 0< M) (p : Parent) (i j : Fin n)
    (P : Submodule ℝ E4) (ell : ℕ) (hd : Module.finrank ℝ P=ell-1)
    {rho : ℝ} (hrho : 0< rho)
    (hcell : angularCell D N M p i=angularCell D N M p j) :
    ‖phiCenter rho (tangentCoordinates P ell hd (localHorizontalSlope D N p i))-
      phiCenter rho (tangentCoordinates P ell hd (localHorizontalSlope D N p j))‖≤
      3*((64/(M:ℝ))/8)+((ell-1:ℕ):ℝ)*rho := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  rw [angularCell_readback D N M hM p i,angularCell_readback D N M hM p j] at hcell
  have hFull := same_angle_distance (by positivity : (0:ℝ)<(64/(M:ℝ))/8)
    (localHorizontalSlope D N p i) (localHorizontalSlope D N p j)
    (localHorizontalSlope_mem_heightKernel D N p i) (localHorizontalSlope_mem_heightKernel D N p j) hcell
  have hTangent := tangent_distance P ell hd (localHorizontalSlope D N p i) (localHorizontalSlope D N p j)
  exact (phiCenter_distance hrho _ _).trans (add_le_add_right (hTangent.trans hFull) _)

theorem same_angular_cell_ball {n : ℕ} (D : FiniteScaleSource n) (N M : ℕ)
    (hM : 0< M) (p : Parent) (i j : Fin n)
    (P : Submodule ℝ E4) (ell : ℕ) (hell : ell≤ 3) (hd : Module.finrank ℝ P=ell-1)
    {rho : ℝ} (hrho : 0< rho) (hscale : 4*rho≤ 64/(M:ℝ))
    (hcell : angularCell D N M p i=angularCell D N M p j) :
    dist (phiCenter rho (tangentCoordinates P ell hd (localHorizontalSlope D N p i)))
      (phiCenter rho (tangentCoordinates P ell hd (localHorizontalSlope D N p j)))≤ 64/(M:ℝ) := by
  have hh := same_angular_cell_centers D N M hM p i j P ell hd hrho hcell
  have hellR : ((ell-1:ℕ):ℝ)≤ 2 := by exact_mod_cast (show ell-1≤ 2 by omega)
  have hm := mul_le_mul_of_nonneg_right hellR hrho.le
  rw [dist_eq_norm]
  nlinarith only [hh,hm,hscale]

end NativeProjectedRichClassLocality
