import Theorems.Thm_StickyKakeya4_native_slab_original_plane
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_local
import Theorems.Thm_StickyKakeya4_native_quotient_grid_centers

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeSlabGridPullback
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeHorizontalGrainSlice NativeGrainQuotientInjection NativeGrainQuotientBins
open NativeReferenceXYGridLinear NativeReferenceXYGridMaps NativeReferenceXYGridLocal
open NativeDirectionRankDichotomy NativeIncidentAffineAnchorGeometry NativeSlabOriginalPlane
open scoped Matrix.Norms.Elementwise

/-- The literal common-Phi grid label, realized at its standard cell center. -/
def phiCenter {d : ℕ} (rho : ℝ) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (NativeQuotientGridCenters.center rho (label rho x))

lemma phiCenter_error {d : ℕ} {rho : ℝ} (hrho : 0 < rho) (x : EuclideanSpace ℝ (Fin d)) :
    ‖x-phiCenter rho x‖ ≤ (d:ℝ)*rho/2 := by
  have hh : ‖x-phiCenter rho x‖ ≤ (d:ℝ)*(rho/2) := by
    apply euclidean_coord_bound
    intro j
    exact floor_center_error hrho (x j)
  linarith only [hh]

lemma grid_slab_transfer {d : ℕ} {rho : ℝ} (hrho : 0 < rho)
    (u x : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖=1) (c r : ℝ)
    (hslab : |inner ℝ u (phiCenter rho x)-c| ≤ r) :
    |inner ℝ u x-c| ≤ r+(d:ℝ)*rho/2 := by
  have hc := abs_real_inner_le_norm u (x-phiCenter rho x)
  rw [hu,one_mul] at hc
  have herr := phiCenter_error hrho x
  have htri := abs_sub_le (inner ℝ u x) (inner ℝ u (phiCenter rho x)) c
  rw [←inner_sub_right] at htri
  linarith only [hc,herr,htri,hslab]

/-- A slab of the actual tangent grid centers gives a lower-rank ORIGINAL
slope plane with every rounding and normalization factor explicit. -/
theorem original_grid_infDist {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (hN : 0 < N)
    (p : Parent) (i : Fin n) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (u : EuclideanSpace ℝ (Fin (ell-1)))
    (c r e rho : ℝ) (hu : ‖u‖=1) (hrho : 0 < rho)
    (hslab : |inner ℝ u (phiCenter rho (tangentCoordinates P ell hd (localHorizontalSlope D N p i)))-c| ≤ r)
    (hres : ‖quotientMap P hP ell hell hell4 hd M (localHorizontalSlope D N p i)-xi‖ ≤ e) :
    Metric.infDist (slopeVector D i) (originalPlane N hN p P hP ell hell hell4 hd M xi u c:Set E4) ≤
      (2*r+((ell-1:ℕ):ℝ)*rho+e)/(N:ℝ) := by
  have hs := grid_slab_transfer hrho u (tangentCoordinates P ell hd (localHorizontalSlope D N p i)) hu c r hslab
  have hh := original_infDist D N hN p i P hP ell hell hell4 hd M hM xi u c
    (r+((ell-1:ℕ):ℝ)*rho/2) e hu hs hres
  convert hh using 1
  ring

/-- The same explicitly constructed plane serves every original tube label
at the tested point, including when the test is imposed on common-Phi bins. -/
theorem original_grid_point_slab_near {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (hN : 0 < N)
    (p : Parent) (I : Finset (Fin n × Index)) (k : Index)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (u : EuclideanSpace ℝ (Fin (ell-1)))
    (c r e rho : ℝ) (hu : ‖u‖=1) (hrho : 0 < rho)
    (hres : ∀i,(i,k)∈I → ‖quotientMap P hP ell hell hell4 hd M (localHorizontalSlope D N p i)-xi‖ ≤ e) :
    Module.finrank ℝ (originalPlane N hN p P hP ell hell hell4 hd M xi u c)=ell-1 ∧
      ∀i,(i,k)∈I →
        |inner ℝ u (phiCenter rho (tangentCoordinates P ell hd (localHorizontalSlope D N p i)))-c| ≤ r →
        Metric.infDist (slopeVector D i) (originalPlane N hN p P hP ell hell hell4 hd M xi u c:Set E4) ≤
          (2*r+((ell-1:ℕ):ℝ)*rho+e)/(N:ℝ) := by
  refine ⟨originalPlane_finrank N hN p P hP ell hell hell4 hd M xi u c hu,?_⟩
  intro i hi hslab
  exact original_grid_infDist D N hN p i P hP ell hell hell4 hd M hM xi u c r e rho hu hrho hslab (hres i hi)

end NativeSlabGridPullback
