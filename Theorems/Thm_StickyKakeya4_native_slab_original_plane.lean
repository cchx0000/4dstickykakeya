import Theorems.Thm_StickyKakeya4_native_slab_plane_pullback
import Theorems.Thm_StickyKakeya4_native_slab_parent_normalization

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeSlabOriginalPlane
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeHorizontalGrainSlice NativeGrainQuotientInjection NativeReferenceXYGridLinear
open NativeDirectionRankDichotomy NativeIncidentAffineAnchorGeometry NativeGrainHeightProjectionTransport
open NativeSlabPlanePullback NativeSlabParentNormalization
open scoped Matrix.Norms.Elementwise

/-- Actual lower-rank plane in the ORIGINAL slope-vector space. -/
def originalPlane (N : ℕ) (hN : 0 < N) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (u : EuclideanSpace ℝ (Fin (ell-1))) (c : ℝ) : Submodule ℝ E4 :=
  (nativePlane P hP ell hell hell4 hd M xi u c).map (parentEquiv N hN p).symm.toLinearMap

def originalWitness {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (u : EuclideanSpace ℝ (Fin (ell-1))) (c : ℝ) : E4 :=
  (parentEquiv N hN p).symm (nativeWitness P hP ell hell hell4 hd M xi u
    (tangentCoordinates P ell hd (localHorizontalSlope D N p i)) c)

lemma originalPlane_finrank (N : ℕ) (hN : 0 < N) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (u : EuclideanSpace ℝ (Fin (ell-1))) (c : ℝ) (hu : ‖u‖=1) :
    Module.finrank ℝ (originalPlane N hN p P hP ell hell hell4 hd M xi u c)=ell-1 := by
  rw [originalPlane,LinearEquiv.finrank_map_eq]
  exact nativePlane_finrank P hP ell hell hell4 hd M xi u c hu

/-- The original tube index stays fixed. The constructed witness has
height one, so the complete affine error is divided by N exactly. -/
theorem original_slab_pullback {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (hN : 0 < N)
    (p : Parent) (i : Fin n) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (u : EuclideanSpace ℝ (Fin (ell-1)))
    (c r e : ℝ) (hu : ‖u‖=1)
    (hslab : |inner ℝ u (tangentCoordinates P ell hd (localHorizontalSlope D N p i))-c| ≤ r)
    (hres : ‖quotientMap P hP ell hell hell4 hd M (localHorizontalSlope D N p i)-xi‖ ≤ e) :
    Module.finrank ℝ (originalPlane N hN p P hP ell hell hell4 hd M xi u c)=ell-1 ∧
      originalWitness D N hN p i P hP ell hell hell4 hd M xi u c∈originalPlane N hN p P hP ell hell hell4 hd M xi u c ∧
      originalWitness D N hN p i P hP ell hell hell4 hd M xi u c (3:Fin 4)=1 ∧
      dist (slopeVector D i) (originalWitness D N hN p i P hP ell hell hell4 hd M xi u c) ≤ (2*r+e)/(N:ℝ) := by
  obtain ⟨hT,hQ⟩ := parent_coordinates D N p i P hP ell hell hell4 hd M
  have hv : parentDirection N p (slopeVector D i) (3:Fin 4)=1 := by rw [parentDirection_last,slopeVector_last]
  obtain ⟨_hRank,hmem,hw3,hclose⟩ := native_slab_pullback P hP ell hell hell4 hd M hM xi u c r e
    (parentDirection N p (slopeVector D i)) hv hu (by rw [hT]; exact hslab) (by rw [hQ]; exact hres)
  rw [hT] at hmem hw3 hclose
  let w := nativeWitness P hP ell hell hell4 hd M xi u
    (tangentCoordinates P ell hd (localHorizontalSlope D N p i)) c
  have horigmem : originalWitness D N hN p i P hP ell hell hell4 hd M xi u c∈
      originalPlane N hN p P hP ell hell hell4 hd M xi u c :=
    Submodule.mem_map.mpr ⟨w,hmem,rfl⟩
  refine ⟨originalPlane_finrank N hN p P hP ell hell hell4 hd M xi u c hu,horigmem,?_,?_⟩
  · exact hw3
  · have he := unparent_distance N p (parentDirection N p (slopeVector D i)) w (hv.trans hw3.symm)
    rw [unparent_parent N hN p] at he
    change dist (slopeVector D i) (unparentDirection N p w) ≤ _
    rw [he]
    exact div_le_div_of_nonneg_right hclose (Nat.cast_nonneg N)

/-- The rank-selection consumer receives literal distance to a constructed
original plane, not an auxiliary product-coordinate plane or witness premise. -/
theorem original_infDist {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (hN : 0 < N)
    (p : Parent) (i : Fin n) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (u : EuclideanSpace ℝ (Fin (ell-1)))
    (c r e : ℝ) (hu : ‖u‖=1)
    (hslab : |inner ℝ u (tangentCoordinates P ell hd (localHorizontalSlope D N p i))-c| ≤ r)
    (hres : ‖quotientMap P hP ell hell hell4 hd M (localHorizontalSlope D N p i)-xi‖ ≤ e) :
    Metric.infDist (slopeVector D i) (originalPlane N hN p P hP ell hell hell4 hd M xi u c:Set E4) ≤ (2*r+e)/(N:ℝ) := by
  have hh := original_slab_pullback D N hN p i P hP ell hell hell4 hd M hM xi u c r e hu hslab hres
  exact (Metric.infDist_le_dist_of_mem hh.2.1).trans hh.2.2.2

/-- One plane serves every original edge at the tested point. This is an
entry to fresh current-family rank selection; it asserts no inherited broadness. -/
theorem original_point_slab_near {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (hN : 0 < N)
    (p : Parent) (I : Finset (Fin n × Index)) (k : Index)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (u : EuclideanSpace ℝ (Fin (ell-1)))
    (c r e : ℝ) (hu : ‖u‖=1)
    (hres : ∀i,(i,k)∈I → ‖quotientMap P hP ell hell hell4 hd M (localHorizontalSlope D N p i)-xi‖ ≤ e) :
    Module.finrank ℝ (originalPlane N hN p P hP ell hell hell4 hd M xi u c)=ell-1 ∧
      ∀i,(i,k)∈I → |inner ℝ u (tangentCoordinates P ell hd (localHorizontalSlope D N p i))-c| ≤ r →
        Metric.infDist (slopeVector D i) (originalPlane N hN p P hP ell hell hell4 hd M xi u c:Set E4) ≤ (2*r+e)/(N:ℝ) := by
  refine ⟨originalPlane_finrank N hN p P hP ell hell hell4 hd M xi u c hu,?_⟩
  intro i hi hslab
  exact original_infDist D N hN p i P hP ell hell hell4 hd M hM xi u c r e hu hslab (hres i hi)

end NativeSlabOriginalPlane
