import Theorems.Thm_StickyKakeya4_native_horizontal_graph_coordinates
import Theorems.Thm_StickyKakeya4_native_parent_horizontal_readback
import Theorems.Thm_StickyKakeya4_native_actual_horizontal_grain_slice
import Theorems.Thm_StickyKakeya4_native_parent_grain_incidence_cleanup

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeGrainQuotientGeometry
open Classical Finset StickyKakeya4 NativeHorizontalGrainSlice NativeProjectorCellChart
open NativeSelectedHorizontalGraphChart NativeHorizontalGraphCoordinates
open NativeCommonCubicalMesh NativeOriginalParentSelection NativeSquaredGrainQueries
open NativeSpatialAngularGeometry NativeOriginalCellChartGeometry WeightedRichDirectionalLayers RichDirectionalLayers
open NativeActualProjectedGrainCount NativeOriginalPacketReference NativeParentGrainIncidenceCleanup

/-- The actual graph quotient, with the reference plane held fixed. -/
def residual (P Q : Submodule ℝ E4) : E4 →ₗ[ℝ] E4 :=
  Pᗮ.starProjection.toLinearMap-
    (Pᗮ.subtype.comp (totalGraph P Q)).comp P.orthogonalProjectionOnto.toLinearMap

lemma residual_apply (P Q : Submodule ℝ E4) (x : E4) :
    residual P Q x=Pᗮ.starProjection x-(totalGraph P Q (P.orthogonalProjectionOnto x):E4) := rfl

lemma residual_norm (P Q : Submodule ℝ E4) (x : E4) :
    ‖residual P Q x‖ ≤ (5/4:ℝ)*‖x‖ := by
  have hg := totalGraph_norm P Q (P.orthogonalProjectionOnto x)
  have hp := P.norm_orthogonalProjectionOnto_apply_le x
  have hn := Pᗮ.norm_starProjection_apply_le x
  have ht := norm_sub_le (Pᗮ.starProjection x) (totalGraph P Q (P.orthogonalProjectionOnto x):E4)
  change ‖(totalGraph P Q (P.orthogonalProjectionOnto x):E4)‖ ≤ _ at hg
  rw [residual_apply]
  linarith

lemma residual_eq_zero_of_mem (P Q : Submodule ℝ E4)
    (hd : Module.finrank ℝ P=Module.finrank ℝ Q) (hc : cell P=cell Q)
    {x : E4} (hx : x∈Q) : residual P Q x=0 := by
  obtain ⟨p,rfl⟩ := (totalGraph_characterization P Q hd hc x).mp hx
  rw [residual_apply,map_add,map_add]
  rw [P.starProjection_orthogonal_apply_eq_zero p.property,
    Pᗮ.starProjection_mem_subspace_eq_self,
    P.orthogonalProjectionOnto_mem_subspace_eq_self,
    P.orthogonalProjectionOnto_apply_of_mem_orthogonal (totalGraph P Q p).property]
  simp only [zero_add,add_zero,sub_self]

/-- Thick plane membership gives a quotient error, not exact collinearity. -/
theorem residual_norm_le_infDist (P Q : Submodule ℝ E4)
    (hd : Module.finrank ℝ P=Module.finrank ℝ Q) (hc : cell P=cell Q) (x : E4) :
    ‖residual P Q x‖ ≤ (5/4:ℝ)*Metric.infDist x (Q:Set E4) := by
  have hz := residual_eq_zero_of_mem P Q hd hc (Q.starProjection_apply_mem x)
  have hh := residual_norm P Q (x-Q.starProjection x)
  rw [map_sub,hz,sub_zero,NativeEqualRankPlaneTransfer.projection_residual_eq_infDist] at hh
  exact hh

/-- Fixed orthonormal coordinates of the actual horizontal graph quotient. -/
def coordinates (P Q : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) : E4 →ₗ[ℝ] EuclideanSpace ℝ (Fin (4-ell)) :=
  ((normalBasis P hP ell hell hell4 hd).repr.toLinearMap.comp
    (normalSpace P).orthogonalProjectionOnto.toLinearMap).comp (residual P Q)

lemma coordinates_norm_le_infDist (P Q : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (hPQ : Module.finrank ℝ P=Module.finrank ℝ Q) (hc : cell P=cell Q) (x : E4) :
    ‖coordinates P Q hP ell hell hell4 hd x‖ ≤ (5/4:ℝ)*Metric.infDist x (Q:Set E4) := by
  change ‖(normalBasis P hP ell hell hell4 hd).repr
    ((normalSpace P).orthogonalProjectionOnto (residual P Q x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact ((normalSpace P).norm_orthogonalProjectionOnto_apply_le _).trans
    (residual_norm_le_infDist P Q hPQ hc x)

/-- The physical parent contributes precisely N/512 to horizontal thickness. -/
theorem parent_coordinates_difference {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (parent : Parent) (P R : Submodule ℝ E4)
    (hP : P≤heightKernel) (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (hPR : Module.finrank ℝ P=Module.finrank ℝ (sliceSpace R))
    (hc : cell P=cell (sliceSpace R))
    {v x y : E4} {H : ℝ} (hvR : v∈R) (hv : v (3:Fin 4)=1) (hvn : ‖v‖ ≤ 2)
    (hxy : x (3:Fin 4)=y (3:Fin 4)) (hnear : Metric.infDist (x-y) (R:Set E4) ≤ H) :
    ‖coordinates P (sliceSpace R) hP ell hell hell4 hd
      (NativeLocalParentPhysicalMap.physicalMap D a N parent x)-
      coordinates P (sliceSpace R) hP ell hell hell4 hd
      (NativeLocalParentPhysicalMap.physicalMap D a N parent y)‖ ≤
        (15/4:ℝ)*((N:ℝ)/512)*H := by
  have hh := near_horizontal_slice R hvR hv hvn hnear
  have he : removeHeight v (x-y)=x-y := by
    change x-y-(x (3:Fin 4)-y (3:Fin 4)) • v=x-y
    rw [hxy,sub_self,zero_smul,sub_zero]
  rw [he] at hh
  rw [←map_sub]
  have hquot := coordinates_norm_le_infDist P (sliceSpace R) hP ell hell hell4 hd hPR hc
    (NativeLocalParentPhysicalMap.physicalMap D a N parent x-
      NativeLocalParentPhysicalMap.physicalMap D a N parent y)
  rw [NativeParentHorizontalReadback.physical_map_horizontal_infDist D a N parent x y hxy R] at hquot
  have hscale := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ (5/4)*(N/512))
  nlinarith only [hquot,hscale]

/-- Raw vertex membership supplies literal original incidences and their
original grain error. No representative projection replaces a vertex. -/
lemma mixed_vertices_near {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (E : Finset (Fin n × Index))
    (c : Parent × (Index × Index)) (k l : Index)
    (hk : k∈mixedVertices D a m (phaseDepth m) plane ell E c)
    (hl : l∈mixedVertices D a m (phaseDepth m) plane ell E c) :
    Metric.infDist (cellCenter (64/((2^(phaseDepth m):ℕ):ℝ)) k-
      cellCenter (64/((2^(phaseDepth m):ℕ):ℝ)) l) (plane c.2.1:Set E4) ≤ 2*grainWidth m ell := by
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hk
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hl
  have hg := mixed_fiber_geometry D a m plane ell E c x y hx hy
  have hxc := hx
  simp only [mixedFiber,classFiber,mem_filter] at hxc
  have hnode : spatialLabel D (2^m) x.2=c.2.1 :=
    congrArg (fun z : Parent × (Index × Index) => z.2.1) hxc.2
  simpa only [rawVertex,hnode] using hg.2.2.2.2

end NativeGrainQuotientGeometry
