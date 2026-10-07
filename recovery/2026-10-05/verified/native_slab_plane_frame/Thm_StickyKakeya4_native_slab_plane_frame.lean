import Theorems.Thm_StickyKakeya4_slab_plane_pullback
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_incidence
import Theorems.Thm_StickyKakeya4_native_grain_height_projection_transport
import Theorems.Thm_StickyKakeya4_native_incident_affine_anchor_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeSlabPlaneFrame
open Classical Finset StickyKakeya4 NativeHorizontalGrainSlice NativeGrainQuotientInjection
open NativeReferenceXYGridLinear NativeHorizontalGraphCoordinates NativeOriginalParentSelection
open NativeReferenceXYGridIncidence NativeGrainHeightProjectionTransport NativeIncidentAffineAnchorGeometry
open NativeDirectionRankDichotomy NativeLocalParentGeometry
open scoped Matrix.Norms.Elementwise

abbrev Coordinates (ell : ℕ) :=
  (EuclideanSpace ℝ (Fin (ell-1)) × EuclideanSpace ℝ (Fin (4-ell))) × ℝ

/-- The actual fixed orthonormal frame in the product order required by
SlabPlanePullback. This is linear and does not contain the changing field. -/
def coordinateMap (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) :
    E4 →ₗ[ℝ] Coordinates ell :=
  ((tangentCoordinates P ell hd).prod (NativeReferenceXYGridLinear.normalCoordinates P hP ell hell hell4 hd)).prod
    (EuclideanSpace.projₗ (3:Fin 4))

lemma coordinateMap_injective (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) :
    Function.Injective (coordinateMap P hP ell hell hell4 hd) := by
  intro x y hxy
  apply frame_injective P hP ell hell hell4 hd
  apply Prod.ext
  · exact congrArg (fun z : Coordinates ell => z.1.1) hxy
  · apply Prod.ext
    · exact congrArg (fun z : Coordinates ell => z.1.2) hxy
    · exact congrArg (fun z : Coordinates ell => z.2) hxy

lemma coordinate_finrank (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) :
    Module.finrank ℝ E4=Module.finrank ℝ (Coordinates ell) := by
  simp only [Coordinates,Module.finrank_prod,finrank_euclideanSpace_fin,Module.finrank_self]
  omega

/-- Its inverse is constructed from the proved bijective coordinate map;
no inverse-frame certificate is supplied by a caller. -/
def frameEquiv (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) :
    E4 ≃ₗ[ℝ] Coordinates ell :=
  LinearMap.linearEquivOfInjective (coordinateMap P hP ell hell hell4 hd)
    (coordinateMap_injective P hP ell hell hell4 hd) (coordinate_finrank ell hell hell4)

lemma frameEquiv_apply (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (v : E4) :
    frameEquiv P hP ell hell hell4 hd v=
      ((tangentCoordinates P ell hd v,NativeReferenceXYGridLinear.normalCoordinates P hP ell hell hell4 hd v),v (3:Fin 4)) := rfl

lemma inverse_coordinates (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (z : Coordinates ell) :
    tangentCoordinates P ell hd ((frameEquiv P hP ell hell hell4 hd).symm z)=z.1.1 ∧
    NativeReferenceXYGridLinear.normalCoordinates P hP ell hell hell4 hd ((frameEquiv P hP ell hell hell4 hd).symm z)=z.1.2 ∧
    ((frameEquiv P hP ell hell hell4 hd).symm z) (3:Fin 4)=z.2 := by
  have hh := (frameEquiv P hP ell hell hell4 hd).apply_symm_apply z
  exact ⟨congrArg (fun z : Coordinates ell => z.1.1) hh,
    congrArg (fun z : Coordinates ell => z.1.2) hh,congrArg Prod.snd hh⟩

def matrixContinuous {ell : ℕ} (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) :
    EuclideanSpace ℝ (Fin (ell-1)) →L[ℝ] EuclideanSpace ℝ (Fin (4-ell)) :=
  M.toEuclideanLin.toContinuousLinearMap

lemma matrixContinuous_apply {ell : ℕ} (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (x : EuclideanSpace ℝ (Fin (ell-1))) : matrixContinuous M x=M.toEuclideanLin x := rfl

lemma matrixContinuous_norm (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ)) :
    ‖matrixContinuous M‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [matrixContinuous_apply,one_mul] using matrix_action_norm ell hell hell4 M hM x

end NativeSlabPlaneFrame
