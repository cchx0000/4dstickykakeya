import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_linear
import Theorems.Thm_StickyKakeya4_canonical_configured_E4_bridge

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
noncomputable section
namespace NativePackedFrameIsometry
open Classical Finset StickyKakeya4 NativeHorizontalGrainSlice
open NativeHorizontalGraphCoordinates NativeGrainQuotientInjection NativeReferenceXYGridLinear
open CanonicalConfiguredE4Bridge
open scoped BigOperators

/-- The Euclidean pack, unlike the ordinary product norm on frameEquiv,
preserves the sum of the three orthogonal squared norms. -/
lemma assemble_norm_sq (s : Split)
    (x : EuclideanSpace ℝ (Fin (tangentDim s)))
    (y : EuclideanSpace ℝ (Fin (normalDim s))) (t : ℝ) :
    ‖assemble s x y t‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + t ^ 2 := by
  cases s <;>
    simp [PiLp.norm_sq_eq_of_L2, assemble, Fin.sum_univ_succ,
      Real.norm_eq_abs, sq_abs] <;> ring

/-- Exact Pythagoras for the actual horizontal tangent and normal basis. -/
lemma coordinate_energy (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P = ell - 1) (x : E4) :
    ‖tangentCoordinates P ell hd x‖ ^ 2 +
      ‖normalCoordinates P hP ell hell hell4 hd x‖ ^ 2 + x (3 : Fin 4) ^ 2 = ‖x‖ ^ 2 := by
  let y := removeHeight vertical x
  have hy : y ∈ heightKernel := removeHeight_mem_heightKernel vertical_last x
  have hv : ‖y‖ ^ 2 + x (3 : Fin 4) ^ 2 = ‖x‖ ^ 2 := by
    dsimp [y, removeHeight, vertical]
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, Real.norm_eq_abs,
      PiLp.sub_apply, PiLp.smul_apply, sq_abs]
    ring
  have hp : ‖y‖ ^ 2 = ‖tangentCoordinates P ell hd y‖ ^ 2 +
      ‖normalCoordinates P hP ell hell hell4 hd y‖ ^ 2 := by
    rw [tangentCoordinates_norm, normalCoordinates_norm,
      normalProjection_horizontal P hP hy]
    exact Submodule.norm_sq_eq_add_norm_sq_starProjection y P
  obtain ⟨ht, hn⟩ := coordinates_remove_vertical P hP ell hell hell4 hd x
  change tangentCoordinates P ell hd y = _ at ht
  change normalCoordinates P hP ell hell hell4 hd y = _ at hn
  rw [ht, hn] at hp
  linarith only [hp, hv]

/-- The actual fixed frame is packed into E4, with its height coordinate
unchanged. The matrices defining the grain slopes are not part of this map. -/
def packedMap (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s) : E4 →ₗ[ℝ] E4 := by
  cases s with
  | oneTwo =>
      refine
        { toFun := fun x => assemble .oneTwo (tangentCoordinates P 2 hd x) (normalCoordinates P hP 2 (by decide) (by decide) hd x) (x 3)
          map_add' := ?_
          map_smul' := ?_ }
      · intro x y
        ext j
        fin_cases j <;> simp [assemble, map_add]
      · intro a x
        ext j
        fin_cases j <;> simp [assemble, map_smul]
  | twoOne =>
      refine
        { toFun := fun x => assemble .twoOne (tangentCoordinates P 3 hd x) (normalCoordinates P hP 3 (by decide) (by decide) hd x) (x 3)
          map_add' := ?_
          map_smul' := ?_ }
      · intro x y
        ext j
        fin_cases j <;> simp [assemble, map_add]
      · intro a x
        ext j
        fin_cases j <;> simp [assemble, map_smul]

lemma packedMap_norm (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s) (x : E4) :
    ‖packedMap s P hP hd x‖ = ‖x‖ := by
  have hh : ‖packedMap s P hP hd x‖ ^ 2 = ‖x‖ ^ 2 := by
    cases s with
    | oneTwo =>
        change ‖assemble .oneTwo _ _ _‖ ^ 2 = _
        rw [assemble_norm_sq]
        exact coordinate_energy P hP 2 (by decide) (by decide) hd x
    | twoOne =>
        change ‖assemble .twoOne _ _ _‖ ^ 2 = _
        rw [assemble_norm_sq]
        exact coordinate_energy P hP 3 (by decide) (by decide) hd x
  nlinarith only [hh, norm_nonneg (packedMap s P hP hd x), norm_nonneg x]

def packedIsometry (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s) : E4 →ₗᵢ[ℝ] E4 :=
  { packedMap s P hP hd with norm_map' := packedMap_norm s P hP hd }

/-- The concrete orthonormal chart required by actual marked-line transport.
Surjectivity is derived in E4 from norm preservation, not supplied as a premise. -/
def frame (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s) : E4 ≃ₗᵢ[ℝ] E4 :=
  LinearIsometryEquiv.ofSurjective (packedIsometry s P hP hd)
    ((LinearMap.injective_iff_surjective
      (f := (packedIsometry s P hP hd).toLinearMap)).mp
        (packedIsometry s P hP hd).injective)

lemma frame_height (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s) (x : E4) :
    frame s P hP hd x (3 : Fin 4) = x 3 := by
  cases s <;> rfl

lemma frame_apply_oneTwo (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = 1) (x : E4) :
    frame .oneTwo P hP hd x = assemble .oneTwo (tangentCoordinates P 2 hd x)
      (normalCoordinates P hP 2 (by decide) (by decide) hd x) (x 3) := rfl

lemma frame_apply_twoOne (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = 2) (x : E4) :
    frame .twoOne P hP hd x = assemble .twoOne (tangentCoordinates P 3 hd x)
      (normalCoordinates P hP 3 (by decide) (by decide) hd x) (x 3) := rfl

end NativePackedFrameIsometry
