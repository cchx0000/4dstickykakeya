import Theorems.Thm_StickyKakeya4_finite_plane_projection_allscale

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open Finset
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

/-- The concrete coordinate projection is a genuine real linear map. -/
def projectionLinear (uv : ℝ × ℝ) : Point3 →ₗ[ℝ] (ℝ × ℝ) where
  toFun := project uv
  map_add' x y := by
    ext <;> simp only [project, Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' a x := by
    change (a * x.1 - uv.1 * (a * x.2.2), a * x.2.1 - uv.2 * (a * x.2.2)) =
      (a * (x.1 - uv.1 * x.2.2), a * (x.2.1 - uv.2 * x.2.2))
    ext <;> ring

lemma projectionLinear_surjective (uv : ℝ × ℝ) : Function.Surjective (projectionLinear uv) := by
  intro q
  refine ⟨(q.1, (q.2, 0)), ?_⟩
  change project uv (q.1, (q.2, 0)) = q
  simp [project]

/-- The tested planar sets are literal native sup-norm closed balls. -/
lemma projectedBall_eq_native_ball {X : Type*} (Q : Finset X) (p : X → Point3)
    (uv c : ℝ × ℝ) (R : ℝ) :
    projectedBall Q p uv c R = Q.filter (fun i => ‖projectionLinear uv (p i) - c‖ ≤ R) := by
  ext i
  simp only [projectedBall, Finset.mem_filter, projectionLinear, LinearMap.coe_mk,
    AddHom.coe_mk, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, max_le_iff]

/-- Distinct representative cells imply distinct actual projected points. -/
lemma projection_injective_of_cells {X : Type*} (Q : Finset X) (p : X → Point3)
    (uv : ℝ × ℝ) (rho : ℝ)
    (hcell : Set.InjOn (fun i => projectedCell uv rho (p i)) (↑Q)) :
    Set.InjOn (fun i => projectionLinear uv (p i)) (↑Q) := by
  intro i hi j hj he
  apply hcell hi hj
  have hproj : project uv (p i) = project uv (p j) := he
  simp only [projectedCell, hproj]

/-- Cardinality is therefore preserved by actual projection on retained labels. -/
lemma projected_original_card {X : Type*} (Q : Finset X) (p : X → Point3)
    (uv : ℝ × ℝ) (rho : ℝ)
    (hcell : Set.InjOn (fun i => projectedCell uv rho (p i)) (↑Q)) :
    (Q.image (fun i => projectionLinear uv (p i))).card = Q.card :=
  Finset.card_image_iff.mpr (projection_injective_of_cells Q p uv rho hcell)

end FinitePlaneProjectionGrid
