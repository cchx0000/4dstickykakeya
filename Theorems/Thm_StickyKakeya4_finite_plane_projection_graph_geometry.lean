import Theorems.Thm_StickyKakeya4_finite_plane_projection_final

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

noncomputable section

namespace FinitePlaneProjectionGrid

/-- The genuine coordinate projection has operator bound two in the native
nested-product sup norms. -/
lemma projectionLinear_norm_le_of_abs {uv : ℝ × ℝ}
    (hu : |uv.1| ≤ 1) (hv : |uv.2| ≤ 1) (x : Point3) :
    ‖projectionLinear uv x‖ ≤ 2 * ‖x‖ := by
  have hx : |x.1| ≤ ‖x‖ := by
    change |x.1| ≤ max |x.1| (max |x.2.1| |x.2.2|)
    exact le_max_left _ _
  have hy : |x.2.1| ≤ ‖x‖ := by
    change |x.2.1| ≤ max |x.1| (max |x.2.1| |x.2.2|)
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hz : |x.2.2| ≤ ‖x‖ := by
    change |x.2.2| ≤ max |x.1| (max |x.2.1| |x.2.2|)
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hcoord (s t : ℝ) (hs : |s| ≤ ‖x‖) (ht : |t| ≤ 1) :
      |s - t * x.2.2| ≤ 2 * ‖x‖ := by
    calc
      |s - t * x.2.2| ≤ |s| + |t * x.2.2| := abs_sub _ _
      _ = |s| + |t| * |x.2.2| := by rw [abs_mul]
      _ ≤ ‖x‖ + 1 * |x.2.2| := add_le_add hs
        (mul_le_mul_of_nonneg_right ht (abs_nonneg _))
      _ ≤ 2 * ‖x‖ := by linarith
  change max |x.1 - uv.1 * x.2.2| |x.2.1 - uv.2 * x.2.2| ≤ 2 * ‖x‖
  exact max_le (hcoord _ _ hx hu) (hcoord _ _ hy hv)

/-- Every member of the explicit finite family has the same native norm bound. -/
lemma projectionLinear_norm_le {n : ℕ} {uv : ℝ × ℝ}
    (huv : uv ∈ parameters n) (x : Point3) :
    ‖projectionLinear uv x‖ ≤ 2 * ‖x‖ := by
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
  exact projectionLinear_norm_le_of_abs (slope_abs_le_one hu) (slope_abs_le_one hv) x

lemma projectionLinear_sub_norm_le {n : ℕ} {uv : ℝ × ℝ}
    (huv : uv ∈ parameters n) (x y : Point3) :
    ‖projectionLinear uv x - projectionLinear uv y‖ ≤ 2 * ‖x - y‖ := by
  rw [← map_sub]
  exact projectionLinear_norm_le huv (x - y)

lemma projectionLinear_lipschitz {n : ℕ} {uv : ℝ × ℝ}
    (huv : uv ∈ parameters n) : LipschitzWith 2 (projectionLinear uv) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_ofNat] using projectionLinear_sub_norm_le huv x y

/-- Same literal floor cells control distances between actual projected points. -/
lemma same_projected_cell_norm_le (uv : ℝ × ℝ) {rho : ℝ} (hrho : 0 < rho)
    {p q : Point3} (h : projectedCell uv rho p = projectedCell uv rho q) :
    ‖projectionLinear uv p - projectionLinear uv q‖ ≤ rho := by
  obtain ⟨hx, hy⟩ := same_projected_cell_close uv hrho h
  change max |(project uv p).1 - (project uv q).1|
    |(project uv p).2 - (project uv q).2| ≤ rho
  exact max_le hx hy

/-- Apply the genuine linear map to the original spatial edge, retaining the
original target, anchor, and real scalar exactly. -/
lemma original_edge_projected_error {n : ℕ} {uv : ℝ × ℝ}
    (huv : uv ∈ parameters n) {target a b anchor : Point3} {c E : ℝ}
    (hedge : ‖target - a - c • (b - anchor)‖ ≤ E) :
    ‖projectionLinear uv target - projectionLinear uv a -
      c • (projectionLinear uv b - projectionLinear uv anchor)‖ ≤ 2 * E := by
  calc
    _ = ‖projectionLinear uv (target - a - c • (b - anchor))‖ := by
      rw [map_sub, map_sub, map_smul, map_sub]
    _ ≤ 2 * ‖target - a - c • (b - anchor)‖ := projectionLinear_norm_le huv _
    _ ≤ 2 * E := mul_le_mul_of_nonneg_left hedge (by norm_num)

/-- Transport an original spatial edge to any actual same-cell representatives.
No geometric relation between arbitrary representative triples is assumed. -/
theorem original_edge_same_cell_transport {n : ℕ} {uv : ℝ × ℝ}
    (huv : uv ∈ parameters n) {rho : ℝ} (hrho : 0 < rho)
    {target a b anchor a' b' : Point3} {c E : ℝ}
    (hedge : ‖target - a - c • (b - anchor)‖ ≤ E)
    (ha : projectedCell uv rho a = projectedCell uv rho a')
    (hb : projectedCell uv rho b = projectedCell uv rho b') :
    ‖projectionLinear uv target - projectionLinear uv a' -
      c • (projectionLinear uv b' - projectionLinear uv anchor)‖ ≤
        2 * E + (1 + |c|) * rho := by
  have hbase := original_edge_projected_error huv hedge
  have hA := same_projected_cell_norm_le uv hrho ha
  have hB := same_projected_cell_norm_le uv hrho hb
  have hC : ‖c • (projectionLinear uv b - projectionLinear uv b')‖ ≤ |c| * rho := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hB (abs_nonneg _)
  have he : projectionLinear uv target - projectionLinear uv a' -
      c • (projectionLinear uv b' - projectionLinear uv anchor) =
      (projectionLinear uv target - projectionLinear uv a -
        c • (projectionLinear uv b - projectionLinear uv anchor)) +
      (projectionLinear uv a - projectionLinear uv a') +
      c • (projectionLinear uv b - projectionLinear uv b') := by
    simp only [smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖projectionLinear uv target - projectionLinear uv a -
          c • (projectionLinear uv b - projectionLinear uv anchor)‖ +
        ‖projectionLinear uv a - projectionLinear uv a'‖ +
        ‖c • (projectionLinear uv b - projectionLinear uv b')‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ 2 * E + rho + |c| * rho := add_le_add (add_le_add hbase hA) hC
    _ = _ := by ring

/-- Replacing the target by a same-cell representative costs one further rho;
the original anchor and scalar are still retained. -/
theorem original_edge_same_cell_target_transport {n : ℕ} {uv : ℝ × ℝ}
    (huv : uv ∈ parameters n) {rho : ℝ} (hrho : 0 < rho)
    {target target' a b anchor a' b' : Point3} {c E : ℝ}
    (hedge : ‖target - a - c • (b - anchor)‖ ≤ E)
    (ha : projectedCell uv rho a = projectedCell uv rho a')
    (hb : projectedCell uv rho b = projectedCell uv rho b')
    (htarget : projectedCell uv rho target = projectedCell uv rho target') :
    ‖projectionLinear uv target' - projectionLinear uv a' -
      c • (projectionLinear uv b' - projectionLinear uv anchor)‖ ≤
        2 * E + (2 + |c|) * rho := by
  have hbase := original_edge_same_cell_transport huv hrho hedge ha hb
  have ht := same_projected_cell_norm_le uv hrho htarget.symm
  have he : projectionLinear uv target' - projectionLinear uv a' -
      c • (projectionLinear uv b' - projectionLinear uv anchor) =
      (projectionLinear uv target - projectionLinear uv a' -
        c • (projectionLinear uv b' - projectionLinear uv anchor)) +
      (projectionLinear uv target' - projectionLinear uv target) := by abel
  rw [he]
  calc
    _ ≤ ‖projectionLinear uv target - projectionLinear uv a' -
        c • (projectionLinear uv b' - projectionLinear uv anchor)‖ +
        ‖projectionLinear uv target' - projectionLinear uv target‖ := norm_add_le _ _
    _ ≤ (2 * E + (1 + |c|) * rho) + rho := add_le_add hbase ht
    _ = _ := by ring

end FinitePlaneProjectionGrid
