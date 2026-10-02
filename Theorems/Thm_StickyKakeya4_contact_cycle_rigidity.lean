import Theorems.Thm_StickyKakeya4_four_cycle_contact_frame
import Theorems.Thm_StickyKakeya4_three_matrix_inverse_bounds
import Theorems.Thm_StickyKakeya4_separated_bush_fiber

/-!
# Rigidity of a genuine nondegenerate contact four-cycle

All four physical vertices, all four old collision times, and the original
collision error remain fixed. Summing the four residuals gives an exact
linear system for three time differences. The actual horizontal determinant,
not a claimed inverse-norm certificate, controls that system through the
checked 3×3 adjugate bounds.

The resulting cycle plane is the graph of its actual slope matrix `B A⁻¹`
and is close to the scalar Lagrangian graph `-t I`. This is more rigid than
an arbitrary coherent three-plane and avoids a cubic-interpolation loss on
this genuinely nondegenerate branch. Existence of enough such nondegenerate
old-root cycles and payment of the complementary branches remain separate.
-/

open scoped BigOperators

noncomputable section

namespace StickyKakeya4.ContactCycleRigidity

/-- Oriented physical edge of a four-cycle. -/
def edge (a : Fin 4 → E3) (i : Fin 4) : E3 := a (fourCycleNext i) - a i

/-- The actual old-time contact error on each oriented edge. -/
def residual (a b : Fin 4 → E3) (t : Fin 4 → ℝ) (i : Fin 4) : E3 :=
  edge b i + t i • edge a i

/-- Columns are the first three consecutive horizontal cycle edges. -/
def edgeMatrix (a : Fin 4 → E3) : Mat3 :=
  fun i j => edge a j.castSucc i

/-- The manuscript's three anchored secants. -/
def anchoredMatrix (a : Fin 4 → E3) : Mat3 :=
  fun i j => (a j.succ - a 0) i

/-- Consecutive and anchored frames have exactly the same determinant. -/
theorem edgeMatrix_det_eq_anchored (a : Fin 4 → E3) :
    (edgeMatrix a).det = (anchoredMatrix a).det := by
  simp [edgeMatrix, anchoredMatrix, edge, fourCycleNext, Matrix.det_fin_three]
  ring

/-- The four oriented horizontal edges close exactly. -/
theorem sum_edges_eq_zero (a : Fin 4 → E3) : ∑ i, edge a i = 0 := by
  simp [edge, fourCycleNext, Fin.sum_univ_succ]
  module

/-- Exact Cramer system. No closest-time substitution or finer auxiliary
collision scale is used. -/
theorem time_difference_system (a b : Fin 4 → E3) (t : Fin 4 → ℝ) :
    (edgeMatrix a).mulVec (fun j : Fin 3 => t j.castSucc - t 3) =
      (∑ i : Fin 4, residual a b t i).ofLp := by
  funext k
  simp [edgeMatrix, residual, edge, fourCycleNext, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  ring

/-- Four errors of size `r` have total norm at most `4r`. -/
theorem residual_sum_norm_le (a b : Fin 4 → E3) (t : Fin 4 → ℝ)
    (r : ℝ) (hres : ∀ i, ‖residual a b t i‖ ≤ r) :
    ‖∑ i : Fin 4, residual a b t i‖ ≤ 4 * r := by
  calc
    ‖∑ i : Fin 4, residual a b t i‖ ≤ ∑ i : Fin 4, ‖residual a b t i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, r := Finset.sum_le_sum (fun i _ => hres i)
    _ = 4 * r := by simp

/-- The same bound applies to every coordinate, as required by the actual
adjugate inverse estimate. -/
theorem residual_sum_coordinate_le (a b : Fin 4 → E3) (t : Fin 4 → ℝ)
    (r : ℝ) (hres : ∀ i, ‖residual a b t i‖ ≤ r) (j : Fin 3) :
    |(∑ i : Fin 4, residual a b t i) j| ≤ 4 * r := by
  have h := (PiLp.norm_apply_le (∑ i : Fin 4, residual a b t i) j).trans
    (residual_sum_norm_le a b t r hres)
  simpa only [Real.norm_eq_abs] using h

/-- Three independent horizontal edges force their old collision times to
cluster around the fourth old time, at the original error scale. -/
theorem old_times_cluster (a b : Fin 4 → E3) (t : Fin 4 → ℝ)
    (M Δ r : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hr : 0 ≤ r)
    (hA : ∀ i j, |edgeMatrix a i j| ≤ M)
    (hdet : Δ ≤ |(edgeMatrix a).det|)
    (hres : ∀ i, ‖residual a b t i‖ ≤ r) (i : Fin 4) :
    |t i - t 3| ≤ 24 * M ^ 2 * r / Δ := by
  have hfirst (j : Fin 3) : |t j.castSucc - t 3| ≤ 24 * M ^ 2 * r / Δ := by
    have h := threeMatrix_solution_entry_abs_le hM hΔ (by positivity : 0 ≤ 4 * r)
      hA hdet (time_difference_system a b t)
      (fun k => residual_sum_coordinate_le a b t r hres k) j
    convert h using 1; ring
  fin_cases i
  · exact hfirst 0
  · exact hfirst 1
  · exact hfirst 2
  · change |t 3 - t 3| ≤ 24 * M ^ 2 * r / Δ
    rw [sub_self, abs_zero]
    positivity

/-- In particular any pair of the original four times is close. -/
theorem old_times_pairwise_cluster (a b : Fin 4 → E3) (t : Fin 4 → ℝ)
    (M Δ r : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hr : 0 ≤ r)
    (hA : ∀ i j, |edgeMatrix a i j| ≤ M)
    (hdet : Δ ≤ |(edgeMatrix a).det|)
    (hres : ∀ i, ‖residual a b t i‖ ≤ r) (i j : Fin 4) :
    |t i - t j| ≤ 48 * M ^ 2 * r / Δ := by
  have hi := old_times_cluster a b t M Δ r hM hΔ hr hA hdet hres i
  have hj := old_times_cluster a b t M Δ r hM hΔ hr hA hdet hres j
  calc
    |t i - t j| ≤ |t i - t 3| + |t 3 - t j| := abs_sub_le _ _ _
    _ ≤ 24 * M ^ 2 * r / Δ + 24 * M ^ 2 * r / Δ := by
      rw [abs_sub_comm (t 3) (t j)]
      exact add_le_add hi hj
    _ = 48 * M ^ 2 * r / Δ := by ring

/-- Direction-chart bounds supply the frame-entry bound concretely. -/
theorem edgeMatrix_bound_of_direction_bound (a : Fin 4 → E3) (U : ℝ)
    (ha : ∀ i, ‖a i‖ ≤ U) (i j : Fin 3) : |edgeMatrix a i j| ≤ 2 * U := by
  have hcoord (k : Fin 4) : |a k i| ≤ U := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (a k) i).trans (ha k)
  change |(a (fourCycleNext j.castSucc) - a j.castSucc) i| ≤ 2 * U
  change |a (fourCycleNext j.castSucc) i - a j.castSucc i| ≤ 2 * U
  exact (abs_sub _ _).trans (by linarith [hcoord (fourCycleNext j.castSucc), hcoord j.castSucc])

/-- Actual graph-slope matrix of the phase-space span of the three cycle edges. -/
def graphSlope (a b : Fin 4 → E3) : Mat3 := edgeMatrix b * (edgeMatrix a)⁻¹

/-- This graph matrix maps every actual horizontal frame combination to the
matching actual vertical frame combination. -/
theorem graphSlope_maps_frame (a b : Fin 4 → E3)
    (hdet : (edgeMatrix a).det ≠ 0) (u : Fin 3 → ℝ) :
    (graphSlope a b).mulVec ((edgeMatrix a).mulVec u) = (edgeMatrix b).mulVec u := by
  unfold graphSlope
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one]

/-- A scalar-plane error is exactly the physical residual frame followed by
the inverse horizontal frame. -/
theorem scalar_graph_error_identity (a b : Fin 4 → E3) (s : ℝ)
    (hdet : (edgeMatrix a).det ≠ 0) :
    graphSlope a b + s • (1 : Mat3) =
      (edgeMatrix b + s • edgeMatrix a) * (edgeMatrix a)⁻¹ := by
  rw [Matrix.add_mul, Matrix.smul_mul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)]
  rfl

/-- Every entry of the residual frame at the reference old time is small. -/
theorem reference_residual_frame_le (a b : Fin 4 → E3) (t : Fin 4 → ℝ)
    (M Δ r : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hr : 0 ≤ r)
    (hA : ∀ i j, |edgeMatrix a i j| ≤ M)
    (hdet : Δ ≤ |(edgeMatrix a).det|)
    (hres : ∀ i, ‖residual a b t i‖ ≤ r) (i j : Fin 3) :
    |(edgeMatrix b + t 3 • edgeMatrix a) i j| ≤
      r + M * (24 * M ^ 2 * r / Δ) := by
  have hcoord : |residual a b t j.castSucc i| ≤ r := by
    simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (residual a b t j.castSucc) i).trans (hres j.castSucc)
  have ht := old_times_cluster a b t M Δ r hM hΔ hr hA hdet hres j.castSucc
  have hid : (edgeMatrix b + t 3 • edgeMatrix a) i j =
      residual a b t j.castSucc i + (t 3 - t j.castSucc) * edgeMatrix a i j := by
    simp [edgeMatrix, residual]
    ring
  rw [hid]
  calc
    |residual a b t j.castSucc i + (t 3 - t j.castSucc) * edgeMatrix a i j| ≤
        |residual a b t j.castSucc i| + |(t 3 - t j.castSucc) * edgeMatrix a i j| := abs_add_le _ _
    _ ≤ r + M * (24 * M ^ 2 * r / Δ) := by
      rw [abs_mul, abs_sub_comm (t 3) (t j.castSucc)]
      have hp := mul_le_mul ht (hA i j) (abs_nonneg _) (by positivity : 0 ≤ 24 * M ^ 2 * r / Δ)
      nlinarith

/-- Explicit scalar-plane rigidity for the genuine cycle plane. The right
side is `6 M² r/Δ + 144 M⁵ r/Δ²`, with no new collision error substituted. -/
theorem graphSlope_scalar_error_le (a b : Fin 4 → E3) (t : Fin 4 → ℝ)
    (M Δ r : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hr : 0 ≤ r)
    (hA : ∀ i j, |edgeMatrix a i j| ≤ M)
    (hdet : Δ ≤ |(edgeMatrix a).det|)
    (hres : ∀ i, ‖residual a b t i‖ ≤ r) (i j : Fin 3) :
    |(graphSlope a b + t 3 • (1 : Mat3)) i j| ≤
      6 * M ^ 2 * (r + M * (24 * M ^ 2 * r / Δ)) / Δ := by
  rw [scalar_graph_error_identity a b (t 3) (threeMatrix_det_ne_zero hΔ hdet)]
  exact threeMatrix_mul_inv_entry_abs_le hM hΔ (by positivity) hA hdet
    (reference_residual_frame_le a b t M Δ r hM hΔ hr hA hdet hres) i j

/-- A single diagonal coordinate of two scalar graph approximations controls
their times. This avoids generic cubic interpolation on this branch. -/
theorem scalar_graph_time_coherence (F G : Mat3) (s t εF εG θ : ℝ)
    (hF : |F 0 0 + s| ≤ εF) (hG : |G 0 0 + t| ≤ εG)
    (hcoherent : |F 0 0 - G 0 0| ≤ θ) :
    |s - t| ≤ εF + θ + εG := by
  obtain ⟨hFlo, hFhi⟩ := abs_le.mp hF
  obtain ⟨hGlo, hGhi⟩ := abs_le.mp hG
  obtain ⟨hClo, hChi⟩ := abs_le.mp hcoherent
  apply abs_le.mpr
  constructor <;> linarith

/-- The explicit scalar-plane error has only a quadratic determinant debt.
This is the scale relevant to coherent genuine cycle labels. -/
theorem graphSlope_scalar_error_quadratic
    (a b : Fin 4 → E3) (t : Fin 4 → ℝ)
    (M Δ r : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hΔone : Δ ≤ 1) (hr : 0 ≤ r)
    (hA : ∀ i j, |edgeMatrix a i j| ≤ M)
    (hdet : Δ ≤ |(edgeMatrix a).det|)
    (hres : ∀ i, ‖residual a b t i‖ ≤ r) (i j : Fin 3) :
    |(graphSlope a b + t 3 • (1 : Mat3)) i j| ≤
      (6 * M ^ 2 + 144 * M ^ 5) * r / Δ ^ 2 := by
  have hquot : r / Δ ≤ r / Δ ^ 2 :=
    div_le_div_of_nonneg_left hr (sq_pos_of_pos hΔ) (by nlinarith)
  calc
    |(graphSlope a b + t 3 • (1 : Mat3)) i j| ≤
        6 * M ^ 2 * (r + M * (24 * M ^ 2 * r / Δ)) / Δ :=
      graphSlope_scalar_error_le a b t M Δ r hM hΔ hr hA hdet hres i j
    _ = 6 * M ^ 2 * (r / Δ) + 144 * M ^ 5 * (r / Δ ^ 2) := by
      field_simp [ne_of_gt hΔ]
      ring
    _ ≤ 6 * M ^ 2 * (r / Δ ^ 2) + 144 * M ^ 5 * (r / Δ ^ 2) :=
      add_le_add_left (mul_le_mul_of_nonneg_left hquot (by positivity : 0 ≤ 6 * M ^ 2)) _
    _ = (6 * M ^ 2 + 144 * M ^ 5) * r / Δ ^ 2 := by ring

/-- An actual scalar-slope label cell forces every OLD time in every cycle
with that label into the same one-packet window. The common time center is
`-c`; no new time is attached to the old edge. -/
theorem old_times_in_scalar_label_packet
    (a b : Fin 4 → E3) (t : Fin 4 → ℝ)
    (M Δ r c θ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hΔone : Δ ≤ 1) (hr : 0 ≤ r)
    (hA : ∀ i j, |edgeMatrix a i j| ≤ M)
    (hdet : Δ ≤ |(edgeMatrix a).det|)
    (hres : ∀ i, ‖residual a b t i‖ ≤ r)
    (hcell : |graphSlope a b 0 0 - c| ≤ θ) (i : Fin 4) :
    |t i + c| ≤ θ + (30 * M ^ 2 + 144 * M ^ 5) * r / Δ ^ 2 := by
  have hdiag : |graphSlope a b 0 0 + t 3| ≤
      (6 * M ^ 2 + 144 * M ^ 5) * r / Δ ^ 2 := by
    simpa using graphSlope_scalar_error_quadratic a b t M Δ r hM hΔ hΔone hr hA hdet hres 0 0
  have hcenter : |t 3 + c| ≤
      (6 * M ^ 2 + 144 * M ^ 5) * r / Δ ^ 2 + θ := by
    obtain ⟨hl1, hu1⟩ := abs_le.mp hdiag
    obtain ⟨hl2, hu2⟩ := abs_le.mp hcell
    apply abs_le.mpr
    constructor <;> linarith
  have htime := old_times_cluster a b t M Δ r hM hΔ hr hA hdet hres i
  have hquot : r / Δ ≤ r / Δ ^ 2 :=
    div_le_div_of_nonneg_left hr (sq_pos_of_pos hΔ) (by nlinarith)
  calc
    |t i + c| = |(t i - t 3) + (t 3 + c)| := by congr 1; ring
    _ ≤ |t i - t 3| + |t 3 + c| := abs_add_le _ _
    _ ≤ 24 * M ^ 2 * r / Δ +
        ((6 * M ^ 2 + 144 * M ^ 5) * r / Δ ^ 2 + θ) := add_le_add htime hcenter
    _ ≤ 24 * M ^ 2 * (r / Δ ^ 2) +
        ((6 * M ^ 2 + 144 * M ^ 5) * r / Δ ^ 2 + θ) := by
      apply add_le_add_left
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left hquot (by positivity : 0 ≤ 24 * M ^ 2)
    _ = θ + (30 * M ^ 2 + 144 * M ^ 5) * r / Δ ^ 2 := by ring

/-- The inherited old edges remain actual collisions at the common packet
center, with the full root error retained in the explicit radius. -/
theorem old_edges_collide_at_scalar_label
    (a b : Fin 4 → E3) (t : Fin 4 → ℝ)
    (M Δ r c θ L : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hΔone : Δ ≤ 1) (hr : 0 ≤ r)
    (hA : ∀ i j, |edgeMatrix a i j| ≤ M)
    (hdet : Δ ≤ |(edgeMatrix a).det|)
    (hres : ∀ i, ‖residual a b t i‖ ≤ r)
    (hcell : |graphSlope a b 0 0 - c| ≤ θ)
    (hangle : ∀ i, ‖edge a i‖ ≤ L) (i : Fin 4) :
    ‖edge b i + (-c) • edge a i‖ ≤
      r + (θ + (30 * M ^ 2 + 144 * M ^ 5) * r / Δ ^ 2) * L := by
  have hpacket : |t i - (-c)| ≤ θ + (30 * M ^ 2 + 144 * M ^ 5) * r / Δ ^ 2 := by
    simpa only [sub_neg_eq_add] using
      old_times_in_scalar_label_packet a b t M Δ r c θ hM hΔ hΔone hr hA hdet hres hcell i
  exact SeparatedBushFiber.collision_at_packet_center
    (a (fourCycleNext i)) (b (fourCycleNext i)) (a i) (b i)
    (t i) (-c) r (θ + (30 * M ^ 2 + 144 * M ^ 5) * r / Δ ^ 2) L
    (hres i) hpacket (hangle i)

end StickyKakeya4.ContactCycleRigidity
