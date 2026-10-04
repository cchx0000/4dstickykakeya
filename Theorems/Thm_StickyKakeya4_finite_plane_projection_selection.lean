import Theorems.Thm_StickyKakeya4_finite_plane_projection_energy
import Theorems.Thm_StickyKakeya4_two_tube_path_collision_count

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Finset
open scoped BigOperators
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

/-- The literal projected cell of an original spatial label. -/
def projectedCell (uv : ℝ × ℝ) (rho : ℝ) (p : Point3) : ℤ × ℤ :=
  (⌊(project uv p).1 / rho⌋, ⌊(project uv p).2 / rho⌋)

lemma same_floor_close {x y rho : ℝ} (hrho : 0 < rho)
    (h : ⌊x / rho⌋ = ⌊y / rho⌋) : |x - y| ≤ rho := by
  have hx := NativeTangentGridCoarsening.coarse_floor_interval hrho (k := ⌊x / rho⌋) rfl
  have hy := NativeTangentGridCoarsening.coarse_floor_interval hrho (k := ⌊x / rho⌋) h.symm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Same projected cells give actual close projected points. -/
lemma same_projected_cell_close (uv : ℝ × ℝ) {rho : ℝ} (hrho : 0 < rho)
    {p q : Point3} (h : projectedCell uv rho p = projectedCell uv rho q) :
    |(project uv p).1 - (project uv q).1| ≤ rho ∧
    |(project uv p).2 - (project uv q).2| ≤ rho := by
  exact ⟨same_floor_close hrho (congrArg Prod.fst h),
    same_floor_close hrho (congrArg Prod.snd h)⟩

/-- Cauchy-Schwarz on the actual occupied projected cells. -/
theorem projected_cell_energy {X : Type*} (P : Finset X) (p : X → Point3)
    (uv : ℝ × ℝ) {rho : ℝ} (hrho : 0 < rho) :
    (P.card : ℝ) ^ 2 ≤ ((P.image (fun i => projectedCell uv rho (p i))).card : ℝ) *
      (labelCollisions P p uv rho).card := by
  let f := fun i => projectedCell uv rho (p i)
  have hCS : (P.card : ℝ) ^ 2 ≤ ((P.image f).card : ℝ) *
      (TwoTubePathCollisionCount.collisions P f).card := by
    exact_mod_cast TwoTubePathCollisionCount.square_card_le_image_mul_collisions P f
  have hsub : TwoTubePathCollisionCount.collisions P f ⊆ labelCollisions P p uv rho := by
    intro ik hik
    obtain ⟨hi, hk, he⟩ := TwoTubePathCollisionCount.mem_collisions P f ik |>.mp hik
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hk⟩,
      same_projected_cell_close uv hrho he⟩
  exact hCS.trans (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (Finset.card_le_card hsub)) (by positivity))

lemma parameters_nonempty (n : ℕ) : (parameters n).Nonempty := by
  have hs : (slopes n).Nonempty := Finset.card_pos.mp (by rw [slopes_card]; omega)
  exact hs.product hs

lemma exists_le_average {T : Type*} (S : Finset T) (f : T → ℝ) (C : ℝ)
    (hS : S.Nonempty) (hbudget : (∑ t ∈ S, f t) ≤ C * S.card) :
    ∃ t ∈ S, f t ≤ C := by
  by_contra hnot
  have hlarge : ∀ t ∈ S, C < f t := by
    intro t ht
    exact lt_of_not_ge (fun hf => hnot ⟨t, ht, hf⟩)
  have hsum := Finset.sum_lt_sum_of_nonempty hS hlarge
  have hconst : (∑ _t ∈ S, C) = C * S.card := by simp [mul_comm]
  rw [hconst] at hsum
  linarith

/-- A concrete member of the explicit projection family preserves the
occupied-cell population of the original set, with all KT1 losses explicit. -/
theorem exists_large_projected_image {X : Type*} (P : Finset X) (p : X → Point3)
    (n J : ℕ) {rho K : ℝ} (hP : P.Nonempty) (hmesh : mesh n ≤ rho) (hK : 0 < K)
    (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (htop : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (hKT1 : ∀ i ∈ P, ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ K * R / rho) :
    ∃ uv ∈ parameters n,
      ((labelCollisions P p uv rho).card : ℝ) ≤ 257 * K * P.card ∧
      (P.card : ℝ) / (257 * K) ≤
        ((P.image (fun i => projectedCell uv rho (p i))).card : ℝ) := by
  have hbudget := actual_KT1_collision_energy P p n J hmesh hK.le hJ htop hKT1
  obtain ⟨uv, huv, hcoll⟩ := exists_le_average (parameters n)
    (fun uv => ((labelCollisions P p uv rho).card : ℝ)) (257 * K * P.card)
    (parameters_nonempty n) hbudget
  refine ⟨uv, huv, hcoll, ?_⟩
  have hCS := projected_cell_energy P p uv ((mesh_pos n).trans_le hmesh)
  have hN : 0 < (P.card : ℝ) := by exact_mod_cast hP.card_pos
  have hprod := mul_le_mul_of_nonneg_left hcoll
    (show 0 ≤ ((P.image (fun i => projectedCell uv rho (p i))).card : ℝ) by positivity)
  have hpos : 0 < 257 * K := by positivity
  apply (div_le_iff₀ hpos).2
  nlinarith

end FinitePlaneProjectionGrid
