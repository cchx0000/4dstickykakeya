import Theorems.Thm_StickyKakeya4_finite_plane_projection_triangles
import Theorems.Thm_StickyKakeya4_finite_plane_projection_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Finset
open scoped BigOperators
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

/-- Original secant cross-product size in the native sup norm. -/
def crossSize (p q s : Point3) : ℝ :=
  distance3
    ((q.2.1 - p.2.1) * (s.2.2 - p.2.2) - (q.2.2 - p.2.2) * (s.2.1 - p.2.1))
    ((q.2.2 - p.2.2) * (s.1 - p.1) - (q.1 - p.1) * (s.2.2 - p.2.2))
    ((q.1 - p.1) * (s.2.1 - p.2.1) - (q.2.1 - p.2.1) * (s.1 - p.1))

/-- Twice signed area of the actual projected original triangle. -/
def projectedArea (uv : ℝ × ℝ) (p q s : Point3) : ℝ :=
  ((project uv q).1 - (project uv p).1) * ((project uv s).2 - (project uv p).2) -
  ((project uv q).2 - (project uv p).2) * ((project uv s).1 - (project uv p).1)

def triples {X : Type*} (B : Finset X) : Finset (X × (X × X)) := B ×ˢ (B ×ˢ B)

def degenerateTriples {X : Type*} (B : Finset X) (b : X → Point3) (A : ℝ) :
    Finset (X × (X × X)) :=
  (triples B).filter (fun ijk => crossSize (b ijk.1) (b ijk.2.1) (b ijk.2.2) < A)

def smallProjectedTriples {X : Type*} (B : Finset X) (b : X → Point3)
    (uv : ℝ × ℝ) (r : ℝ) : Finset (X × (X × X)) :=
  (triples B).filter (fun ijk => |projectedArea uv (b ijk.1) (b ijk.2.1) (b ijk.2.2)| ≤ r)

lemma triples_card {X : Type*} (B : Finset X) :
    ((triples B).card : ℝ) = (B.card : ℝ) ^ 3 := by
  simp only [triples, Finset.card_product, Nat.cast_mul]
  ring

lemma actual_triangle_parameter_count (n : ℕ) (p q s : Point3) {r A : ℝ}
    (hr : 0 ≤ r) (hA : 0 < A) (hcross : A ≤ crossSize p q s) :
    (((parameters n).filter (fun uv => |projectedArea uv p q s| ≤ r)).card : ℝ) ≤
      (8 * r / A + 2 * mesh n) * (parameters n).card := by
  have he (uv : ℝ × ℝ) : projectedArea uv p q s =
      ((q.1 - p.1) - uv.1 * (q.2.2 - p.2.2)) *
        ((s.2.1 - p.2.1) - uv.2 * (s.2.2 - p.2.2)) -
      ((q.2.1 - p.2.1) - uv.2 * (q.2.2 - p.2.2)) *
        ((s.1 - p.1) - uv.1 * (s.2.2 - p.2.2)) := by
    dsimp [projectedArea, project]
    ring
  simp_rw [he]
  exact projected_triangle_count n hr hA hcross

lemma triangle_fubini {X : Type*} (B : Finset X) (b : X → Point3)
    (n : ℕ) (r : ℝ) :
    (∑ uv ∈ parameters n, ((smallProjectedTriples B b uv r).card : ℝ)) =
      ∑ ijk ∈ triples B, (((parameters n).filter (fun uv =>
        |projectedArea uv (b ijk.1) (b ijk.2.1) (b ijk.2.2)| ≤ r)).card : ℝ) := by
  simp only [smallProjectedTriples, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact Finset.sum_comm

/-- Average projected small-area triples are bounded by original degenerate
triples plus the explicitly counted finite-grid strip error. -/
theorem original_triangle_projection_budget {X : Type*} (B : Finset X) (b : X → Point3)
    (n : ℕ) {r A : ℝ} (hr : 0 ≤ r) (hA : 0 < A) :
    (∑ uv ∈ parameters n, ((smallProjectedTriples B b uv r).card : ℝ)) ≤
      (((degenerateTriples B b A).card : ℝ) +
        (8 * r / A + 2 * mesh n) * (B.card : ℝ) ^ 3) * (parameters n).card := by
  have hm := mesh_pos n
  let c := 8 * r / A + 2 * mesh n
  have hc : 0 ≤ c := by dsimp [c]; positivity
  rw [triangle_fubini]
  calc
    _ ≤ ∑ ijk ∈ triples B,
        ((if crossSize (b ijk.1) (b ijk.2.1) (b ijk.2.2) < A
          then (parameters n).card else 0 : ℝ) + c * (parameters n).card) := by
      apply Finset.sum_le_sum
      intro ijk _hijk
      by_cases hbad : crossSize (b ijk.1) (b ijk.2.1) (b ijk.2.2) < A
      · rw [if_pos hbad]
        have hh : (((parameters n).filter (fun uv =>
            |projectedArea uv (b ijk.1) (b ijk.2.1) (b ijk.2.2)| ≤ r)).card : ℝ) ≤
              (parameters n).card :=
          Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
        have h0 : 0 ≤ c * (parameters n).card := by positivity
        linarith
      · rw [if_neg hbad, zero_add]
        exact actual_triangle_parameter_count n _ _ _ hr hA (le_of_not_gt hbad)
    _ = (((degenerateTriples B b A).card : ℝ) +
        c * (B.card : ℝ) ^ 3) * (parameters n).card := by
      rw [Finset.sum_add_distrib]
      have hsum : (∑ ijk ∈ triples B,
          (if crossSize (b ijk.1) (b ijk.2.1) (b ijk.2.2) < A
            then ((parameters n).card : ℝ) else 0)) =
          ((degenerateTriples B b A).card : ℝ) * (parameters n).card := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, degenerateTriples]
      rw [hsum]
      simp only [Finset.sum_const, nsmul_eq_mul, triples_card]
      ring

/-- Two finite average budgets select the same original parameter. -/
lemma exists_joint_average {T : Type*} (S : Finset T) (f g : T → ℝ) {F G : ℝ}
    (hS : S.Nonempty) (hF : 0 < F) (hG : 0 < G)
    (hf0 : ∀ t ∈ S, 0 ≤ f t) (hg0 : ∀ t ∈ S, 0 ≤ g t)
    (hf : (∑ t ∈ S, f t) ≤ F * S.card)
    (hg : (∑ t ∈ S, g t) ≤ G * S.card) :
    ∃ t ∈ S, f t ≤ 2 * F ∧ g t ≤ 2 * G := by
  have hbudget : (∑ t ∈ S, (f t / F + g t / G)) ≤ 2 * S.card := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
    have hff := (div_le_div_of_nonneg_right hf hF.le)
    have hgg := (div_le_div_of_nonneg_right hg hG.le)
    have heF : F * (S.card : ℝ) / F = S.card := by field_simp
    have heG : G * (S.card : ℝ) / G = S.card := by field_simp
    rw [heF] at hff
    rw [heG] at hgg
    linarith
  obtain ⟨t, ht, hsum⟩ := exists_le_average S (fun t => f t / F + g t / G) 2 hS hbudget
  refine ⟨t, ht, ?_, ?_⟩
  · have hgn : 0 ≤ g t / G := div_nonneg (hg0 t ht) hG.le
    exact (div_le_iff₀ hF).mp (by linarith)
  · have hfn : 0 ≤ f t / F := div_nonneg (hf0 t ht) hF.le
    exact (div_le_iff₀ hG).mp (by linarith)

/-- A single explicit projection simultaneously preserves A's occupied
cells and bounds B's small projected triangles. Original B degeneracy is
an input about original geometry; no projected property is assumed. -/
theorem exists_common_projection {X Y : Type*} (P : Finset X) (p : X → Point3)
    (B : Finset Y) (b : Y → Point3) (n J : ℕ) {rho K r A : ℝ}
    (hP : P.Nonempty) (hB : B.Nonempty) (hmesh : mesh n ≤ rho) (hK : 0 < K)
    (hr : 0 ≤ r) (hA : 0 < A) (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (htop : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (hKT1 : ∀ i ∈ P, ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ K * R / rho) :
    ∃ uv ∈ parameters n,
      (P.card : ℝ) / (514 * K) ≤
        ((P.image (fun i => projectedCell uv rho (p i))).card : ℝ) ∧
      ((smallProjectedTriples B b uv r).card : ℝ) ≤
        2 * (((degenerateTriples B b A).card : ℝ) +
          (8 * r / A + 2 * mesh n) * (B.card : ℝ) ^ 3) := by
  let F := 257 * K * (P.card : ℝ)
  let G := ((degenerateTriples B b A).card : ℝ) +
    (8 * r / A + 2 * mesh n) * (B.card : ℝ) ^ 3
  have hNp : 0 < (P.card : ℝ) := by exact_mod_cast hP.card_pos
  have hNb : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hm := mesh_pos n
  have hF : 0 < F := by dsimp [F]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  obtain ⟨uv, huv, hcoll, htri⟩ := exists_joint_average (parameters n)
    (fun uv => ((labelCollisions P p uv rho).card : ℝ))
    (fun uv => ((smallProjectedTriples B b uv r).card : ℝ)) (parameters_nonempty n) hF hG
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
    (actual_KT1_collision_energy P p n J hmesh hK.le hJ htop hKT1)
    (original_triangle_projection_budget B b n hr hA)
  refine ⟨uv, huv, ?_, htri⟩
  have hCS := projected_cell_energy P p uv (hm.trans_le hmesh)
  have hprod := mul_le_mul_of_nonneg_left hcoll
    (show 0 ≤ ((P.image (fun i => projectedCell uv rho (p i))).card : ℝ) by positivity)
  have hpos : 0 < 514 * K := by positivity
  apply (div_le_iff₀ hpos).2
  dsimp [F] at hprod
  nlinarith

end FinitePlaneProjectionGrid
