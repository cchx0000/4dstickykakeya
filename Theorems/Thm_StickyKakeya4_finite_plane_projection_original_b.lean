import Theorems.Thm_StickyKakeya4_finite_plane_projection_line_tubes

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Finset
open scoped BigOperators
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

/-- A literal original-space line tube, expressed without choosing a line
parameterization. For a nonzero secant this is equivalent, up to fixed norm
constants, to a tube about the line through its endpoints. -/
def originalCrossTube {X : Type*} (B : Finset X) (b : X → Point3)
    (i j : X) (w : ℝ) : Finset X :=
  B.filter (fun k => crossSize (b i) (b j) (b k) ≤ w * dist3 (b i) (b j))

lemma triple_filter_card {X : Type*} (B : Finset X) (f : X × (X × X) → Prop) :
    (((triples B).filter f).card : ℝ) =
      ∑ i ∈ B, ∑ j ∈ B, ((B.filter (fun k => f (i, (j, k)))).card : ℝ) := by
  simp only [triples, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Original close-pair and line-tube exclusions give the actual number of
original small-area triangles. This is not an input about projections. -/
theorem original_degenerate_triple_count {X : Type*} (B : Finset X) (b : X → Point3)
    {r0 w0 kappa epsilon : ℝ} (hw0 : 0 ≤ w0) (hepsilon : 0 ≤ epsilon)
    (hclose : ∀ i ∈ B,
      ((B.filter (fun j => dist3 (b i) (b j) ≤ r0)).card : ℝ) ≤ kappa * B.card)
    (hline : ∀ i ∈ B, ∀ j ∈ B, r0 < dist3 (b i) (b j) →
      ((originalCrossTube B b i j w0).card : ℝ) ≤ epsilon * B.card) :
    ((degenerateTriples B b (r0 * w0)).card : ℝ) ≤
      (kappa + epsilon) * (B.card : ℝ) ^ 3 := by
  have hpair : ∀ i ∈ B, ∀ j ∈ B,
      ((B.filter (fun k => crossSize (b i) (b j) (b k) < r0 * w0)).card : ℝ) ≤
        (if dist3 (b i) (b j) ≤ r0 then (B.card : ℝ) else 0) + epsilon * B.card := by
    intro i hi j hj
    by_cases hn : dist3 (b i) (b j) ≤ r0
    · rw [if_pos hn]
      have hh : ((B.filter (fun k => crossSize (b i) (b j) (b k) < r0 * w0)).card : ℝ) ≤
          B.card := Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      have h0 : 0 ≤ epsilon * B.card := by positivity
      linarith
    · rw [if_neg hn, zero_add]
      have hfar := lt_of_not_ge hn
      have hsub : B.filter (fun k => crossSize (b i) (b j) (b k) < r0 * w0) ⊆
          originalCrossTube B b i j w0 := by
        intro k hk
        obtain ⟨hkB, hcross⟩ := Finset.mem_filter.mp hk
        refine Finset.mem_filter.mpr ⟨hkB, ?_⟩
        have hm := mul_le_mul_of_nonneg_right hfar.le hw0
        nlinarith
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hline i hi j hj hfar)
  unfold degenerateTriples
  rw [triple_filter_card]
  calc
    _ ≤ ∑ i ∈ B, ∑ j ∈ B,
        ((if dist3 (b i) (b j) ≤ r0 then (B.card : ℝ) else 0) + epsilon * B.card) := by
      exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpair i hi j hj))
    _ ≤ ∑ _i ∈ B, (kappa + epsilon) * (B.card : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hh := mul_le_mul_of_nonneg_right (hclose i hi) (Nat.cast_nonneg B.card : (0 : ℝ) ≤ B.card)
      nlinarith
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Concrete common-projection conclusion from original A ball counts and
original B close-pair/line-tube exclusions. The line-concentration loss is
explicit, including the finite slope-grid error. -/
theorem exists_common_projection_line_control {X Y : Type*}
    (P : Finset X) (p : X → Point3) (B : Finset Y) (b : Y → Point3)
    (n J : ℕ) {rho K r0 w0 w kappa epsilon : ℝ}
    (hP : P.Nonempty) (hBnon : B.Nonempty) (hmesh : mesh n ≤ rho) (hK : 0 < K)
    (hr0 : 0 < r0) (hw0 : 0 < w0) (hw : 0 ≤ w) (hepsilon : 0 ≤ epsilon)
    (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (htop : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (hKT1 : ∀ i ∈ P, ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ K * R / rho)
    (hB : ∀ i ∈ B, |(b i).1| ≤ 1 ∧ |(b i).2.1| ≤ 1 ∧ |(b i).2.2| ≤ 1)
    (hclose : ∀ i ∈ B,
      ((B.filter (fun j => dist3 (b i) (b j) ≤ r0)).card : ℝ) ≤ kappa * B.card)
    (hline : ∀ i ∈ B, ∀ j ∈ B, r0 < dist3 (b i) (b j) →
      ((originalCrossTube B b i j w0).card : ℝ) ≤ epsilon * B.card) :
    ∃ uv ∈ parameters n,
      (P.card : ℝ) / (514 * K) ≤
        ((P.image (fun i => projectedCell uv rho (p i))).card : ℝ) ∧
      ∀ a d c : ℝ, max |a| |d| = 1 →
        ((projectedLineStrip B b uv a d c w).card : ℝ) ^ 3 ≤
          (2 * (kappa + epsilon + 128 * w / (r0 * w0) + 2 * mesh n)) * (B.card : ℝ) ^ 3 := by
  have hdeg := original_degenerate_triple_count B b hw0.le hepsilon hclose hline
  obtain ⟨uv, huv, himage, htri⟩ := exists_common_projection P p B b n J
    hP hBnon hmesh hK (by positivity : 0 ≤ 16 * w) (mul_pos hr0 hw0) hJ htop hKT1
  refine ⟨uv, huv, himage, ?_⟩
  intro a d c hnormal
  have hcube := projected_line_strip_cube B b (c := c) huv hw hnormal hB
  have hstep := hcube.trans htri
  calc
    _ ≤ 2 * (((degenerateTriples B b (r0 * w0)).card : ℝ) +
        (8 * (16 * w) / (r0 * w0) + 2 * mesh n) * (B.card : ℝ) ^ 3) := hstep
    _ ≤ 2 * ((kappa + epsilon) * (B.card : ℝ) ^ 3 +
        (8 * (16 * w) / (r0 * w0) + 2 * mesh n) * (B.card : ℝ) ^ 3) := by linarith
    _ = _ := by ring

/-- Convenient explicit fractional line-tube loss: the caller chooses theta
and verifies one displayed scalar inequality. All geometric counting above
has already been derived from original labels. -/
theorem line_strip_fraction_of_cube {X : Type*} (B : Finset X) (b : X → Point3)
    (uv : ℝ × ℝ) (a d c w theta beta : ℝ) (htheta : 0 ≤ theta)
    (hbeta : beta ≤ theta ^ 3)
    (hcube : ((projectedLineStrip B b uv a d c w).card : ℝ) ^ 3 ≤
      beta * (B.card : ℝ) ^ 3) :
    ((projectedLineStrip B b uv a d c w).card : ℝ) ≤ theta * B.card := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
  calc
    _ ≤ beta * (B.card : ℝ) ^ 3 := hcube
    _ ≤ theta ^ 3 * (B.card : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hbeta (by positivity)
    _ = _ := by ring

end FinitePlaneProjectionGrid
