import Theorems.Thm_StickyKakeya4_finite_plane_projection_grid

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Finset
open scoped BigOperators
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

abbrev Point3 := ℝ × (ℝ × ℝ)

/-- Native nested-product coordinate projection, preserving original labels. -/
def project (uv : ℝ × ℝ) (p : Point3) : ℝ × ℝ :=
  (p.1 - uv.1 * p.2.2, p.2.1 - uv.2 * p.2.2)

def dist3 (p q : Point3) : ℝ :=
  distance3 (p.1 - q.1) (p.2.1 - q.2.1) (p.2.2 - q.2.2)

lemma dist3_eq_norm (p q : Point3) : dist3 p q = ‖p - q‖ := by
  simp only [dist3, distance3, Prod.norm_def, Real.norm_eq_abs, Prod.fst_sub, Prod.snd_sub]

/-- Literal original-label collision fiber. -/
def pairParameters {X : Type*} (n : ℕ) (p : X → Point3) (i j : X) (rho : ℝ) :
    Finset (ℝ × ℝ) :=
  collisions n ((p i).1 - (p j).1) ((p i).2.1 - (p j).2.1)
    ((p i).2.2 - (p j).2.2) rho

lemma pairParameters_iff {X : Type*} (n : ℕ) (p : X → Point3) (i j : X) (rho : ℝ)
    (uv : ℝ × ℝ) :
    uv ∈ pairParameters n p i j rho ↔ uv ∈ parameters n ∧
      |(project uv (p i)).1 - (project uv (p j)).1| ≤ rho ∧
      |(project uv (p i)).2 - (project uv (p j)).2| ≤ rho := by
  simp only [pairParameters, collisions, Finset.mem_filter, project]
  have he₁ : (p i).1 - (p j).1 - uv.1 * ((p i).2.2 - (p j).2.2) =
      ((p i).1 - uv.1 * (p i).2.2) - ((p j).1 - uv.1 * (p j).2.2) := by ring
  have he₂ : (p i).2.1 - (p j).2.1 - uv.2 * ((p i).2.2 - (p j).2.2) =
      ((p i).2.1 - uv.2 * (p i).2.2) - ((p j).2.1 - uv.2 * (p j).2.2) := by ring
  rw [he₁, he₂]

/-- An explicit finite dyadic shell, in the original spatial scale. -/
def shell (j : ℕ) (rho d : ℝ) : Prop :=
  2 ^ j * rho < d ∧ d ≤ 2 ^ (j + 1) * rho

lemma exists_shell {rho d : ℝ} (J : ℕ) (hsmall : rho < d)
    (htop : d ≤ 2 ^ (J + 1) * rho) :
    ∃ j ∈ Finset.range (J + 1), shell j rho d := by
  have hex : ∃ j : ℕ, d ≤ 2 ^ (j + 1) * rho := ⟨J, htop⟩
  let j := Nat.find hex
  have hj : j ≤ J := Nat.find_min' hex htop
  refine ⟨j, Finset.mem_range.mpr (by omega), ?_, Nat.find_spec hex⟩
  by_cases hz : j = 0
  · simpa only [hz, pow_zero, one_mul] using hsmall
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have hnot : ¬ d ≤ 2 ^ (k + 1) * rho := Nat.find_min hex (by dsimp [j] at hk ⊢; omega)
    simpa only [hk, Nat.succ_eq_add_one] using lt_of_not_ge hnot

lemma two_pow_reciprocal (j : ℕ) : (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j = 1 := by
  rw [← mul_pow]
  norm_num

lemma finite_geometric_le_two (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ j ≤ 2 := by
  have he : (∑ j ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ j) =
      2 * (1 - (1 / 2 : ℝ) ^ (J + 1)) := by
    rw [geom_sum_eq]
    · ring
    · norm_num
  rw [he]
  have hh : 0 ≤ (1 / 2 : ℝ) ^ (J + 1) := by positivity
  linarith

lemma shell_pair_count {X : Type*} (n j : ℕ) (p : X → Point3) (i k : X)
    {rho : ℝ} (hmesh : mesh n ≤ rho) (hs : shell j rho (dist3 (p i) (p k)))
    (htop : dist3 (p i) (p k) ≤ 2) :
    ((pairParameters n p i k rho).card : ℝ) ≤
      64 * ((1 / 2 : ℝ) ^ j) ^ 2 * (parameters n).card := by
  have hrho := (mesh_pos n).trans_le hmesh
  have hscale : 0 < (2 : ℝ) ^ j * rho := by positivity
  have hd : 0 < dist3 (p i) (p k) := hscale.trans hs.1
  have hbase := collision_count n hmesh hd htop
  have hcoef : 64 * rho ^ 2 / dist3 (p i) (p k) ^ 2 ≤
      64 * ((1 / 2 : ℝ) ^ j) ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).2
    have hpow : ((2 : ℝ) ^ j * rho) ^ 2 ≤ dist3 (p i) (p k) ^ 2 := by
      nlinarith [hs.1]
    have hh := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ 64 * ((1 / 2 : ℝ) ^ j) ^ 2 by positivity)
    have hid : 64 * ((1 / 2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j * rho) ^ 2 =
        64 * rho ^ 2 := by
      calc
        _ = 64 * ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j) ^ 2 * rho ^ 2 := by ring
        _ = _ := by rw [two_pow_reciprocal]; ring
    rw [hid] at hh
    exact hh
  exact hbase.trans (mul_le_mul_of_nonneg_right hcoef (by positivity))

/-- Derived shell contribution from an actual original-label KT1 ball count. -/
theorem shell_energy_bound {X : Type*} (P : Finset X) (p : X → Point3)
    (n j : ℕ) (i : X) {rho K : ℝ} (hmesh : mesh n ≤ rho)
    (htop : ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (hball : ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ K * R / rho) :
    (∑ k ∈ P.filter (fun k => shell j rho (dist3 (p i) (p k))),
      ((pairParameters n p i k rho).card : ℝ)) ≤
      (128 * K * (1 / 2 : ℝ) ^ j) * (parameters n).card := by
  have hrho := (mesh_pos n).trans_le hmesh
  let S := P.filter (fun k => shell j rho (dist3 (p i) (p k)))
  let C : ℝ := 64 * ((1 / 2 : ℝ) ^ j) ^ 2 * (parameters n).card
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hscale : rho ≤ (2 : ℝ) ^ (j + 1) * rho := by
    have hpow : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hsub : S ⊆ P.filter (fun k => dist3 (p i) (p k) ≤ 2 ^ (j + 1) * rho) := by
    intro k hk
    obtain ⟨hP, hs⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨hP, hs.2⟩
  have hcard : (S.card : ℝ) ≤ K * (2 ^ (j + 1) * rho) / rho :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hball _ hscale)
  calc
    _ ≤ ∑ _k ∈ S, C := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hkP, hks⟩ := Finset.mem_filter.mp hk
      exact shell_pair_count n j p i k hmesh hks (htop k hkP)
    _ = (S.card : ℝ) * C := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K * (2 ^ (j + 1) * rho) / rho) * C := mul_le_mul_of_nonneg_right hcard hC
    _ = (128 * K * (1 / 2 : ℝ) ^ j) * (parameters n).card := by
      have hcancel : K * (2 ^ (j + 1) * rho) / rho = K * 2 ^ (j + 1) := by
        field_simp
      rw [hcancel]
      dsimp [C]
      rw [pow_succ]
      calc
        _ = 128 * K * ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j) *
            (1 / 2 : ℝ) ^ j * (parameters n).card := by ring
        _ = _ := by rw [two_pow_reciprocal]; ring



lemma sum_le_near_add_shells {X : Type*} (P : Finset X) (J : Finset ℕ)
    (f : X → ℝ) (near : X → Prop) (ann : ℕ → X → Prop)
    (hf : ∀ k ∈ P, 0 ≤ f k)
    (hcover : ∀ k ∈ P, near k ∨ ∃ j ∈ J, ann j k) :
    ∑ k ∈ P, f k ≤ (∑ k ∈ P.filter near, f k) +
      ∑ j ∈ J, ∑ k ∈ P.filter (ann j), f k := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hf0 := hf k hk
  have hann0 : ∀ j ∈ J, 0 ≤ if ann j k then f k else 0 := by
    intro j _hj
    split_ifs <;> linarith
  by_cases hn : near k
  · rw [if_pos hn]
    have hs0 := Finset.sum_nonneg hann0
    linarith
  · obtain ⟨j, hj, hkj⟩ := (hcover k hk).resolve_left hn
    rw [if_neg hn, zero_add]
    have hs := Finset.single_le_sum hann0 hj
    simpa only [if_pos hkj] using hs

/-- A point-centered KT1 cap implies the complete finite collision-energy
bound. The annulus count is geometric and contributes no logarithmic loss. -/
theorem point_energy_bound {X : Type*} (P : Finset X) (p : X → Point3)
    (n J : ℕ) (i : X) {rho K : ℝ} (hmesh : mesh n ≤ rho) (hK : 0 ≤ K)
    (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (htop : ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (hball : ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ K * R / rho) :
    (∑ k ∈ P, ((pairParameters n p i k rho).card : ℝ)) ≤
      257 * K * (parameters n).card := by
  have hrho := (mesh_pos n).trans_le hmesh
  let f := fun k => ((pairParameters n p i k rho).card : ℝ)
  have hcover : ∀ k ∈ P, dist3 (p i) (p k) ≤ rho ∨
      ∃ j ∈ Finset.range (J + 1), shell j rho (dist3 (p i) (p k)) := by
    intro k hk
    by_cases hn : dist3 (p i) (p k) ≤ rho
    · exact Or.inl hn
    · exact Or.inr (exists_shell J (lt_of_not_ge hn) ((htop k hk).trans hJ))
  have hsplit := sum_le_near_add_shells P (Finset.range (J + 1)) f
    (fun k => dist3 (p i) (p k) ≤ rho)
    (fun j k => shell j rho (dist3 (p i) (p k))) (fun _ _ => Nat.cast_nonneg _) hcover
  have hnear : (∑ k ∈ P.filter (fun k => dist3 (p i) (p k) ≤ rho), f k) ≤
      K * (parameters n).card := by
    have hcard : ((P.filter (fun k => dist3 (p i) (p k) ≤ rho)).card : ℝ) ≤ K := by
      have hh := hball rho le_rfl
      rwa [mul_div_cancel_right₀ K (ne_of_gt hrho)] at hh
    calc
      _ ≤ ∑ _k ∈ P.filter (fun k => dist3 (p i) (p k) ≤ rho), ((parameters n).card : ℝ) := by
        apply Finset.sum_le_sum
        intro k _hk
        exact Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      _ = ((P.filter (fun k => dist3 (p i) (p k) ≤ rho)).card : ℝ) * (parameters n).card := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hfar : (∑ j ∈ Finset.range (J + 1),
      ∑ k ∈ P.filter (fun k => shell j rho (dist3 (p i) (p k))), f k) ≤
      256 * K * (parameters n).card := by
    calc
      _ ≤ ∑ j ∈ Finset.range (J + 1),
          (128 * K * (1 / 2 : ℝ) ^ j) * (parameters n).card := by
        exact Finset.sum_le_sum (fun j _hj => shell_energy_bound P p n j i hmesh htop hball)
      _ = (128 * K * (parameters n).card) *
          (∑ j ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ ≤ (128 * K * (parameters n).card) * 2 :=
        mul_le_mul_of_nonneg_left (finite_geometric_le_two J) (by positivity)
      _ = _ := by ring
  exact hsplit.trans (by linarith)

/-- Ordered pairs of the SAME original labels colliding under an actual
member of the explicit finite projection family. -/
def labelCollisions {X : Type*} (P : Finset X) (p : X → Point3)
    (uv : ℝ × ℝ) (rho : ℝ) : Finset (X × X) :=
  (P ×ˢ P).filter (fun ik =>
    |(project uv (p ik.1)).1 - (project uv (p ik.2)).1| ≤ rho ∧
    |(project uv (p ik.1)).2 - (project uv (p ik.2)).2| ≤ rho)

lemma collision_fubini {X : Type*} (P : Finset X) (p : X → Point3)
    (n : ℕ) (rho : ℝ) :
    (∑ uv ∈ parameters n, ((labelCollisions P p uv rho).card : ℝ)) =
      ∑ i ∈ P, ∑ k ∈ P, ((pairParameters n p i k rho).card : ℝ) := by
  have he (i k : X) : pairParameters n p i k rho =
      (parameters n).filter (fun uv =>
        |(project uv (p i)).1 - (project uv (p k)).1| ≤ rho ∧
        |(project uv (p i)).2 - (project uv (p k)).2| ≤ rho) := by
    ext uv
    simpa only [Finset.mem_filter] using pairParameters_iff n p i k rho uv
  simp_rw [he]
  simp only [labelCollisions, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_comm]

/-- Full quantitative actual KT1-to-projection collision bound on original
labels, derived from their spatial ball counts. -/
theorem actual_KT1_collision_energy {X : Type*} (P : Finset X) (p : X → Point3)
    (n J : ℕ) {rho K : ℝ} (hmesh : mesh n ≤ rho) (hK : 0 ≤ K)
    (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (htop : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (hKT1 : ∀ i ∈ P, ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ K * R / rho) :
    (∑ uv ∈ parameters n, ((labelCollisions P p uv rho).card : ℝ)) ≤
      257 * K * P.card * (parameters n).card := by
  rw [collision_fubini]
  calc
    _ ≤ ∑ _i ∈ P, 257 * K * (parameters n).card := by
      exact Finset.sum_le_sum (fun i hi => point_energy_bound P p n J i hmesh hK hJ
        (htop i hi) (hKT1 i hi))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end FinitePlaneProjectionGrid
