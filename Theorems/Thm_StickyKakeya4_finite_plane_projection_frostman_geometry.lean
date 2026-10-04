import Theorems.Thm_StickyKakeya4_finite_plane_projection_frostman

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Finset
open scoped BigOperators
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

/-- Original labels whose actual projected points lie in a planar sup-norm ball. -/
def projectedBall {X : Type*} (Q : Finset X) (p : X → Point3)
    (uv c : ℝ × ℝ) (R : ℝ) : Finset X :=
  Q.filter (fun i => |(project uv (p i)).1 - c.1| ≤ R ∧
    |(project uv (p i)).2 - c.2| ≤ R)

/-- Bounded projected cells imply geometric planar ball counts at a comparable scale. -/
theorem retainedScales_ball_bound {X : Type*} (P Q : Finset X) (p : X → Point3)
    (scales : Finset ℝ) (uv c : ℝ × ℝ) {rho D R h : ℝ}
    (hrho : 0 < rho) (hD : 0 ≤ D) (hh : 0 < h) (hhmem : h ∈ scales) (hRh : R ≤ 2 * h)
    (hQ : Q ⊆ retainedScales P p scales uv rho D) :
    ((projectedBall Q p uv c R).card : ℝ) ≤ 25 * D * h / rho := by
  let S := projectedBall Q p uv c R
  let f := fun i => projectedCell uv h (p i)
  let I := S.image f
  let k0 : ℤ := ⌊c.1 / h⌋
  let l0 : ℤ := ⌊c.2 / h⌋
  let menu := Finset.Icc (k0 - 2) (k0 + 2) ×ˢ Finset.Icc (l0 - 2) (l0 + 2)
  have hIsub : I ⊆ menu := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨_hiQ, hi1, hi2⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_product.mpr ⟨ProjectionHeavyCells.floor_two_interval hh (hi1.trans hRh),
      ProjectionHeavyCells.floor_two_interval hh (hi2.trans hRh)⟩
  have hIcard : I.card ≤ 25 := by
    have hinterval (k : ℤ) : (Finset.Icc (k - 2) (k + 2)).card = 5 := by
      rw [Int.card_Icc]
      have heq : k + 2 + 1 - (k - 2) = (5 : ℤ) := by ring
      rw [heq]
      rfl
    have hmenu : menu.card = 25 := by simp only [menu, Finset.card_product, hinterval]
    exact (Finset.card_le_card hIsub).trans_eq hmenu
  have hfiber : ∀ k ∈ I, ((S.filter (fun i => f i = k)).card : ℝ) ≤ D * h / rho := by
    intro k hk
    obtain ⟨i, hiS, hik⟩ := Finset.mem_image.mp hk
    have hiQ := (Finset.mem_filter.mp hiS).1
    have hsub : S.filter (fun j => f j = k) ⊆
        P.filter (fun j => projectedCell uv h (p j) = projectedCell uv h (p i)) := by
      intro j hj
      obtain ⟨hjS, hjk⟩ := Finset.mem_filter.mp hj
      have hjQ := (Finset.mem_filter.mp hjS).1
      have hjP := retainedScales_subset P p scales uv rho D (hQ hjQ)
      exact Finset.mem_filter.mpr ⟨hjP, hjk.trans hik.symm⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (retainedScales_cell_bound P p scales uv rho D hhmem (hQ hiQ))
  calc
    _ = ∑ k ∈ I, ((S.filter (fun i => f i = k)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image f S
    _ ≤ ∑ _k ∈ I, D * h / rho := Finset.sum_le_sum hfiber
    _ = (I.card : ℝ) * (D * h / rho) := by simp
    _ ≤ 25 * (D * h / rho) := mul_le_mul_of_nonneg_right (by exact_mod_cast hIcard) (by positivity)
    _ = _ := by ring

/-- Finite dyadic scale menu sufficient for every radius between rho and 2. -/
def dyadicScales (J : ℕ) (rho : ℝ) : Finset ℝ :=
  (Finset.range (J + 2)).image (fun j : ℕ => (2 : ℝ) ^ j * rho)

lemma base_mem_dyadicScales (J : ℕ) (rho : ℝ) : rho ∈ dyadicScales J rho := by
  exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp⟩

lemma dyadicScales_ge_base (J : ℕ) {rho r : ℝ} (hrho : 0 ≤ rho)
    (hr : r ∈ dyadicScales J rho) : rho ≤ r := by
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hr
  have hh : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  nlinarith

lemma dyadicScales_card_bound (J : ℕ) (rho : ℝ) : (dyadicScales J rho).card ≤ J + 2 := by
  exact (Finset.card_image_le).trans_eq (Finset.card_range _)

lemma exists_dyadicScale (J : ℕ) {rho R : ℝ} (hrho : 0 < rho)
    (hR : rho ≤ R) (hRtop : R ≤ 2) (hJ : 2 ≤ 2 ^ (J + 1) * rho) :
    ∃ h ∈ dyadicScales J rho, R ≤ h ∧ h ≤ 2 * R := by
  by_cases heq : R = rho
  · exact ⟨rho, base_mem_dyadicScales J rho, by rw [heq], by rw [heq]; linarith⟩
  · obtain ⟨j, hj, hlo, hhi⟩ := exists_shell J (lt_of_le_of_ne hR (Ne.symm heq)) (hRtop.trans hJ)
    refine ⟨2 ^ (j + 1) * rho, Finset.mem_image.mpr ⟨j + 1, ?_, rfl⟩, hhi, ?_⟩
    · exact Finset.mem_range.mpr (by have hh := Finset.mem_range.mp hj; omega)
    · rw [pow_succ]
      nlinarith

/-- Every planar ball above the discretization scale is controlled, for every center. -/
theorem retainedScales_allscale_ball_bound {X : Type*} (P Q : Finset X) (p : X → Point3)
    (J : ℕ) (uv c : ℝ × ℝ) {rho D R : ℝ} (hrho : 0 < rho) (hD : 0 ≤ D)
    (hR : rho ≤ R) (hRtop : R ≤ 2) (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (hQ : Q ⊆ retainedScales P p (dyadicScales J rho) uv rho D) :
    ((projectedBall Q p uv c R).card : ℝ) ≤ 50 * D * R / rho := by
  obtain ⟨h, hh, hRh, hhR⟩ := exists_dyadicScale J hrho hR hRtop hJ
  have hhpos : 0 < h := hrho.trans_le (hR.trans hRh)
  have hbound := retainedScales_ball_bound P Q p (dyadicScales J rho) uv c hrho hD hhpos hh
    (show R ≤ 2 * h by linarith) hQ
  calc
    _ ≤ 25 * D * h / rho := hbound
    _ ≤ 25 * D * (2 * R) / rho :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhR (by positivity)) hrho.le
    _ = _ := by ring

/-- One actual label per surviving base cell retains a quantitative fraction. -/
theorem retainedScales_representatives {X : Type*} (P : Finset X) (p : X → Point3)
    (scales : Finset ℝ) (uv : ℝ × ℝ) {rho D : ℝ}
    (hrho : 0 < rho) (hD : 0 < D) (hbase : rho ∈ scales)
    (hret : (P.card : ℝ) / 2 ≤ (retainedScales P p scales uv rho D).card) :
    ∃ Q : Finset X, Q ⊆ retainedScales P p scales uv rho D ∧
      (P.card : ℝ) / (2 * D) ≤ Q.card ∧
      Set.InjOn (fun i => projectedCell uv rho (p i)) (↑Q) := by
  let S := retainedScales P p scales uv rho D
  let f := fun i => projectedCell uv rho (p i)
  obtain ⟨Q, hQS, _himage, hinj, hcard⟩ := exists_cell_representatives S f
  have hfiber : ∀ k ∈ S.image f, ((S.filter (fun i => f i = k)).card : ℝ) ≤ D := by
    intro k hk
    obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hk
    have hsub : S.filter (fun j => f j = k) ⊆ P.filter (fun j => f j = f i) := by
      intro j hj
      obtain ⟨hjS, hjk⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨retainedScales_subset P p scales uv rho D hjS, hjk.trans hik.symm⟩
    have hh := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (retainedScales_cell_bound P p scales uv rho D hbase hi)
    simpa only [mul_div_cancel_right₀ D hrho.ne'] using hh
  have hpopulation : (S.card : ℝ) ≤ D * Q.card := by
    calc
      _ = ∑ k ∈ S.image f, ((S.filter (fun i => f i = k)).card : ℝ) := by
        exact_mod_cast Finset.card_eq_sum_card_image f S
      _ ≤ ∑ _k ∈ S.image f, D := Finset.sum_le_sum hfiber
      _ = D * Q.card := by simp only [Finset.sum_const, nsmul_eq_mul, hcard]; ring
  refine ⟨Q, hQS, ?_, hinj⟩
  apply (div_le_iff₀ (show 0 < 2 * D by positivity)).2
  nlinarith

end FinitePlaneProjectionGrid
