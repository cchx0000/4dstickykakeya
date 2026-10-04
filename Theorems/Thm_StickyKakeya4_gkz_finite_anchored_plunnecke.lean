import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped Pointwise BigOperators

namespace GKZFiniteAnchoredPlunnecke
variable {G I : Type*} [AddCommGroup G] [DecidableEq G]

/-- Mathlib's proved homogeneous Plünnecke inequality, with a real-valued
anchor expansion bound. The hypothesis controls X+U, not merely U. -/
theorem iterated_sum_from_anchor (X U : Finset G) (hX : X.Nonempty)
    {M : ℝ} (hsmall : ((X+U).card : ℝ) ≤ M*X.card) (n : ℕ) :
    ((n • U).card : ℝ) ≤ M^n*X.card := by
  have hpos : 0 < (X.card : ℝ) := Nat.cast_pos.mpr hX.card_pos
  have hPR : ((n • U).card : ℚ≥0) ≤
      (((X+U).card : ℚ≥0)/(X.card : ℚ≥0))^n*X.card :=
    Finset.pluennecke_ruzsa_inequality_nsmul_add hX U n
  have hReal : ((n • U).card : ℝ) ≤
      (((X+U).card : ℝ)/(X.card : ℝ))^n*X.card := by
    have hcast : ((n • U).card : ℝ) ≤
        ((((X+U).card : ℚ≥0)/(X.card : ℚ≥0))^n*X.card : ℚ≥0) := by
      exact_mod_cast hPR
    simpa using hcast
  have hratio : ((X+U).card : ℝ)/(X.card : ℝ) ≤ M := (div_le_iff₀ hpos).mpr hsmall
  exact hReal.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hratio n) (Nat.cast_nonneg _))

/-- A fixed union of dilates has small anchored expansion when each actual
dilate has that property. Ordinary Plünnecke then controls its bounded sums. -/
theorem finite_union_anchored_sum (X : Finset G) (J : Finset I) (D : I → Finset G)
    (hX : X.Nonempty) {M : ℝ}
    (hsmall : ∀ i ∈ J, ((X+D i).card : ℝ) ≤ M*X.card) (n : ℕ) :
    ((n • J.biUnion D).card : ℝ) ≤ ((J.card : ℝ)*M)^n*X.card := by
  apply iterated_sum_from_anchor X (J.biUnion D) hX
  have hsub : X+J.biUnion D ⊆ J.biUnion (fun i => X+D i) := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨i, hi, hy⟩ := Finset.mem_biUnion.mp hy
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_add.mpr ⟨x, hx, y, hy, rfl⟩⟩
  calc
    _ ≤ ((J.biUnion (fun i => X+D i)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ i ∈ J, ((X+D i).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ J, M*(X.card : ℝ) := Finset.sum_le_sum hsmall
    _ = _ := by simp [mul_assoc]

/-- A large actual common subset converts two self-sum bounds into both mixed
sum and mixed difference bounds by proved finite Ruzsa inequalities. -/
theorem original_overlap_mixed_bounds (X Y F : Finset G) {N eta M : ℝ}
    (hN : 0 < N) (hM : 0 ≤ M) (hFX : F ⊆ X) (hFY : F ⊆ Y)
    (hF : eta*N ≤ F.card)
    (hXX : ((X+X).card : ℝ) ≤ M*N) (hYY : ((Y+Y).card : ℝ) ≤ M*N) :
    eta*((X+Y).card : ℝ) ≤ M^2*N ∧
    eta*((X-Y).card : ℝ) ≤ M^2*N := by
  have hXF : ((X+F).card : ℝ) ≤ M*N :=
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.add_subset_add (Finset.Subset.refl X) hFX))).trans hXX
  have hFY' : ((F+Y).card : ℝ) ≤ M*N :=
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.add_subset_add hFY (Finset.Subset.refl Y)))).trans hYY
  have hYF : ((Y+F).card : ℝ) ≤ M*N := by simpa only [add_comm Y F] using hFY'
  have hprod : ((X+F).card : ℝ)*(F+Y).card ≤ (M*N)^2 := by
    simpa only [pow_two] using mul_le_mul hXF hFY' (Nat.cast_nonneg _) (mul_nonneg hM hN.le)
  have hprod' : ((X+F).card : ℝ)*(Y+F).card ≤ (M*N)^2 := by
    simpa only [pow_two] using mul_le_mul hXF hYF (Nat.cast_nonneg _) (mul_nonneg hM hN.le)
  constructor
  · have hRT : ((X+Y).card : ℝ)*F.card ≤ ((X+F).card : ℝ)*(F+Y).card := by
      exact_mod_cast Finset.ruzsa_triangle_inequality_add_add_add X F Y
    have hlo := mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg (X+Y).card)
    apply (mul_le_mul_iff_left₀ hN).mp
    nlinarith only [hlo.trans (hRT.trans hprod)]
  · have hRT : ((X-Y).card : ℝ)*F.card ≤ ((X+F).card : ℝ)*(Y+F).card := by
      exact_mod_cast Finset.ruzsa_triangle_inequality_sub_add_add X F Y
    have hlo := mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg (X-Y).card)
    apply (mul_le_mul_iff_left₀ hN).mp
    nlinarith only [hlo.trans (hRT.trans hprod')]

end GKZFiniteAnchoredPlunnecke
