import Theorems.Thm_StickyKakeya4_native_reference_slice_budget_cutoff

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000
noncomputable section
namespace NativeAngularRankContradiction
open StickyKakeya4

/-- Cancel the actual occupied angular count between its source lower and
its rank-two affine-line upper. No cardinality is identified with mass. -/
theorem angular_count_cancellation {kappa rho r loss A B count : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) (hA : 0 ≤ A)
    (hlower : rho^(-kappa) ≤ A*r^(-9*loss)*count)
    (hupper : count ≤ B*rho^(-1:ℝ)) :
    1 ≤ A*B*r^(-9*loss)*rho^(kappa-1) := by
  have hleft : rho^(-kappa)*rho^kappa=1 := by
    rw [←Real.rpow_add hrho]
    simp only [neg_add_cancel,Real.rpow_zero]
  calc
    1 = rho^(-kappa)*rho^kappa := hleft.symm
    _ ≤ (A*r^(-9*loss)*count)*rho^kappa :=
      mul_le_mul_of_nonneg_right hlower (Real.rpow_nonneg hrho.le _)
    _ ≤ (A*r^(-9*loss)*(B*rho^(-1:ℝ)))*rho^kappa :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hupper (by positivity)) (by positivity)
    _ = A*B*r^(-9*loss)*(rho^(-1:ℝ)*rho^kappa) := by ring
    _ = _ := by rw [←Real.rpow_add hrho]; congr 2; ring

/-- The wide geometric scale bound rho<=160r^(1/3) suffices. All losses
remain r-powers; rankLoss is never incorrectly changed into a delta loss. -/
theorem rank_gain_survives {kappa rho r loss : ℝ}
    (hk : 1 < kappa) (hk2 : kappa ≤ 2) (hrho : 0 < rho)
    (hr : 0 < r) (hr1 : r ≤ 1) (hloss : loss ≤ (kappa-1)/108)
    (hscale : rho ≤ 160*r^((1:ℝ)/3)) :
    r^(-9*loss)*rho^(kappa-1) ≤ 160*r^((kappa-1)/4) := by
  have hgap : 0 < kappa-1 := sub_pos.mpr hk
  have hconstant : (160:ℝ)^(kappa-1) ≤ 160 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 160) (show kappa-1 ≤ 1 by linarith only [hk2])
  have hp := Real.rpow_le_rpow hrho.le hscale hgap.le
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hr.le _),←Real.rpow_mul hr.le] at hp
  have hsmall : r^(-9*loss+(1/3)*(kappa-1)) ≤ r^((kappa-1)/4) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith only [hloss])
  calc
    _ ≤ r^(-9*loss)*((160:ℝ)^(kappa-1)*r^((1/3)*(kappa-1))) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ r^(-9*loss)*(160*r^((1/3)*(kappa-1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hconstant (by positivity)) (by positivity)
    _ = 160*r^(-9*loss+(1/3)*(kappa-1)) := by rw [Real.rpow_add hr]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by norm_num)

/-- Rank two cannot carry the source lower at a sufficiently fine r. Rank
three is separately excluded by the already proved kappa+rank<=4 whenkappa>1. -/
theorem incompatible_rank_two_counts {kappa rho r loss A B count : ℝ}
    (hk : 1 < kappa) (hk2 : kappa ≤ 2) (hrho : 0 < rho)
    (hr : 0 < r) (hr1 : r ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hloss : loss ≤ (kappa-1)/108) (hscale : rho ≤ 160*r^((1:ℝ)/3))
    (hlower : rho^(-kappa) ≤ A*r^(-9*loss)*count)
    (hupper : count ≤ B*rho^(-1:ℝ))
    (hsmall : 160*A*B*r^((kappa-1)/4) < 1) : False := by
  have hl := angular_count_cancellation hrho hr hA hlower hupper
  have hu := mul_le_mul_of_nonneg_left (rank_gain_survives hk hk2 hrho hr hr1 hloss hscale)
    (mul_nonneg hA hB)
  have hh : A*B*r^(-9*loss)*rho^(kappa-1) ≤ 160*A*B*r^((kappa-1)/4) := by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hu
  exact (not_lt_of_ge (hl.trans hh)) hsmall

/-- One cutoff chosen after the fixed source constants (including g), but
before D, pays the contradiction uniformly across all possible rank cutoffs. -/
theorem exists_original_scale_cutoff {kappa amin C : ℝ}
    (hk : 1 < kappa) (ha : 0 < amin) (hC : 0 ≤ C) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀delta r a : ℝ,0 < delta → delta ≤ delta0 → 0 < r →
        amin ≤ a → r ≤ delta^a → C*r^((kappa-1)/4) < 1 := by
  obtain ⟨d,hd,hd1,H⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < amin*((kappa-1)/4) by positivity) hC (by norm_num : (0:ℝ)<1/2)
  refine ⟨d,hd,hd1,?_⟩
  intro delta r a hdelta hsmall hr ha' hrscale
  have hroot : r ≤ delta^amin := hrscale.trans
    (Real.rpow_le_rpow_of_exponent_ge hdelta (hsmall.trans hd1) ha')
  have hp := Real.rpow_le_rpow hr.le hroot (show 0 ≤ (kappa-1)/4 by linarith only [hk])
  rw [←Real.rpow_mul hdelta.le] at hp
  have hb := (mul_le_mul_of_nonneg_left hp hC).trans (H delta hdelta hsmall)
  linarith only [hb]

end NativeAngularRankContradiction
