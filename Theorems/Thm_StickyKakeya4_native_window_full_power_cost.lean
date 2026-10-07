import Mathlib

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeWindowFullPowerCost

/-- The fixed coarse endpoint uses global population and nonemptiness, so
the complete localized Euclidean window cost remains linear in K. The B
estimate is the already proved intrinsic fixed-menu gap bound. -/
theorem complete_cost_le {rho K B e s : ℝ} (J : ℕ)
    (hrho : 0 < rho) (hK : 0 ≤ K) (hs2 : s ≤ 2)
    (HK : K ≤ rho^(-e)) (HB : B^2 ≤ 512*rho^(-(3/(J:ℝ)))) :
    (4:ℝ)^s*((2:ℝ)^40*K*B^2) ≤ (2:ℝ)^54*rho^(-(e+3/(J:ℝ))) := by
  have hproduct : K*B^2 ≤ 512*rho^(-(e+3/(J:ℝ))) := by
    have hp := mul_le_mul HK HB (sq_nonneg B) (Real.rpow_nonneg hrho.le (-e))
    calc
      _ ≤ rho^(-e)*(512*rho^(-(3/(J:ℝ)))) := hp
      _ = 512*(rho^(-e)*rho^(-(3/(J:ℝ)))) := by ring
      _ = _ := by rw [←Real.rpow_add hrho]; congr 2; ring
  have h4 : (4:ℝ)^s ≤ 16 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) hs2
    norm_num at hh
    exact hh
  calc
    _ = ((4:ℝ)^s*(2:ℝ)^40)*(K*B^2) := by ring
    _ ≤ (16*(2:ℝ)^40)*(512*rho^(-(e+3/(J:ℝ)))) := mul_le_mul
      (mul_le_mul_of_nonneg_right h4 (by positivity)) hproduct
      (mul_nonneg hK (sq_nonneg _)) (by positivity)
    _ ≤ (2:ℝ)^54*rho^(-(e+3/(J:ℝ))) := by
      have hc : 16*(2:ℝ)^40*512 ≤ (2:ℝ)^54 := by norm_num
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc
        (Real.rpow_nonneg hrho.le (-(e+3/(J:ℝ))))

/-- One explicit fixed cutoff pays the entire remaining fixed factor.
This cutoff can be imposed before selecting the actual source. -/
theorem paid_complete_cost {rho K B e s b epsilon : ℝ} (J : ℕ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hK : 0 ≤ K) (hs2 : s ≤ 2) (hb : 0 < b)
    (HK : K ≤ rho^(-e)) (HB : B^2 ≤ 512*rho^(-(3/(J:ℝ))))
    (hcut : rho ≤ (2:ℝ)^(-54/b)) (hbudget : e+3/(J:ℝ)+b ≤ epsilon) :
    (4:ℝ)^s*((2:ℝ)^40*K*B^2) ≤ rho^(-epsilon) := by
  have hfixed : (2:ℝ)^54 ≤ rho^(-b) := by
    have hexp : (-54/b)*(-b)=(54:ℝ) := by field_simp
    calc
      (2:ℝ)^54 = (2:ℝ)^((-54/b)*(-b)) := by rw [hexp]; norm_num
      _ = ((2:ℝ)^(-54/b))^(-b) := Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos hrho hcut (neg_nonpos.mpr hb.le)
  calc
    _ ≤ (2:ℝ)^54*rho^(-(e+3/(J:ℝ))) := complete_cost_le J hrho hK hs2 HK HB
    _ ≤ rho^(-b)*rho^(-(e+3/(J:ℝ))) := mul_le_mul_of_nonneg_right hfixed (by positivity)
    _ = rho^(-(e+3/(J:ℝ)+b)) := by rw [←Real.rpow_add hrho]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hrho hrho1 (neg_le_neg hbudget)

end NativeWindowFullPowerCost
