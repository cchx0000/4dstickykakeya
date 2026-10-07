import Theorems.Thm_StickyKakeya4_native_actual_new_cut_budget
import Theorems.Thm_StickyKakeya4_native_retention_output_power

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
noncomputable section
namespace NativeNewCutOutputBudget
open NativeActualNewCutBudget NativeRetentionOutputPower

/-- The relative multiplier in the existing paid third-core record is the
literal natural cost of the new cuts, once the old quotient cost is removed. -/
lemma actual_multiplier (Cbase Cpre : ℝ) (N : ℕ)
    (hCbase : 0 < Cbase) (hCpre : 0 < Cpre)
    (hidentity : Cpre = Cbase * (N : ℝ)) :
    max 1 (Cpre / Cbase) = (N : ℝ) := by
  have hN : 0 < N := by
    by_contra hn
    have hzero : N = 0 := by omega
    simp only [hzero, Nat.cast_zero, mul_zero] at hidentity
    linarith only [hidentity, hCpre]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [hidentity, mul_div_cancel_left₀ _ hCbase.ne', max_eq_right hN1]

/-- The actual new-cut charge pays the square appearing in the same-T Y
constant. The old graph, quotient and third-core allowances are not repeated. -/
theorem paid_Y_constant_at_output
    (K Ksupport normal g R0 m : ℕ) (hnormal : normal ≤ 4)
    (meshConstant row r loss d metric epsilon kappa epsilonPaid Delta : ℝ)
    (depths : Fin K → ℕ) (Cbase Cpre : ℝ)
    (hC : 0 ≤ meshConstant) (hrow : 0 ≤ row) (hr : 0 < r) (hr1 : r ≤ 1)
    (hloss : 0 ≤ loss) (hd : 0 ≤ d) (hmetric : 0 ≤ metric)
    (hepsilon : 0 ≤ epsilon) (hepsilon4 : epsilon ≤ 1 / 4)
    (hPaid : 0 ≤ epsilonPaid) (hLip : metric ≤ r ^ (-2 * epsilon))
    (hsmall : (64 : ℝ) / ((2 ^ m : ℕ) : ℝ) ≤ 1)
    (hstopLo : 3072 * r ≤ ((64 : ℝ) / ((2 ^ m : ℕ) : ℝ)) ^ 2)
    (hstopHi : ((64 : ℝ) / ((2 ^ m : ℕ) : ℝ)) ^ 2 ≤ 6144 * r)
    (hHeight : ((8 * R0 : ℕ) : ℝ) ≤
      1280 * (((64 : ℝ) / ((2 ^ m : ℕ) : ℝ)) / 64) ^ (-2 * epsilon))
    (hCbase : 0 < Cbase) (hCpre : 0 < Cpre)
    (hidentity : Cpre = Cbase *
      (newCutCharge K Ksupport normal g R0 meshConstant row r loss d metric kappa
        (fun j => 64 / ((2 ^ (depths j) : ℕ) : ℝ)) : ℝ))
    (hD : 0 < Delta)
    (hbase : 64 * Delta ≤ 2 * max
      ((5 / 4 : ℝ) * ((64 : ℝ) / ((2 ^ m : ℕ) : ℝ)) ^ (1 - 2 * epsilon))
      ((64 : ℝ) / ((2 ^ m : ℕ) : ℝ)))
    (hnu : newExponent K epsilon loss d ≤ 1 / 2) :
    (max 1 (Cpre / Cbase)) ^ 2 *
        ((64 : ℝ) / ((2 ^ m : ℕ) : ℝ)) ^ (-epsilonPaid) ≤
      (6144 * (fixedFactor K Ksupport g meshConstant row) ^ 2) *
        Delta ^ (-(8 * newExponent K epsilon loss d + 2 * epsilonPaid)) := by
  let rho : ℝ := 64 / ((2 ^ m : ℕ) : ℝ)
  let nu := newExponent K epsilon loss d
  let C := fixedFactor K Ksupport g meshConstant row
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hnu0 : 0 ≤ nu := by dsimp [nu, newExponent]; positivity
  have hM := source_new_cut_cost K Ksupport normal g R0 m hnormal
    meshConstant row r loss d metric epsilon kappa depths
    hC hrow hr hr1 hloss hd hmetric hepsilon hLip hsmall hstopLo hHeight
  rw [← actual_multiplier Cbase Cpre _ hCbase hCpre hidentity] at hM
  have hF : (max 1 (Cpre / Cbase)) ^ 2 * rho ^ (-epsilonPaid) ≤
      C ^ 2 * r ^ (-(2 * nu)) * rho ^ (-epsilonPaid) * Delta ^ (-(0 : ℝ)) := by
    calc
      _ ≤ (C * r ^ (-nu)) ^ 2 * rho ^ (-epsilonPaid) := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hM 2) (Real.rpow_nonneg hrho.le _)
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast hr.le]
        norm_num only [Nat.cast_ofNat, neg_zero, Real.rpow_zero, mul_one]
        congr 2
        ring
  have hshape : Delta ^ 2 ≤ rho := configured_square_le_reference hrho hsmall hD.le
    hepsilon hepsilon4 hbase
  have hout := total_retention_at_output (C := C ^ 2) (r := r) (rho := rho)
    (Delta := Delta) (nu := 2 * nu) (A := epsilonPaid) (zeta := 0)
    (sq_nonneg C) hD hrho.le (by positivity) (by dsimp [nu]; linarith only [hnu])
    hPaid hshape hstopHi hF
  have hexp : 4 * (2 * nu) + 2 * epsilonPaid + 0 = 8 * nu + 2 * epsilonPaid := by ring
  rw [hexp] at hout
  exact hout

/-- The coefficient cutoff is chosen from the fixed menu counts, g and the
requested tolerance before the source and every output scale. -/
theorem exists_Y_output_cutoff (K Ksupport g : ℕ)
    (meshConstant row eta53 : ℝ) (hC : 0 ≤ meshConstant) (hrow : 0 ≤ row)
    (heta53 : 0 < eta53) :
    ∃ D0 : ℝ, 0 < D0 ∧ D0 ≤ 1 ∧ ∀ Delta deltaY F nu epsilonPaid : ℝ,
      0 < deltaY → deltaY ≤ Delta → Delta ≤ D0 →
      8 * nu + 2 * epsilonPaid ≤ eta53 / 2 →
      F ≤ (6144 * (fixedFactor K Ksupport g meshConstant row) ^ 2) *
        Delta ^ (-(8 * nu + 2 * epsilonPaid)) → F ≤ deltaY ^ (-eta53) := by
  have hfixed : 0 < fixedFactor K Ksupport g meshConstant row := by
    unfold fixedFactor offsetCoefficient
    positivity
  obtain ⟨D0, hD0, hD01, H⟩ := exists_uniform_retention_cutoff
    (32 * eta53) (6144 * (fixedFactor K Ksupport g meshConstant row) ^ 2)
    (by positivity) (by positivity)
  refine ⟨D0, hD0, hD01, ?_⟩
  intro Delta deltaY F nu epsilonPaid hY hYD hsmall hmargin hF
  have hD : 0 < Delta := hY.trans_le hYD
  have hh := H Delta F (8 * nu + 2 * epsilonPaid) hD hsmall
    (show 8 * nu + 2 * epsilonPaid ≤ (32 * eta53) / 64 by linarith only [hmargin]) hF
  have heq : (32 * eta53) / 32 = eta53 := by ring
  rw [heq] at hh
  exact hh.trans (Real.rpow_le_rpow_of_nonpos hY hYD (neg_nonpos.mpr heta53.le))

end NativeNewCutOutputBudget
