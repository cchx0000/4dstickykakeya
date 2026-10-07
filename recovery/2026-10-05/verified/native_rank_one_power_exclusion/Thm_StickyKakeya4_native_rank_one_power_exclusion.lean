import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000
noncomputable section

namespace NativeRankOnePowerExclusion

/-- The actual retained lower bound and original-reference local upper bound
force a scalar budget. The factor 6144 is exactly 64 times the dyadic
rounding factor 96; its exponent is bounded using kappa ≤ 3. -/
theorem rank_one_budget_le {delta r kappa eta a N G Q theta nu M : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hr : 0 < r)
    (hk : 0 < kappa) (hk3 : kappa ≤ 3) (heta : eta ≤ kappa / 2)
    (ha : 0 < a) (hradius : r ≤ delta ^ a) (hN : 0 < N)
    (hNr : 1 / 96 ≤ N * r) (hG : 0 < G) (hQ : 0 ≤ Q)
    (hlower : r ^ eta / G * delta ^ (-kappa + nu) ≤ M)
    (hupper : M ≤ 9261 * Q ^ (2 : ℕ) * delta ^ (-theta) * (N * delta / 64) ^ (-kappa)) :
    1 ≤ (9261 * (6144 : ℝ) ^ (3 : ℕ)) * G * Q ^ (2 : ℕ) *
      delta ^ (a * kappa / 2 - theta - nu) := by
  have hr1 : r ≤ 1 := hradius.trans (Real.rpow_le_one hd.le hd1 ha.le)
  have heps : 0 < N * delta / 64 := by positivity
  have hbase : 0 < 6144 * r := by positivity
  have hepslower : delta / (6144 * r) ≤ N * delta / 64 := by
    apply (div_le_iff₀ hbase).mpr
    have hh := mul_le_mul_of_nonneg_right hNr hd.le
    nlinarith only [hh]
  have hconstant : (6144 : ℝ) ^ kappa ≤ (6144 : ℝ) ^ (3 : ℕ) := by
    calc
      _ ≤ (6144 : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hk3
      _ = _ := by norm_num
  have hepspow : (N * delta / 64) ^ (-kappa) ≤
      (6144 : ℝ) ^ (3 : ℕ) * r ^ kappa * delta ^ (-kappa) := by
    calc
      _ ≤ (delta / (6144 * r)) ^ (-kappa) :=
        Real.rpow_le_rpow_of_nonpos (div_pos hd hbase) hepslower (by linarith)
      _ = delta ^ (-kappa) * ((6144 : ℝ) ^ kappa * r ^ kappa) := by
        rw [Real.div_rpow hd.le hbase.le, Real.rpow_neg hbase.le, div_inv_eq_mul,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6144) hr.le]
      _ ≤ delta ^ (-kappa) * ((6144 : ℝ) ^ (3 : ℕ) * r ^ kappa) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hr.le _))
          (Real.rpow_nonneg hd.le _)
      _ = _ := by ring
  have hraw : r ^ eta / G * delta ^ (-kappa + nu) ≤
      9261 * Q ^ (2 : ℕ) * delta ^ (-theta) *
        ((6144 : ℝ) ^ (3 : ℕ) * r ^ kappa * delta ^ (-kappa)) := by
    exact hlower.trans (hupper.trans (mul_le_mul_of_nonneg_left hepspow
      (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hQ 2))
        (Real.rpow_nonneg hd.le _))))
  have hnormalize : (r ^ eta / G * delta ^ (-kappa + nu)) *
      (G * r ^ (-eta) * delta ^ (kappa - nu)) = 1 := by
    calc
      _ = G⁻¹ * G * (r ^ eta * r ^ (-eta)) *
          (delta ^ (-kappa + nu) * delta ^ (kappa - nu)) := by ring
      _ = 1 := by
        rw [inv_mul_cancel₀ hG.ne', ← Real.rpow_add hr, ← Real.rpow_add hd]
        simp
  have hrcombine : r ^ kappa * r ^ (-eta) = r ^ (kappa - eta) := by
    rw [← Real.rpow_add hr]
    congr 1
  have hdcombine : delta ^ (-theta) * delta ^ (-kappa) * delta ^ (kappa - nu) =
      delta ^ (-theta - nu) := by
    rw [← Real.rpow_add hd, ← Real.rpow_add hd]
    congr 1
    ring
  have hnormalized : 1 ≤ (9261 * (6144 : ℝ) ^ (3 : ℕ)) * G * Q ^ (2 : ℕ) *
      r ^ (kappa - eta) * delta ^ (-theta - nu) := by
    calc
      1 = (r ^ eta / G * delta ^ (-kappa + nu)) *
          (G * r ^ (-eta) * delta ^ (kappa - nu)) := hnormalize.symm
      _ ≤ (9261 * Q ^ (2 : ℕ) * delta ^ (-theta) *
          ((6144 : ℝ) ^ (3 : ℕ) * r ^ kappa * delta ^ (-kappa))) *
          (G * r ^ (-eta) * delta ^ (kappa - nu)) :=
        mul_le_mul_of_nonneg_right hraw (by positivity)
      _ = (9261 * (6144 : ℝ) ^ (3 : ℕ)) * G * Q ^ (2 : ℕ) *
          (r ^ kappa * r ^ (-eta)) *
          (delta ^ (-theta) * delta ^ (-kappa) * delta ^ (kappa - nu)) := by ring
      _ = _ := by rw [hrcombine, hdcombine]
  have hrpower : r ^ (kappa - eta) ≤ delta ^ (a * kappa / 2) := by
    calc
      _ ≤ r ^ (kappa / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
      _ ≤ (delta ^ a) ^ (kappa / 2) := Real.rpow_le_rpow hr.le hradius (by positivity)
      _ = _ := by rw [← Real.rpow_mul hd.le]; congr 1; ring
  calc
    1 ≤ (9261 * (6144 : ℝ) ^ (3 : ℕ)) * G * Q ^ (2 : ℕ) *
        r ^ (kappa - eta) * delta ^ (-theta - nu) := hnormalized
    _ ≤ (9261 * (6144 : ℝ) ^ (3 : ℕ)) * G * Q ^ (2 : ℕ) *
        delta ^ (a * kappa / 2) * delta ^ (-theta - nu) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrpower (by positivity)) (Real.rpow_nonneg hd.le _)
    _ = (9261 * (6144 : ℝ) ^ (3 : ℕ)) * G * Q ^ (2 : ℕ) *
        (delta ^ (a * kappa / 2) * delta ^ (-theta - nu)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hd]
      congr 2
      ring

/-- A strict power cutoff contradicts the two actual rank-one estimates. -/
theorem rank_one_excluded {delta r kappa eta a N G Q theta nu M : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hr : 0 < r)
    (hk : 0 < kappa) (hk3 : kappa ≤ 3) (heta : eta ≤ kappa / 2)
    (ha : 0 < a) (hradius : r ≤ delta ^ a) (hN : 0 < N)
    (hNr : 1 / 96 ≤ N * r) (hG : 0 < G) (hQ : 0 ≤ Q)
    (hlower : r ^ eta / G * delta ^ (-kappa + nu) ≤ M)
    (hupper : M ≤ 9261 * Q ^ (2 : ℕ) * delta ^ (-theta) * (N * delta / 64) ^ (-kappa))
    (hcut : (9261 * (6144 : ℝ) ^ (3 : ℕ)) * G * Q ^ (2 : ℕ) *
      delta ^ (a * kappa / 2 - theta - nu) < 1) : False := by
  exact (not_lt_of_ge (rank_one_budget_le hd hd1 hr hk hk3 heta ha hradius hN hNr hG hQ
    hlower hupper)) hcut

end NativeRankOnePowerExclusion
