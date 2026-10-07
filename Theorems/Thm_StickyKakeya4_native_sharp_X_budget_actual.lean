import Theorems.Thm_StickyKakeya4_native_sharp_X_budget_cutoff

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeSharpXBudgetActual
open NativeSharpXPowerAlgebra NativeSharpXBudgetCosts NativeSharpXBudgetPower NativeSharpXBudgetCutoff
open NativeRetainedSliceBudgetSource NativeRankExponentHierarchy

/-- The explicit actual X-fiber coefficient is a small Delta power after
one source cutoff chosen before D. All three native refinement costs and the
actual rank/history/test-radius fields are consumed, rather than assumed
bounds for X. -/
theorem actual_fiber_coefficient_le_power
    {delta eta zeta lambda b tau seed c2 r q eta0 c epsilon : ℝ}
    (he : 0 < epsilon) (he0 : 0 < eta0) (he01 : eta0 ≤ 1) (heSmall : eta0 ≤ epsilon/2048)
    (hc : 0 < c) (hc1 : c ≤ 1) (hcQ : c ≤ quotientTolerance (epsilon/4)/24)
    (F1 F2 G Q1 Q2 F3 Q3 g m : ℕ) (i : Fin 4) (hm6 : 6 ≤ m) (hell : i.val+1 ≤ 3)
    (hd : 0 < delta) (hsmall : delta ≤ sourceCutoff epsilon c g he hc)
    (heta : 0 ≤ eta) (hetaSeed : eta ≤ seed/8) (hseed0 : 0 ≤ seed)
    (hQ1 : 1 ≤ Q1) (hQ3 : 1 ≤ Q3) (hGF : G ≤ F2)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta) ≤ delta^(-c2))
    (H3 : (F3:ℝ)*(Q3:ℝ)^4 ≤ delta^(-(commonBudget eta0 c/4)))
    (htau0 : 0 ≤ tau) (htau : tau ≤ commonBudget eta0 c/1024) (hseed : seed ≤ tau/16384)
    (hzeta : zeta ≤ seed/256) (hc2 : c2=commonBudget eta0 c/4)
    (hr : 0 < r) (hr1 : r ≤ 1) (hrdelta : r ≤ delta^(cutoff c i))
    (hlambda : lambda=r^(rankLoss eta0 c i)/(4*((g:ℝ)+1)))
    (hb : r^((2*((i.val+1:ℕ):ℝ)+1)*rankLoss eta0 c i) ≤ b)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hqraw : r^(2*c)/(2*delta^(-(1/(g:ℝ)))) ≤ q)
    (hscale : ((64:ℝ)/((2^m:ℕ):ℝ))^2 ≤ 6144*r) :
    fiberCoefficient delta eta zeta tau (seed/8) c2 lambda b F1 G Q2 F3 Q3 q (i.val+1) ≤
      ((64:ℝ)/((2^m:ℕ):ℝ))^(-epsilon) := by
  let rho := (64:ℝ)/((2^m:ℕ):ℝ)
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ)<((2^m:ℕ):ℝ))).mpr
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hm6
    norm_num only [show (2:ℕ)^6=64 by norm_num] at hh
    exact_mod_cast hh
  have hd1 := hsmall.trans (sourceCutoff_le_one epsilon c g he hc)
  have ht := commonBudget_pos he0 hc
  have hloss := rankLoss_pos he0 hc i
  have hle := rankLoss_le_initial he0.le hc.le hc1 i
  have heQuarter : 0 < epsilon/4 := by positivity
  have hqlo := actual_quotient_test hd hr hr1 heQuarter he0.le he01
    (show eta0 ≤ (epsilon/4)/336 by linarith only [heSmall,he]) hc hc1 hcQ i hrdelta htau0 g htau hgrid hqraw
  obtain ⟨heQ,heQ1,heQsmall⟩ := quotientTolerance_bounds heQuarter
  have hRank := fiber_coefficient_rank_bound hd hd1 heta hetaSeed hseed0 ht.le htau hseed hzeta hc2
    F1 F2 G Q1 Q2 F3 Q3 g (i.val+1) hQ1 hQ3 hGF hell H1 H2 H3
    hr hr1 hloss.le hrdelta (cutoff_mul_rankLoss eta0 c i).symm hlambda hb hq hq1 hqlo
  have hRho := rank_bound_to_scale g hrho hloss.le (hle.trans he01) heQ.le heQ1 hscale hRank
  have hPaid := sourceCutoff_pays epsilon c g he hc delta hd hsmall rho r (cutoff c i)
    hrho (cutoff_bounds hc hc1 i).2.2 hrdelta hscale
  have hexp : epsilon/4+(74*rankLoss eta0 c i+16*quotientTolerance (epsilon/4)/3) ≤ epsilon := by
    linarith only [hle.trans heSmall,heQsmall,he]
  exact hRho.trans (calc
    _ ≤ rho^(-(epsilon/4))*rho^(-(74*rankLoss eta0 c i+16*quotientTolerance (epsilon/4)/3)) :=
      mul_le_mul_of_nonneg_right hPaid (by positivity)
    _ = rho^(-(epsilon/4+(74*rankLoss eta0 c i+16*quotientTolerance (epsilon/4)/3))) := by
      rw [←Real.rpow_add hrho]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hrho hrho1 (neg_le_neg hexp))

end NativeSharpXBudgetActual
