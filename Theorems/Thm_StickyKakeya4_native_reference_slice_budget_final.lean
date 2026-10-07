import Theorems.Thm_StickyKakeya4_native_reference_slice_budget_cutoff

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeReferenceSliceBudgetFinal
open StickyKakeya4 NativeReferenceSliceBudgetSource NativeReferenceSliceBudgetCutoff
open NativeRankExponentHierarchy NativeFixedCompactKakeyaExponent NativeSquaredGrainQueries
open NativeHorizontalMenuScaleCost NativeAllTwoScaleConfiguration

/-- Requested reference AD loss, paid entirely by the actual first/second
source costs and history. J and eta0 precede tau; the displayed source cutoff
is chosen after g and before D. i.val+1 is the actual tuple length. -/
theorem actual_reference_constant_le_power
    {delta eta zeta lambda b tau seed c2 r eta0 c epsilon : ℝ}
    (he : 0 < epsilon) (he0 : 0 < eta0) (he01 : eta0 ≤ 1) (heSmall : eta0 ≤ epsilon/168)
    (hc : 0 < c) (hcsmall : c ≤ 1/2)
    (F1 F2 G Q1 Q2 g J m : ℕ) (i : Fin 4)
    (hJ : 0 < J) (hJloss : 3/(J:ℝ) ≤ epsilon/4) (hm6 : 6 ≤ m) (hell : i.val+1 ≤ 3)
    (hd : 0 < delta) (hsmall : delta ≤ sourceCutoff epsilon c g he hc) (heta : 0 ≤ eta)
    (hF1 : 0 < F1) (hG : 0 < G) (hQ1 : 1 ≤ Q1) (hQ2 : 0 < Q2) (hGF : G ≤ F2)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta) ≤ delta^(-c2))
    (htau : tau ≤ commonBudget eta0 c/1024) (hseed : seed ≤ tau/16384)
    (hzeta : zeta ≤ seed/256) (hc2 : c2=commonBudget eta0 c/4)
    (hr : 0 < r) (hr1 : r ≤ 1) (hrdelta : r ≤ delta^(cutoff c i))
    (hlambda : lambda=r^(rankLoss eta0 c i)/(4*((g:ℝ)+1)))
    (hb : r^((2*((i.val+1:ℕ):ℝ)+1)*rankLoss eta0 c i) ≤ b)
    (hscale : ((64:ℝ)/((2^m:ℕ):ℝ))^2 ≤ 6144*r) :
    actualConstant delta eta zeta lambda b F1 G Q2 tau seed c2
        (min (boundaryWindow tau) ((tau/16)/1000)) J m (3-extremalExponent) ≤
      ((64:ℝ)/((2^m:ℕ):ℝ))^(-epsilon) := by
  have hd1 := hsmall.trans (sourceCutoff_le_one epsilon c g he hc)
  have hc1 : c ≤ 1 := by linarith only [hcsmall]
  have ht := commonBudget_pos he0 hc
  have hloss := rankLoss_pos he0 hc i
  have hle := rankLoss_le_initial he0.le hc.le hc1 i
  have hw : min (boundaryWindow tau) ((tau/16)/1000) ≤ tau/16000 := by
    calc
      _ ≤ (tau/16)/1000 := min_le_right _ _
      _ = _ := by ring
  have Hbound := actual_reference_constant_bound hd hd1 heta F1 F2 G Q1 Q2 g (i.val+1) J m
    hF1 hG hQ1 hQ2 hGF H1 H2 ht.le htau hseed hzeta hc2 hw
    hr hr1 hloss.le (hle.trans he01) hell hrdelta (cutoff_mul_rankLoss eta0 c i).symm hlambda hb
    hJ hm6 hscale (sub_nonneg.mpr extremalExponent_le_three)
    (by linarith only [extremalExponent_nonneg] : 3-extremalExponent ≤ 3)
  have hrho : (0:ℝ)<64/((2^m:ℕ):ℝ) := by positivity
  have hrho1 : (64:ℝ)/((2^m:ℕ):ℝ) ≤ 1 := by
    rw [parent_scale_dyadic_span m hm6]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have Hpaid := sourceCutoff_pays epsilon c g he hc delta hd hsmall
    (64/((2^m:ℕ):ℝ)) r (cutoff c i) hrho (cutoff_bounds hc hc1 i).2.2 hrdelta hscale
  have hexp : 42*rankLoss eta0 c i+3/(J:ℝ) ≤ epsilon/2 := by
    linarith only [hle.trans heSmall,hJloss]
  exact Hbound.trans (absorb_remaining_power g hrho hrho1 Hpaid hexp)

end NativeReferenceSliceBudgetFinal
