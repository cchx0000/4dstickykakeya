import Theorems.Thm_StickyKakeya4_native_reference_slice_budget_algebra
import Theorems.Thm_StickyKakeya4_native_two_stage_transversality_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeReferenceSliceBudgetCosts
open NativeReferenceSliceBudgetAlgebra NativeReferenceColumnExponents

lemma first_retention_density_cost {delta eta cost : ℝ} (hd : 0 < delta)
    (F Q : ℕ) (hQ : 1 ≤ Q)
    (H : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) ≤ delta^(-cost)) :
    (F:ℝ)*delta^(-eta) ≤ delta^(-cost) := by
  have hQr : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hfac : (1:ℝ) ≤ (125*175616*16384:ℝ)*(Q:ℝ)^2 := by nlinarith only [hQr]
  calc
    _ ≤ ((125*175616*16384:ℝ)*(Q:ℝ)^2)*((F:ℝ)*delta^(-eta)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac
        (show 0 ≤ (F:ℝ)*delta^(-eta) by positivity)
    _ = (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) := by ring
    _ ≤ _ := H

/-- The first raw cost pays both original eta factors; the second pays
the full G²Q2⁴ factor. No independent retention or radix bound is assumed. -/
theorem pay_actual_costs {delta eta zeta lambda b tau c1 c2 w : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta)
    (hlambda : 0 < lambda) (hb : 0 < b)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-c1))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta) ≤ delta^(-c2)) :
    (Q2:ℝ)^4*(upperCountCoefficient delta zeta
        (profileLower delta (population delta eta lambda b F1 G)
          (columnEpsilon delta lambda c1 c2) tau c1 w)/
      lowerCountCoefficient delta zeta (population delta eta lambda b F1 G)
        (profileUpper delta (columnEpsilon delta lambda c1 c2) tau)) ≤
      ratioConstant*delta^(-(4*zeta+4*tau+5*c1+8*c2+10*w))/(lambda^4*b^2) := by
  have hF1r : (0:ℝ)<F1 := by exact_mod_cast hF1
  have hGr : (0:ℝ)<G := by exact_mod_cast hG
  rw [actual_reference_ratio hd hlambda hb hF1r hGr]
  have hf := first_retention_density_cost hd F1 Q1 hQ1 H1
  have hg := NativeTwoStageTransversalityBudget.retention_radix_le_of_transfer_cost
    hd hd1 heta F2 Q2 (G:ℝ) (Nat.cast_le.mpr hGF) H2
  have hf0 : 0 ≤ (F1:ℝ)*delta^(-eta) := by positivity
  have hg0 : 0 ≤ (G:ℝ)*(Q2:ℝ)^2 := by positivity
  have hcost : ((F1:ℝ)*delta^(-eta))^2*((G:ℝ)*(Q2:ℝ)^2)^2 ≤ delta^(-(2*c1+2*c2)) := by
    calc
      _ ≤ (delta^(-c1))^2*(delta^(-c2))^2 := by
        exact mul_le_mul (pow_le_pow_left₀ hf0 hf 2) (pow_le_pow_left₀ hg0 hg 2) (by positivity) (by positivity)
      _ = _ := by
        rw [←Real.rpow_natCast,←Real.rpow_natCast,←Real.rpow_mul hd.le,←Real.rpow_mul hd.le,
          ←Real.rpow_add hd]
        congr 1
        ring
  have hC := ratioConstant_pos
  calc
    _ = ratioConstant*(((F1:ℝ)*delta^(-eta))^2*((G:ℝ)*(Q2:ℝ)^2)^2)*
        delta^(-(4*zeta+4*tau+3*c1+6*c2+10*w))/(lambda^4*b^2) := by ring
    _ ≤ ratioConstant*delta^(-(2*c1+2*c2))*
        delta^(-(4*zeta+4*tau+3*c1+6*c2+10*w))/(lambda^4*b^2) := by gcongr
    _ = _ := by
      rw [mul_assoc ratioConstant,←Real.rpow_add hd]
      congr 2
      ring

lemma source_exponent_le {t tau seed zeta c2 w : ℝ}
    (ht : 0 ≤ t) (htau : tau ≤ t/1024) (hseed : seed ≤ tau/16384)
    (hzeta : zeta ≤ seed/256) (hc2 : c2=t/4) (hw : w ≤ tau/16000) :
    4*zeta+4*tau+5*(seed/8)+8*c2+10*w ≤ 3*t := by
  rw [hc2]
  linarith only [ht,htau,hseed,hzeta,hw]

theorem pay_source_costs {delta eta zeta lambda b tau seed t c2 w : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta)
    (hlambda : 0 < lambda) (hb : 0 < b)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta) ≤ delta^(-c2))
    (ht : 0 ≤ t) (htau : tau ≤ t/1024) (hseed : seed ≤ tau/16384)
    (hzeta : zeta ≤ seed/256) (hc2 : c2=t/4) (hw : w ≤ tau/16000) :
    (Q2:ℝ)^4*(upperCountCoefficient delta zeta
        (profileLower delta (population delta eta lambda b F1 G)
          (columnEpsilon delta lambda (seed/8) c2) tau (seed/8) w)/
      lowerCountCoefficient delta zeta (population delta eta lambda b F1 G)
        (profileUpper delta (columnEpsilon delta lambda (seed/8) c2) tau)) ≤
      ratioConstant*delta^(-(3*t))/(lambda^4*b^2) := by
  have hh := pay_actual_costs (zeta:=zeta) (tau:=tau) (w:=w)
    hd hd1 heta hlambda hb F1 F2 G Q1 Q2 hF1 hG hQ1 hGF H1 H2
  have hpow := Real.rpow_le_rpow_of_exponent_ge hd hd1
    (neg_le_neg (source_exponent_le ht htau hseed hzeta hc2 hw))
  have hC := ratioConstant_pos
  exact hh.trans (by gcongr)

end NativeReferenceSliceBudgetCosts
