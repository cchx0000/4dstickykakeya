import Theorems.Thm_StickyKakeya4_native_retained_slice_budget_costs

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7500000

noncomputable section
namespace NativeSaturatedAngularRankBudget
open NativeReferenceSliceBudgetAlgebra NativeReferenceSliceBudgetCosts NativeActivePhasePopulation
open NativeRetainedSliceBudgetCosts

/-- H1 pays the first radix together with the original density factor;
H2 pays the second radix. The ancestor gap remains an original-delta loss. -/
theorem angular_parent_cost {delta eta lambda b tau seed t c2 gap : ℝ}
    (hd : 0< delta) (hd1 : delta≤ 1) (heta : 0≤ eta) (hlambda : 0< lambda) (hb : 0< b)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0< F1) (hG : 0< G) (hGF : G≤ F2)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta)≤ delta^(-(seed/8)))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta)≤ delta^(-c2))
    (ht : 0≤ t) (htau : tau≤ t/1024) (hseed : seed≤ tau/16384)
    (hc2 : c2=t/4) (hgap : gap≤ tau) :
    (343*(Q1:ℝ)^2*(Q2:ℝ)^2)/
      ((population delta eta lambda b F1 G/rowConstant)*delta^(2*tau+3*gap))≤ 
        (686*rowConstant)*delta^(-t)/(lambda*b) := by
  have hFirst : (F1:ℝ)*(Q1:ℝ)^2*delta^(-eta)≤ delta^(-(seed/8)) := by
    have hh := first_retention_density_cost (eta:=eta) (cost:=seed/8) hd (F1*Q1^2) 1 (by omega)
      (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_one,one_pow,mul_one,mul_assoc] using H1)
    simpa only [Nat.cast_mul,Nat.cast_pow] using hh
  have hSecond := NativeTwoStageTransversalityBudget.retention_radix_le_of_transfer_cost
    hd hd1 heta F2 Q2 (G:ℝ) (Nat.cast_le.mpr hGF) H2
  have hmargin : seed/8+c2+(2*tau+3*gap)≤ t := by
    rw [hc2]
    linarith only [ht,htau,hseed,hgap]
  have hproduct : ((F1:ℝ)*(Q1:ℝ)^2*delta^(-eta))*((G:ℝ)*(Q2:ℝ)^2)*delta^(-(2*tau+3*gap))≤ delta^(-t) := by
    calc
      _ ≤  delta^(-(seed/8))*delta^(-c2)*delta^(-(2*tau+3*gap)) := by gcongr
      _ = delta^(-(seed/8+c2+(2*tau+3*gap))) := by
        rw [←Real.rpow_add hd,←Real.rpow_add hd]
        congr 1
        ring
      _ ≤  _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hmargin)
  have hF1r : (0:ℝ)< F1 := by exact_mod_cast hF1
  have hGr : (0:ℝ)< G := by exact_mod_cast hG
  have hRow := rowConstant_pos
  calc
    _ = (686*rowConstant)*
        (((F1:ℝ)*(Q1:ℝ)^2*delta^(-eta))*((G:ℝ)*(Q2:ℝ)^2)*delta^(-(2*tau+3*gap)))/(lambda*b) := by
      unfold population
      rw [Real.rpow_neg hd.le eta,Real.rpow_neg hd.le (2*tau+3*gap)]
      field_simp
      ring
    _ ≤  _ := by gcongr

/-- Literal source rank mass and the stopping-scale identity convert the
complete point-angular cost to r^{-9 rankLoss}. No delta-loss is relabeled
as a rho-loss. -/
theorem angular_rank_cost {delta r a eta tau seed t c2 gap rankLoss lambda b : ℝ}
    (g ell : ℕ) (hd : 0< delta) (hd1 : delta≤ 1) (hr : 0< r) (hr1 : r≤ 1)
    (heta : 0≤ eta) (hloss : 0≤ rankLoss) (hell : ell≤ 3)
    (hrdelta : r≤ delta^a) (ht : t=a*rankLoss)
    (hlambda : lambda=r^rankLoss/(4*((g:ℝ)+1)))
    (hb : r^((2*(ell:ℝ)+1)*rankLoss)≤ b)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0< F1) (hG : 0< G) (hGF : G≤ F2)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta)≤ delta^(-(seed/8)))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta)≤ delta^(-c2))
    (ht0 : 0≤ t) (htau : tau≤ t/1024) (hseed : seed≤ tau/16384)
    (hc2 : c2=t/4) (hgap : gap≤ tau) :
    (343*(Q1:ℝ)^2*(Q2:ℝ)^2)/
      ((population delta eta lambda b F1 G/rowConstant)*delta^(2*tau+3*gap))≤ 
        (2744*rowConstant*((g:ℝ)+1))*r^(-(9*rankLoss)) := by
  have hbpos : 0< b := (Real.rpow_pos_of_pos hr _).trans_le hb
  have hlambdapos : 0< lambda := by rw [hlambda]; positivity
  have hcost := angular_parent_cost hd hd1 heta hlambdapos hbpos F1 F2 G Q1 Q2 hF1 hG hGF
    H1 H2 ht0 htau hseed hc2 hgap
  have hrank := rank_parent_retention_power g ell hd hr hr1 hloss hell hrdelta ht hlambda hb
  have hRow := rowConstant_pos
  have hh := mul_le_mul_of_nonneg_left hrank (show 0≤ 686*rowConstant by positivity)
  exact hcost.trans (by convert hh using 1 <;> ring)

end NativeSaturatedAngularRankBudget
