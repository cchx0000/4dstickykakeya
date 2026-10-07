import Theorems.Thm_StickyKakeya4_native_retained_slice_budget_costs

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeRetainedSliceBudgetExtra
open NativeRetainedSliceBudgetAlgebra NativeRetainedSliceBudgetCosts NativeReferenceSliceBudgetAlgebra
open NativeActivePhasePopulation NativeParentHeightGraphCore

def extraCoefficient (delta eta lambda b F G F3 Q3 q : ℝ) (K : ℕ) : ℝ :=
  (selectionCost K:ℝ)*quotientCost q*F3*Q3^4/(population delta eta lambda b F G/rowConstant)

def extraConstant (g K : ℕ) : ℝ :=
  max 1 (8*rowConstant*(selectionCost K:ℝ)*((g:ℝ)+1)*(32768*(32002:ℝ)^4)*(6144:ℝ)^10)

lemma extraConstant_one_le (g K : ℕ) : 1 ≤ extraConstant g K := le_max_left _ _

lemma graphCost_pos (K : ℕ) : (0:ℝ)<selectionCost K := by
  unfold selectionCost NativeProjectorCellChart.chartCount
  positivity

lemma squared_loss {r rho loss : ℝ} (hrho : 0 < rho) (hloss : 0 ≤ loss) (hloss10 : loss ≤ 10)
    (hscale : rho^2 ≤ 6144*r) : r^(-loss) ≤ (6144:ℝ)^10*rho^(-(2*loss)) := by
  have hratio : rho^2/6144 ≤ r := by linarith only [hscale]
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ)<rho^2/6144)
    hratio (neg_nonpos.mpr hloss)
  have heq : (rho^2/6144)^(-loss)=(6144:ℝ)^loss*rho^(-(2*loss)) := by
    rw [Real.div_rpow (sq_nonneg rho) (by norm_num),←Real.rpow_natCast,
      ←Real.rpow_mul hrho.le,Real.rpow_neg (by norm_num : (0:ℝ)≤6144),div_inv_eq_mul]
    norm_num only [Nat.cast_ofNat]
    have he : (2:ℝ)*(-loss)=-(2*loss) := by ring
    rw [he,mul_comm]
  rw [heq] at hp
  have h6144 : (6144:ℝ)^loss ≤ (6144:ℝ)^10 := by
    rw [←Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simpa only [Nat.cast_ofNat] using hloss10
  exact hp.trans (mul_le_mul_of_nonneg_right h6144 (by positivity))

/-- Actual graph selection, actual quotient ceiling, and the actual third
core are all retained in this bound. Only the raw costs and rank/history
facts are used to pay them. -/
theorem extra_coefficient_bound {delta eta lambda b tau seed t c2 r a rankLoss rho q epsilonQ : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta)
    (F1 F2 G Q1 Q2 F3 Q3 g ell K : ℕ) (hF1 : 0 < F1) (hG : 0 < G)
    (hQ1 : 1 ≤ Q1) (hQ2 : 1 ≤ Q2) (hGF : G ≤ F2)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta) ≤ delta^(-c2))
    (H3 : (F3:ℝ)*(Q3:ℝ)^4 ≤ delta^(-(t/4)))
    (ht : 0 ≤ t) (htau : tau ≤ t/1024) (hseed : seed ≤ tau/16384) (hc2 : c2=t/4)
    (hr : 0 < r) (hr1 : r ≤ 1) (hloss : 0 ≤ rankLoss) (hloss1 : rankLoss ≤ 1)
    (hell : ell ≤ 3) (hrdelta : r ≤ delta^a) (hteq : t=a*rankLoss)
    (hlambda : lambda=r^rankLoss/(4*((g:ℝ)+1)))
    (hb : r^((2*(ell:ℝ)+1)*rankLoss) ≤ b)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hscale : rho^2 ≤ 6144*r)
    (hq : 0 < q) (hq1 : q ≤ 1) (heQ : 0 ≤ epsilonQ) (heQ1 : epsilonQ ≤ 1)
    (hqlow : r^(epsilonQ/6)/2 ≤ q) :
    max 1 (extraCoefficient delta eta lambda b F1 G F3 Q3 q K) ≤
      extraConstant g K*rho^(-(18*rankLoss+4*epsilonQ/3)) := by
  have hlambdapos : 0 < lambda := by rw [hlambda]; positivity
  have hbpos : 0 < b := (Real.rpow_pos_of_pos hr _).trans_le hb
  have hparent := third_core_parent_cost hd hd1 heta hlambdapos hbpos
    F1 F2 G Q1 Q2 F3 Q3 hF1 hG hQ1 hQ2 hGF H1 H2 H3 ht htau hseed hc2
  have hrank := rank_parent_retention_power g ell hd hr hr1 hloss hell hrdelta hteq hlambda hb
  have hquot := quotientCost_le hr hq hq1 hqlow
  have hRow := rowConstant_pos
  have hGraph := graphCost_pos K
  have hQuot := quotientCost_pos hq
  have hbase : extraCoefficient delta eta lambda b F1 G F3 Q3 q K ≤
      (8*rowConstant*(selectionCost K:ℝ)*((g:ℝ)+1)*(32768*(32002:ℝ)^4))*
        r^(-(9*rankLoss+2*epsilonQ/3)) := by
    calc
      _ = ((selectionCost K:ℝ)*quotientCost q)*
          (((F3:ℝ)*(Q3:ℝ)^4)/(population delta eta lambda b F1 G/rowConstant)) := by
        unfold extraCoefficient
        ring
      _ ≤ ((selectionCost K:ℝ)*quotientCost q)*((2*rowConstant)*delta^(-t)/(lambda*b)) := by gcongr
      _ = (2*rowConstant*(selectionCost K:ℝ)*quotientCost q)*(delta^(-t)/(lambda*b)) := by ring
      _ ≤ (2*rowConstant*(selectionCost K:ℝ)*quotientCost q)*
          ((4*((g:ℝ)+1))*r^(-(9*rankLoss))) := by gcongr
      _ ≤ (2*rowConstant*(selectionCost K:ℝ)*((32768*(32002:ℝ)^4)*r^(-(2*epsilonQ/3))))*
          ((4*((g:ℝ)+1))*r^(-(9*rankLoss))) := by gcongr
      _ = (8*rowConstant*(selectionCost K:ℝ)*((g:ℝ)+1)*(32768*(32002:ℝ)^4))*
          (r^(-(9*rankLoss))*r^(-(2*epsilonQ/3))) := by ring
      _ = _ := by rw [←Real.rpow_add hr]; congr 2; ring
  have hscalar := squared_loss hrho (show 0 ≤ 9*rankLoss+2*epsilonQ/3 by positivity)
    (show 9*rankLoss+2*epsilonQ/3 ≤ 10 by linarith only [hloss1,heQ1]) hscale
  have hexp : 2*(9*rankLoss+2*epsilonQ/3)=18*rankLoss+4*epsilonQ/3 := by ring
  rw [hexp] at hscalar
  have hbound : extraCoefficient delta eta lambda b F1 G F3 Q3 q K ≤
      extraConstant g K*rho^(-(18*rankLoss+4*epsilonQ/3)) := hbase.trans (calc
    _ ≤ (8*rowConstant*(selectionCost K:ℝ)*((g:ℝ)+1)*(32768*(32002:ℝ)^4))*
        ((6144:ℝ)^10*rho^(-(18*rankLoss+4*epsilonQ/3))) := by gcongr
    _ = (8*rowConstant*(selectionCost K:ℝ)*((g:ℝ)+1)*(32768*(32002:ℝ)^4)*(6144:ℝ)^10)*
        rho^(-(18*rankLoss+4*epsilonQ/3)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hp : 1 ≤ rho^(-(18*rankLoss+4*epsilonQ/3)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrho hrho1 (neg_nonpos.mpr (by positivity))
  exact max_le (by have hc := extraConstant_one_le g K; nlinarith only [hc,hp]) hbound

end NativeRetainedSliceBudgetExtra
