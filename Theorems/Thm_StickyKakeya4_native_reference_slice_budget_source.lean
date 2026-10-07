import Theorems.Thm_StickyKakeya4_native_reference_slice_budget_powers

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeReferenceSliceBudgetSource
open NativeReferenceSliceBudgetAlgebra NativeReferenceSliceBudgetCosts NativeReferenceSliceBudgetPowers
open NativeReferenceColumnExponents NativeHorizontalMenuScaleCost NativeSquaredGrainQueries

/-- The explicit AD constant with the actual source-derived profile values. -/
def actualConstant (delta eta zeta lambda b F G Q tau seed c2 w : ℝ) (J m : ℕ) (s : ℝ) : ℝ :=
  let mu := population delta eta lambda b F G
  let eps := columnEpsilon delta lambda (seed/8) c2
  let L := lowerCountCoefficient delta zeta mu (profileUpper delta eps tau)
  let U := upperCountCoefficient delta zeta (profileLower delta mu eps tau (seed/8) w)
  let B : ℝ := max 8 (((2^((phaseDepth m-m)/J+1):ℕ):ℝ))
  NativeSliceADConstant.constant (L/(Q^4*U)) (Q^4*U/L) B s

/-- Pay the actual reference AD constant directly from both raw source
costs, exact rank retention, actual history mass, and squared-grain geometry.
There is no target profile-bound or AD-constant certificate among the inputs. -/
theorem actual_reference_constant_bound {delta eta zeta lambda b tau seed t c2 w r a rankLoss s : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta)
    (F1 F2 G Q1 Q2 g ell J m : ℕ)
    (hF1 : 0 < F1) (hG : 0 < G) (hQ1 : 1 ≤ Q1) (hQ2 : 0 < Q2) (hGF : G ≤ F2)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta) ≤ delta^(-c2))
    (ht : 0 ≤ t) (htau : tau ≤ t/1024) (hseed : seed ≤ tau/16384)
    (hzeta : zeta ≤ seed/256) (hc2 : c2=t/4) (hw : w ≤ tau/16000)
    (hr : 0 < r) (hr1 : r ≤ 1) (hloss : 0 ≤ rankLoss) (hloss1 : rankLoss ≤ 1)
    (hell : ell ≤ 3) (hrdelta : r ≤ delta^a) (hteq : t=a*rankLoss)
    (hlambda : lambda=r^rankLoss/(4*((g:ℝ)+1)))
    (hb : r^((2*(ell:ℝ)+1)*rankLoss) ≤ b)
    (hJ : 0 < J) (hm6 : 6 ≤ m)
    (hscale : ((64:ℝ)/((2^m:ℕ):ℝ))^2 ≤ 6144*r) (hs : 0 ≤ s) (hs3 : s ≤ 3) :
    actualConstant delta eta zeta lambda b F1 G Q2 tau seed c2 w J m s ≤
      sourceConstant g*((64:ℝ)/((2^m:ℕ):ℝ))^(-(42*rankLoss+3/(J:ℝ))) := by
  let rho : ℝ := 64/((2^m:ℕ):ℝ)
  let mu := population delta eta lambda b F1 G
  let eps := columnEpsilon delta lambda (seed/8) c2
  let L := lowerCountCoefficient delta zeta mu (profileUpper delta eps tau)
  let U := upperCountCoefficient delta zeta (profileLower delta mu eps tau (seed/8) w)
  let B : ℝ := max 8 (((2^((phaseDepth m-m)/J+1):ℕ):ℝ))
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    dsimp [rho]
    rw [parent_scale_dyadic_span m hm6]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hlambdapos : 0 < lambda := by rw [hlambda]; positivity
  have hbpos : 0 < b := (Real.rpow_pos_of_pos hr _).trans_le hb
  have hF1r : (0:ℝ)<F1 := by exact_mod_cast hF1
  have hGr : (0:ℝ)<G := by exact_mod_cast hG
  have hQ2r : (0:ℝ)<Q2 := by exact_mod_cast hQ2
  have hmu : 0 < mu := by dsimp [mu,population]; positivity
  have heps : 0 < eps := by dsimp [eps,columnEpsilon]; positivity
  have hCmp := NativeAnisotropicGlobalSourceBridge.comparisonCost_pos
  have hRow := NativeActivePhasePopulation.rowConstant_pos
  have hPL : 0 < profileLower delta mu eps tau (seed/8) w := by unfold profileLower; positivity
  have hPU : 0 < profileUpper delta eps tau := by unfold profileUpper; positivity
  obtain ⟨hL,hU⟩ := count_coefficients_pos (zeta:=zeta) hd hmu hPL hPU
  have hB : 0 < B := lt_of_lt_of_le (by norm_num : (0:ℝ)<8) (le_max_left _ _)
  have hC := ratioConstant_pos
  have hraw := pay_source_costs (zeta:=zeta) (tau:=tau) (w:=w) hd hd1 heta hlambdapos hbpos
    F1 F2 G Q1 Q2 hF1 hG hQ1 hGF H1 H2 ht htau hseed hzeta hc2 hw
  have hrank := rank_history_power g ell hd hr hr1 hloss hell hrdelta hteq hlambda hb
  have hgrain := squared_grain_power hr hrho hloss hloss1 hscale
  have hratio : (Q2:ℝ)^4*(U/L) ≤
      (ratioConstant*(4*((g:ℝ)+1))^4*(6144:ℝ)^21)*rho^(-(42*rankLoss)) := by
    calc
      _ ≤ ratioConstant*delta^(-(3*t))/(lambda^4*b^2) := hraw
      _ = ratioConstant*(delta^(-(3*t))/(lambda^4*b^2)) := by ring
      _ ≤ ratioConstant*((4*((g:ℝ)+1))^4*r^(-(21*rankLoss))) :=
        mul_le_mul_of_nonneg_left hrank hC.le
      _ ≤ ratioConstant*((4*((g:ℝ)+1))^4*((6144:ℝ)^21*rho^(-(42*rankLoss)))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgrain (by positivity)) hC.le
      _ = _ := by ring
  have hBcost : B^s ≤ 512*rho^(-(3/(J:ℝ))) := intrinsic_gap_power_cost J m hJ hm6 s hs hs3
  have hprod : 729*((Q2:ℝ)^4*(U/L))*B^s ≤
      sourceConstant g*rho^(-(42*rankLoss+3/(J:ℝ))) := by
    calc
      _ ≤ 729*((ratioConstant*(4*((g:ℝ)+1))^4*(6144:ℝ)^21)*rho^(-(42*rankLoss)))*
          (512*rho^(-(3/(J:ℝ)))) := by gcongr
      _ = (729*512*ratioConstant*(4*((g:ℝ)+1))^4*(6144:ℝ)^21)*
          (rho^(-(42*rankLoss))*rho^(-(3/(J:ℝ)))) := by ring
      _ = (729*512*ratioConstant*(4*((g:ℝ)+1))^4*(6144:ℝ)^21)*
          rho^(-(42*rankLoss+3/(J:ℝ))) := by rw [←Real.rpow_add hrho]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hpower : 1 ≤ rho^(-(42*rankLoss+3/(J:ℝ))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrho hrho1 (neg_nonpos.mpr (by positivity))
  change NativeSliceADConstant.constant (L/((Q2:ℝ)^4*U)) (((Q2:ℝ)^4*U)/L) B s ≤ _
  rw [reference_ad_constant_eq hL hU hQ2r hB]
  exact max_le (by
    have hh := sourceConstant_one_le g
    nlinarith only [hh,hpower]) hprod

end NativeReferenceSliceBudgetSource
