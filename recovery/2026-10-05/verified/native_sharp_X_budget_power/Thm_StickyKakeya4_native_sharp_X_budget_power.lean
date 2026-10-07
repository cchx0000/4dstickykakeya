import Theorems.Thm_StickyKakeya4_native_sharp_X_budget_costs

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeSharpXBudgetPower
open NativeSharpXBudgetCosts NativeSharpXPowerAlgebra NativeRetainedSliceBudgetAlgebra
open NativeSourceParentGrainCleanup NativeActualProjectedGrainCount NativeActualRichPacketLayers

/-- Fixed losses only: the source-dependent radius is excluded. -/
def baseConstant (g : ℕ) : ℝ := parentGrainConstant*(6*(referenceConstant:ℝ))^3*
  (2*(41*(256*258):ℝ))^12*(32768*(32002:ℝ)^4)*(4*((g:ℝ)+1))^4

def sourceConstant (g : ℕ) : ℝ := max 1 (baseConstant g*(6144:ℝ)^40)

lemma baseConstant_nonneg (g : ℕ) : 0 ≤ baseConstant g := by
  have hC := NativeParentVertexMassCap.parentCapConstant_pos
  unfold baseConstant parentGrainConstant
  positivity

lemma sourceConstant_one_le (g : ℕ) : 1 ≤ sourceConstant g := le_max_left _ _

/-- Pay all source-dependent terms after cap cancellation by the actual
rank fraction and the actual quantitative test-radius lower. -/
theorem fiber_coefficient_rank_bound {delta eta zeta tau seed t c2 r a loss lambda b q epsilonQ : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta) (hetaSeed : eta ≤ seed/8)
    (hseed0 : 0 ≤ seed) (ht : 0 ≤ t) (htau : tau ≤ t/1024) (hseed : seed ≤ tau/16384)
    (hzeta : zeta ≤ seed/256) (hc2 : c2=t/4)
    (F1 F2 G Q1 Q2 F3 Q3 g ell : ℕ) (hQ1 : 1 ≤ Q1) (hQ3 : 1 ≤ Q3) (hGF : G ≤ F2) (hell : ell ≤ 3)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta) ≤ delta^(-c2))
    (H3 : (F3:ℝ)*(Q3:ℝ)^4 ≤ delta^(-(t/4)))
    (hr : 0 < r) (hr1 : r ≤ 1) (hloss : 0 ≤ loss) (hrdelta : r ≤ delta^a) (hteq : t=a*loss)
    (hlambda : lambda=r^loss/(4*((g:ℝ)+1))) (hb : r^((2*(ell:ℝ)+1)*loss) ≤ b)
    (hq : 0 < q) (hq1 : q ≤ 1) (hqlo : r^(epsilonQ/6)/2 ≤ q) :
    fiberCoefficient delta eta zeta tau (seed/8) c2 lambda b F1 G Q2 F3 Q3 q ell ≤
      baseConstant g*r^(-(37*loss+8*epsilonQ/3)) := by
  have hraw := raw_cost_power hd hd1 heta hetaSeed hseed0 ht htau hseed hzeta hc2
    F1 F2 G Q1 Q2 F3 Q3 ell hQ1 hQ3 hGF hell H1 H2 H3
  have hdelta : delta^(-(5*t)) ≤ r^(-(5*loss)) := by
    have hh := Real.rpow_le_rpow_of_nonpos hr hrdelta (neg_nonpos.mpr (show 0 ≤ 5*loss by positivity))
    rw [←Real.rpow_mul hd.le] at hh
    convert hh using 1
    rw [hteq]
    congr 1
    ring
  have hrawr := hraw.trans hdelta
  have hlambdapos : 0 < lambda := by rw [hlambda]; positivity
  have hbpos : 0 < b := (Real.rpow_pos_of_pos hr _).trans_le hb
  have hden := rank_denominator g ell hr hr1 hloss hell hlambda hb
  have htrans := transverse_power ell hr hq hq1 hell hqlo
  have hquot := quotientCost_le hr hq hq1 hqlo
  have href := reference_factor ell hell
  have hC : 0 ≤ parentGrainConstant := by
    have hh := NativeParentVertexMassCap.parentCapConstant_pos
    unfold parentGrainConstant
    positivity
  have hQ := quotientCost_pos hq
  have hD := transverseCost_pos hq ell
  unfold fiberCoefficient
  calc
    _ = (parentGrainConstant*(2*(ell:ℝ)*(referenceConstant:ℝ))^ell*transverseCost q ell*quotientCost q)*
        ((F1:ℝ)*G*(Q2:ℝ)^2*F3*(Q3:ℝ)^2*
          delta^(-(2*eta+3*zeta+7*tau+(ell:ℝ)*(seed/8+5*c2))))*(1/(lambda*b)^(ell+1)) := by ring
    _ ≤ (parentGrainConstant*(6*(referenceConstant:ℝ))^3*
        ((2*(41*(256*258):ℝ))^12*r^(-(2*epsilonQ)))*
        ((32768*(32002:ℝ)^4)*r^(-(2*epsilonQ/3))))*
        r^(-(5*loss))*((4*((g:ℝ)+1))^4*r^(-(32*loss))) := by gcongr
    _ = baseConstant g*(r^(-(2*epsilonQ))*r^(-(2*epsilonQ/3))*r^(-(5*loss))*r^(-(32*loss))) := by
      unfold baseConstant
      ring
    _ = _ := by
      rw [←Real.rpow_add hr,←Real.rpow_add hr,←Real.rpow_add hr]
      congr 2
      ring

lemma squared_scale_power {rho r exponent : ℝ} (hrho : 0 < rho)
    (he : 0 ≤ exponent) (he40 : exponent ≤ 40) (hscale : rho^2 ≤ 6144*r) :
    r^(-exponent) ≤ (6144:ℝ)^40*rho^(-(2*exponent)) := by
  have hratio : rho^2/6144 ≤ r := by linarith only [hscale]
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ)<rho^2/6144)
    hratio (neg_nonpos.mpr he)
  have heq : (rho^2/6144)^(-exponent)=(6144:ℝ)^exponent*rho^(-(2*exponent)) := by
    rw [Real.div_rpow (sq_nonneg rho) (by norm_num),←Real.rpow_natCast,
      ←Real.rpow_mul hrho.le,Real.rpow_neg (by norm_num : (0:ℝ)≤6144),div_inv_eq_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(-exponent)=-(2*exponent) by ring,mul_comm]
  rw [heq] at hp
  have h6144 : (6144:ℝ)^exponent ≤ (6144:ℝ)^40 := by
    rw [←Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simpa only [Nat.cast_ofNat] using he40
  exact hp.trans (mul_le_mul_of_nonneg_right h6144 (by positivity))

/-- Convert only the actual middle squared-scale identity, with its fixed
6144 constant, into the desired Delta exponent. -/
lemma rank_bound_to_scale {C rho r loss epsilonQ : ℝ} (g : ℕ)
    (hrho : 0 < rho) (hloss : 0 ≤ loss) (hloss1 : loss ≤ 1)
    (heQ : 0 ≤ epsilonQ) (heQ1 : epsilonQ ≤ 1) (hscale : rho^2 ≤ 6144*r)
    (H : C ≤ baseConstant g*r^(-(37*loss+8*epsilonQ/3))) :
    C ≤ sourceConstant g*rho^(-(74*loss+16*epsilonQ/3)) := by
  have hh := squared_scale_power hrho
    (show 0 ≤ 37*loss+8*epsilonQ/3 by positivity)
    (show 37*loss+8*epsilonQ/3 ≤ 40 by linarith only [hloss1,heQ1]) hscale
  have he : 2*(37*loss+8*epsilonQ/3)=74*loss+16*epsilonQ/3 := by ring
  rw [he] at hh
  exact H.trans (calc
    _ ≤ baseConstant g*((6144:ℝ)^40*rho^(-(74*loss+16*epsilonQ/3))) :=
      mul_le_mul_of_nonneg_left hh (baseConstant_nonneg g)
    _ = (baseConstant g*(6144:ℝ)^40)*rho^(-(74*loss+16*epsilonQ/3)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end NativeSharpXBudgetPower
