import Theorems.Thm_StickyKakeya4_native_sharp_X_power_algebra
import Theorems.Thm_StickyKakeya4_native_retained_slice_budget_final

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeSharpXBudgetCosts
open NativeSharpXPowerAlgebra NativeReferenceSliceBudgetCosts NativeRetainedSliceBudgetAlgebra
open NativeSourceParentGrainCleanup NativeActualProjectedGrainCount NativeActualRichPacketLayers

lemma raw_cost_power {delta eta zeta tau seed t c2 : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta) (hetaSeed : eta ≤ seed/8)
    (hseed0 : 0 ≤ seed) (ht : 0 ≤ t) (htau : tau ≤ t/1024) (hseed : seed ≤ tau/16384)
    (hzeta : zeta ≤ seed/256) (hc2 : c2=t/4)
    (F1 F2 G Q1 Q2 F3 Q3 ell : ℕ) (hQ1 : 1 ≤ Q1) (hQ3 : 1 ≤ Q3) (hGF : G ≤ F2) (hell : ell ≤ 3)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta) ≤ delta^(-c2))
    (H3 : (F3:ℝ)*(Q3:ℝ)^4 ≤ delta^(-(t/4))) :
    (F1:ℝ)*G*(Q2:ℝ)^2*F3*(Q3:ℝ)^2*
      delta^(-(2*eta+3*zeta+7*tau+(ell:ℝ)*(seed/8+5*c2))) ≤ delta^(-(5*t)) := by
  have hf := first_retention_density_cost hd F1 Q1 hQ1 H1
  have hg := NativeTwoStageTransversalityBudget.retention_radix_le_of_transfer_cost
    hd hd1 heta F2 Q2 (G:ℝ) (Nat.cast_le.mpr hGF) H2
  have hQ3r : (1:ℝ) ≤ Q3 := by exact_mod_cast hQ3
  have hthird : (F3:ℝ)*(Q3:ℝ)^2 ≤ delta^(-(t/4)) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hQ3r (by norm_num : 2 ≤ 4)) (Nat.cast_nonneg F3)).trans H3
  have hellr : (ell:ℝ) ≤ 3 := by exact_mod_cast hell
  have hgamma : 0 ≤ seed/8+5*c2 := by rw [hc2]; positivity
  have hprod := mul_le_mul_of_nonneg_right hellr hgamma
  have hexp : seed/8+c2+t/4+eta+3*zeta+7*tau+(ell:ℝ)*(seed/8+5*c2) ≤ 5*t := by
    rw [hc2] at hprod ⊢
    linarith only [hprod,ht,htau,hseed,hzeta,hetaSeed]
  have hpow : delta^(-eta)*delta^(-(eta+3*zeta+7*tau+(ell:ℝ)*(seed/8+5*c2)))=
      delta^(-(2*eta+3*zeta+7*tau+(ell:ℝ)*(seed/8+5*c2))) := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  calc
    _ = ((F1:ℝ)*delta^(-eta))*((G:ℝ)*(Q2:ℝ)^2)*((F3:ℝ)*(Q3:ℝ)^2)*
        delta^(-(eta+3*zeta+7*tau+(ell:ℝ)*(seed/8+5*c2))) := by rw [←hpow]; ring
    _ ≤ delta^(-(seed/8))*delta^(-c2)*delta^(-(t/4))*
        delta^(-(eta+3*zeta+7*tau+(ell:ℝ)*(seed/8+5*c2))) := by gcongr
    _ = delta^(-(seed/8+c2+t/4+eta+3*zeta+7*tau+(ell:ℝ)*(seed/8+5*c2))) := by
      rw [←Real.rpow_add hd,←Real.rpow_add hd,←Real.rpow_add hd]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hexp)

lemma rank_denominator {r lambda b loss : ℝ} (g ell : ℕ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hloss : 0 ≤ loss) (hell : ell ≤ 3)
    (hlambda : lambda=r^loss/(4*((g:ℝ)+1)))
    (hb : r^((2*(ell:ℝ)+1)*loss) ≤ b) :
    1/(lambda*b)^(ell+1) ≤ (4*((g:ℝ)+1))^4*r^(-(32*loss)) := by
  have hellr : (ell:ℝ) ≤ 3 := by exact_mod_cast hell
  have hbpos : 0 < b := (Real.rpow_pos_of_pos hr _).trans_le hb
  have hlambdapos : 0 < lambda := by rw [hlambda]; positivity
  have hbr : r^(7*loss) ≤ b :=
    (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by nlinarith only [hellr,hloss])).trans hb
  have hden : r^(8*loss)/(4*((g:ℝ)+1)) ≤ lambda*b := by
    calc
      _ = (r^loss/(4*((g:ℝ)+1)))*r^(7*loss) := by
        rw [div_mul_eq_mul_div,←Real.rpow_add hr]
        congr 2
        ring
      _ ≤ _ := by rw [←hlambda]; exact mul_le_mul_of_nonneg_left hbr hlambdapos.le
  have hinv : 1/(lambda*b) ≤ (4*((g:ℝ)+1))*r^(-(8*loss)) := by
    calc
      _ ≤ 1/(r^(8*loss)/(4*((g:ℝ)+1))) := one_div_le_one_div_of_le (by positivity) hden
      _ = _ := by rw [Real.rpow_neg hr.le]; field_simp
  have hrpow : 1 ≤ r^(-(8*loss)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (neg_nonpos.mpr (by positivity))
  have hbase : 1 ≤ (4*((g:ℝ)+1))*r^(-(8*loss)) := by
    have hg : (0:ℝ) ≤ g := Nat.cast_nonneg _
    nlinarith only [hrpow,hg]
  calc
    _ = (1/(lambda*b))^(ell+1) := by rw [div_pow,one_pow]
    _ ≤ ((4*((g:ℝ)+1))*r^(-(8*loss)))^(ell+1) := pow_le_pow_left₀ (by positivity) hinv _
    _ ≤ ((4*((g:ℝ)+1))*r^(-(8*loss)))^4 := pow_le_pow_right₀ hbase (by omega)
    _ = _ := by
      rw [mul_pow,←Real.rpow_natCast (r^(-(8*loss))),←Real.rpow_mul hr.le]
      congr 2
      norm_num
      ring

lemma transverse_power {r q epsilonQ : ℝ} (ell : ℕ)
    (hr : 0 < r) (hq : 0 < q) (hq1 : q ≤ 1) (hell : ell ≤ 3)
    (hqlo : r^(epsilonQ/6)/2 ≤ q) :
    transverseCost q ell ≤ (2*(41*(256*258):ℝ))^12*r^(-(2*epsilonQ)) := by
  have hbase : 1 ≤ ((41*(256*258):ℝ)/q)^4 := by
    apply one_le_pow₀
    apply (le_div_iff₀ hq).mpr
    linarith only [hq1]
  have hratio : (41*(256*258):ℝ)/q ≤ (2*(41*(256*258):ℝ))/r^(epsilonQ/6) := by
    apply (div_le_div_iff₀ hq (Real.rpow_pos_of_pos hr _)).mpr
    nlinarith only [hqlo]
  unfold transverseCost
  calc
    _ ≤ (((41*(256*258):ℝ)/q)^4)^3 := pow_le_pow_right₀ hbase hell
    _ = ((41*(256*258):ℝ)/q)^12 := by rw [←pow_mul]
    _ ≤ ((2*(41*(256*258):ℝ))/r^(epsilonQ/6))^12 := pow_le_pow_left₀ (by positivity) hratio _
    _ = _ := by
      rw [div_pow,←Real.rpow_natCast (r^(epsilonQ/6)),←Real.rpow_mul hr.le]
      norm_num only [Nat.cast_ofNat]
      rw [show epsilonQ/6*12=2*epsilonQ by ring,Real.rpow_neg hr.le]
      ring

lemma reference_factor (ell : ℕ) (hell : ell ≤ 3) :
    (2*(ell:ℝ)*(referenceConstant:ℝ))^ell ≤ (6*(referenceConstant:ℝ))^3 := by
  have hellr : (ell:ℝ) ≤ 3 := by exact_mod_cast hell
  have href : (1:ℝ) ≤ referenceConstant := by exact_mod_cast referenceConstant_pos
  have hbase : 1 ≤ 6*(referenceConstant:ℝ) := by linarith only [href]
  exact (pow_le_pow_left₀ (by positivity) (by nlinarith only [hellr,href]) ell).trans
    (pow_le_pow_right₀ hbase hell)

end NativeSharpXBudgetCosts
