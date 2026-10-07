import Theorems.Thm_StickyKakeya4_native_actual_rank_four_count
import Theorems.Thm_StickyKakeya4_native_raw_point_rank_four_ratio
import Theorems.Thm_StickyKakeya4_native_compatible_weighted_retention

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeRankFourScalarBudget
open Classical Finset StickyKakeya4 NativeActualRankFourCount NativeRawPointRankFourRatio
open NativeMiddleWindowBalance NativeTwoStageTransversalityBudget NativeCompatibleWeightedRetention
open NativeRankExponentHierarchy NativeTwoAxisPowerInterpolation NativeAllTwoScaleConfiguration
open scoped BigOperators

/-- The two already-derived geometric constants, with no scale dependence. -/
def countConstant : ℝ := rankFourConstant*pointRatioConstant

lemma countConstant_pos : 0 < countConstant := by
  have hR : (0:ℝ) < NativeActualRichPacketLayers.referenceConstant := by
    exact_mod_cast NativeActualRichPacketLayers.referenceConstant_pos
  have hC : 0 < rankFourConstant := by unfold rankFourConstant; positivity
  exact mul_pos hC pointRatioConstant_pos

/-- The actual loss after combining the rank-four count and source profile,
and paying F1*G*Q1^4*Q2^2 from the two actual raw costs. -/
def pointLoss (eta zeta seed fine c1 c2 : ℝ) : ℝ :=
  6*c1+21*c2+2*eta+2*zeta+seed+fine

/-- Preserve every source factor until the raw-cost inequalities pay it. -/
lemma source_cost_product {delta eta1 eta2 c1 c2 : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (he1 : 0 ≤ eta1) (he2 : 0 ≤ eta2)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0 < F1) (hGF : G ≤ F2)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta1) ≤ delta^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta2) ≤ delta^(-c2)) :
    (F1:ℝ)*G*(Q1:ℝ)^4*(Q2:ℝ)^2 ≤ delta^(-(2*c1+c2)) := by
  have hFQ := retention_radix_le_of_transfer_cost hd hd1 he1 F1 Q1 (F1:ℝ) le_rfl hcost1
  have hQ := radix_sq_le_of_transfer_cost hd hd1 he1 F1 Q1 hF1 hcost1
  have hGQ := retention_radix_le_of_transfer_cost hd hd1 he2 F2 Q2 (G:ℝ)
    (by exact_mod_cast hGF) hcost2
  calc
    _ = ((F1:ℝ)*(Q1:ℝ)^2)*(Q1:ℝ)^2*((G:ℝ)*(Q2:ℝ)^2) := by ring
    _ ≤ (delta^(-c1)*delta^(-c1))*delta^(-c2) :=
      mul_le_mul (mul_le_mul hFQ hQ (by positivity) (by positivity)) hGQ
        (by positivity) (by positivity)
    _ = _ := by rw [←Real.rpow_add hd,←Real.rpow_add hd]; congr 1; ring

/-- Actual coarse and fine point counts remain visible until the same
positive coarse count cancels. No point profile, retained mass or radix is
silently replaced by a unit quantity. -/
theorem actual_count_power {delta Delta eta eta2 zeta seed fine c1 c2 kappa beta lambda q : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hDelta : 0 < Delta)
    (heta : 0 ≤ eta) (heta2 : 0 ≤ eta2) (hlambda : 0 < lambda)
    (F1 F2 G Q1 Q2 Vcoarse Vfine : ℕ) (hF1 : 0 < F1) (hGF : G ≤ F2)
    (hVc : 0 < Vcoarse)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta2) ≤ delta^(-c2))
    (hgeometry : (Vcoarse:ℝ)*beta^5*lambda^4*(delta^(c1+5*c2))^4*q^16 ≤
      rankFourConstant*(Q2:ℝ)^2*Delta^4*(Vfine:ℝ))
    (hprofile : lambda*delta^(2*eta+2*zeta+seed+fine)*Delta^4*(Vfine:ℝ) ≤
      pointRatioConstant*(F1:ℝ)*G*(Q1:ℝ)^4*Delta^kappa*(Vcoarse:ℝ)) :
    beta^5*lambda^5*q^16*delta^(pointLoss eta zeta seed fine c1 c2) ≤
      countConstant*Delta^kappa := by
  let p := 2*eta+2*zeta+seed+fine
  let s := 4*c1+20*c2+p
  have hgeomPow : (delta^(c1+5*c2))^4=delta^(4*c1+20*c2) := by
    rw [←Real.rpow_mul_natCast hd.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  have hjoin : delta^(4*c1+20*c2)*delta^p=delta^s := by
    rw [←Real.rpow_add hd]
  have hR : (0:ℝ) < NativeActualRichPacketLayers.referenceConstant := by
    exact_mod_cast NativeActualRichPacketLayers.referenceConstant_pos
  have hC4 : 0 < rankFourConstant := by unfold rankFourConstant; positivity
  have hmul : (Vcoarse:ℝ)*(beta^5*lambda^5*q^16*delta^s) ≤
      (Vcoarse:ℝ)*(countConstant*((F1:ℝ)*G*(Q1:ℝ)^4*(Q2:ℝ)^2)*Delta^kappa) := by
    calc
      _ = (lambda*delta^p)*((Vcoarse:ℝ)*beta^5*lambda^4*(delta^(c1+5*c2))^4*q^16) := by
        rw [hgeomPow,←hjoin]
        ring
      _ ≤ (lambda*delta^p)*(rankFourConstant*(Q2:ℝ)^2*Delta^4*(Vfine:ℝ)) :=
        mul_le_mul_of_nonneg_left hgeometry (by positivity)
      _ = (rankFourConstant*(Q2:ℝ)^2)*(lambda*delta^p*Delta^4*(Vfine:ℝ)) := by ring
      _ ≤ (rankFourConstant*(Q2:ℝ)^2)*
          (pointRatioConstant*(F1:ℝ)*G*(Q1:ℝ)^4*Delta^kappa*(Vcoarse:ℝ)) :=
        mul_le_mul_of_nonneg_left hprofile (by positivity)
      _ = _ := by unfold countConstant; ring
  have hcancel := (mul_le_mul_iff_right₀ (show (0:ℝ)<Vcoarse by exact_mod_cast hVc)).mp hmul
  have hpaid := source_cost_product hd hd1 heta heta2 F1 F2 G Q1 Q2 hF1 hGF hcost1 hcost2
  have hbound := hcancel.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpaid countConstant_pos.le) (Real.rpow_nonneg hDelta.le _))
  have hjoin2 : delta^s*delta^(2*c1+c2)=delta^(pointLoss eta zeta seed fine c1 c2) := by
    rw [←Real.rpow_add hd]
    congr 1
    dsimp [s,p,pointLoss]
    ring
  have hcancel2 : delta^(-(2*c1+c2))*delta^(2*c1+c2)=1 := by
    rw [←Real.rpow_add hd,neg_add_cancel,Real.rpow_zero]
  calc
    _ = (beta^5*lambda^5*q^16*delta^s)*delta^(2*c1+c2) := by rw [←hjoin2]; ring
    _ ≤ (countConstant*delta^(-(2*c1+c2))*Delta^kappa)*delta^(2*c1+c2) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = countConstant*Delta^kappa*(delta^(-(2*c1+c2))*delta^(2*c1+c2)) := by ring
    _ = _ := by rw [hcancel2,mul_one]

/-- Rank four uses etaRank=eta0*c^3 and the source cutoff exponent1/8. -/
def totalExponent (e c eta zeta seed fine c1 c2 : ℝ) (g : ℕ) : ℝ :=
  45*e+32*c+8*(pointLoss eta zeta seed fine c1 c2+16/(g:ℝ))

/-- Fixed constants after the actual normalization Delta=3072r and the
literal lambda/test-radius losses. g is fixed before the native source. -/
def fixedConstant (kappa : ℝ) (g : ℕ) : ℝ :=
  countConstant*(3072:ℝ)^kappa*(2:ℝ)^16*(4*((g:ℝ)+1))^5

lemma fixedConstant_pos (kappa : ℝ) (g : ℕ) : 0 < fixedConstant kappa g := by
  have hC := countConstant_pos
  unfold fixedConstant
  positivity

lemma actual_test_lower {delta r c q : ℝ} (hd : 0 < delta) (hr : 0 < r) (g : ℕ)
    (H : r^(2*c)/(2*delta^(-(1/(g:ℝ)))) ≤ q) :
    (r^(2*c)*delta^(1/(g:ℝ)))/2 ≤ q := by
  have hpos : delta^(1/(g:ℝ))≠0 := (Real.rpow_pos_of_pos hd _).ne'
  calc
    _ = r^(2*c)/(2*delta^(-(1/(g:ℝ)))) := by rw [Real.rpow_neg hd.le]; field_simp [hpos]
    _ ≤ _ := H

/-- The actual retention and mesoscopic q lower retain their full powers.
In particular the transversality loss is32c, not sixteen powers of r. -/
theorem force_scale_power {delta r e c eta zeta seed fine c1 c2 kappa beta lambda q Delta : ℝ}
    (hd : 0 < delta) (hr : 0 < r) (hrdelta : r ≤ delta^(1/8:ℝ))
    (hL : 0 ≤ pointLoss eta zeta seed fine c1 c2)
    (g : ℕ) (hbeta : r^(8*e) ≤ beta)
    (hlambda : lambda=r^e/(4*((g:ℝ)+1)))
    (hq : r^(2*c)/(2*delta^(-(1/(g:ℝ)))) ≤ q) (hDelta : Delta=3072*r)
    (H : beta^5*lambda^5*q^16*delta^(pointLoss eta zeta seed fine c1 c2) ≤
      countConstant*Delta^kappa) :
    r^(totalExponent e c eta zeta seed fine c1 c2 g) ≤ fixedConstant kappa g*r^kappa := by
  let d := 4*((g:ℝ)+1)
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hlpos : 0 < lambda := by rw [hlambda]; positivity
  have hbeta0 : 0 ≤ beta := (Real.rpow_nonneg hr.le _).trans hbeta
  have hb : r^(40*e) ≤ beta^5 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hr.le _) hbeta 5
    have heq : (r^(8*e))^5=r^(40*e) := by
      rw [←Real.rpow_mul_natCast hr.le]
      congr 1
      norm_num only [Nat.cast_ofNat]
      ring
    rwa [heq] at hh
  have hl : lambda^5=r^(5*e)/d^5 := by
    rw [hlambda,div_pow,←Real.rpow_mul_natCast hr.le]
    change r^(e*(5:ℝ))/d^5=_
    congr 1
    congr 1
    ring
  have hql := actual_test_lower hd hr g hq
  have hqp : r^(32*c)*delta^(16/(g:ℝ))/(2:ℝ)^16 ≤ q^16 := by
    have hh := pow_le_pow_left₀ (show 0 ≤ (r^(2*c)*delta^(1/(g:ℝ)))/2 by positivity) hql 16
    have hR : (r^(2*c))^16=r^(32*c) := by
      rw [←Real.rpow_mul_natCast hr.le]
      congr 1
      norm_num only [Nat.cast_ofNat]
      ring
    have hD : (delta^(1/(g:ℝ)))^16=delta^(16/(g:ℝ)) := by
      rw [←Real.rpow_mul_natCast hd.le]
      congr 1
      norm_num only [Nat.cast_ofNat]
      ring
    simpa only [div_pow,mul_pow,hR,hD] using hh
  have hmul := mul_le_mul
    (mul_le_mul_of_nonneg_right hb (show 0 ≤ lambda^5 by positivity)) hqp
    (by positivity) (by positivity)
  have hmulD := mul_le_mul_of_nonneg_right hmul
    (Real.rpow_nonneg hd.le (pointLoss eta zeta seed fine c1 c2))
  have hRjoin : r^(40*e)*r^(5*e)*r^(32*c)=r^(45*e+32*c) := by
    rw [←Real.rpow_add hr,←Real.rpow_add hr]
    congr 1
    ring
  have hDjoin : delta^(16/(g:ℝ))*delta^(pointLoss eta zeta seed fine c1 c2)=
      delta^(pointLoss eta zeta seed fine c1 c2+16/(g:ℝ)) := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  have hlow : r^(45*e+32*c)*delta^(pointLoss eta zeta seed fine c1 c2+16/(g:ℝ))/
      ((2:ℝ)^16*d^5) ≤ countConstant*Delta^kappa := by
    calc
      _ = (r^(40*e)*lambda^5*(r^(32*c)*delta^(16/(g:ℝ))/(2:ℝ)^16))*
          delta^(pointLoss eta zeta seed fine c1 c2) := by
        rw [hl,←hRjoin,←hDjoin]
        field_simp [hdpos.ne']
      _ ≤ _ := hmulD.trans H
  have hclear := (div_le_iff₀ (show 0 < (2:ℝ)^16*d^5 by positivity)).mp hlow
  have hdelta := delta_loss_lower hd hr.le (by norm_num : (0:ℝ)<1/8)
    (show 0 ≤ pointLoss eta zeta seed fine c1 c2+16/(g:ℝ) by positivity) hrdelta
  have hlowR : r^(totalExponent e c eta zeta seed fine c1 c2 g) ≤
      r^(45*e+32*c)*delta^(pointLoss eta zeta seed fine c1 c2+16/(g:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hdelta (Real.rpow_nonneg hr.le (45*e+32*c))
    rw [←Real.rpow_add hr] at hh
    have heq : r^(totalExponent e c eta zeta seed fine c1 c2 g)=
        r^(45*e+32*c+(pointLoss eta zeta seed fine c1 c2+16/(g:ℝ))/(1/8:ℝ)) := by
      unfold totalExponent
      congr 1
      ring
    rw [heq]
    exact hh
  refine hlowR.trans (hclear.trans_eq ?_)
  rw [hDelta,Real.mul_rpow (by norm_num : (0:ℝ)≤3072) hr.le]
  dsimp [fixedConstant,d]
  ring

lemma grid_inverse_le_tau {tau : ℝ} (htau : 0 ≤ tau) (g : ℕ)
    (H : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4) :
    1/(g:ℝ) ≤ tau := by
  have hw : NativeActualMesoscopicRankConfiguration.rankWindow tau ≤ (tau/16)/1000 := min_le_right _ _
  calc
    _ ≤ NativeActualMesoscopicRankConfiguration.rankWindow tau/4 := H.le
    _ ≤ ((tau/16)/1000)/4 := div_le_div_of_nonneg_right hw (by norm_num)
    _ ≤ _ := by linarith

/-- The native tau choice gives a bound independent of J after J was fixed. -/
lemma tau_budget {e tau : ℝ} (htau : 0 ≤ tau) (J : ℕ)
    (H : tau ≤ (e/8)/(1000*((J:ℝ)+1))) : 8000*tau ≤ e := by
  have hden : (0:ℝ)<1000*((J:ℝ)+1) := by positivity
  have hh := (le_div_iff₀ hden).mp H
  have hj : 0 ≤ tau*(J:ℝ) := mul_nonneg htau (Nat.cast_nonneg _)
  nlinarith only [hh,hj]

/-- Every displayed delta loss is paid from the actual source parameter
bounds, including the mesoscopic rounding factor delta^(16/g). -/
lemma exponent_budget {e c eta zeta seed tau : ℝ} (he : 0 ≤ e)
    (htau : 0 ≤ tau) (_hseed0 : 0 ≤ seed)
    (heta : eta ≤ seed/8) (hzeta : zeta ≤ seed/256) (hseed : seed ≤ tau/16384)
    (g J : ℕ) (hgrid : 1/(g:ℝ) ≤ tau)
    (hTau : tau ≤ (e/8)/(1000*((J:ℝ)+1))) :
    totalExponent e c eta zeta seed (tau/16) (seed/8) (e/32) g ≤ 52*e+32*c := by
  have hseedtau : seed ≤ tau := by linarith
  have hL : pointLoss eta zeta seed (tau/16) (seed/8) (e/32) ≤ 21*e/32+4*tau := by
    unfold pointLoss
    linarith
  have hg16 : 16/(g:ℝ) ≤ 16*tau := by
    calc
      _ = 16*(1/(g:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgrid (by norm_num)
  have hpaid := tau_budget htau J hTau
  unfold totalExponent
  linarith only [hL,hg16,hpaid,he]

lemma rank_four_loss_le {kappa eta0 c : ℝ} (hk : 0 < kappa)
    (_he0 : 0 ≤ eta0) (heK : eta0 ≤ kappa/2) (hc : 0 ≤ c) (hc8 : c ≤ 1/8) :
    eta0*c^3 ≤ kappa/1024 := by
  have hp := pow_le_pow_left₀ hc hc8 3
  have hp' : c^3 ≤ (1/512:ℝ) := by norm_num at hp ⊢; exact hp
  have hh := mul_le_mul heK hp' (pow_nonneg hc 3) (show 0 ≤ kappa/2 by positivity)
  nlinarith only [hh]

/-- A concrete hierarchy leaves a strict positive fraction of the kappa gain.
The source tolerance and g are then chosen by the existing actual caller. -/
theorem exponent_le_half_kappa {kappa eta0 c eta zeta seed tau : ℝ}
    (hk : 0 < kappa) (he0 : 0 ≤ eta0) (heK : eta0 ≤ kappa/2)
    (hc : 0 ≤ c) (hc8 : c ≤ 1/8) (hcK : c ≤ kappa/128)
    (htau : 0 ≤ tau) (hseed0 : 0 ≤ seed)
    (heta : eta ≤ seed/8) (hzeta : zeta ≤ seed/256) (hseed : seed ≤ tau/16384)
    (g J : ℕ) (hgrid : 1/(g:ℝ) ≤ tau)
    (hTau : tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1))) :
    totalExponent (eta0*c^3) c eta zeta seed (tau/16) (seed/8) ((eta0*c^3)/32) g ≤ kappa/2 := by
  have he := rank_four_loss_le hk he0 heK hc hc8
  have hfirst := exponent_budget (e:=eta0*c^3) (c:=c) (mul_nonneg he0 (pow_nonneg hc 3))
    htau hseed0 heta hzeta hseed g J hgrid hTau
  calc
    _ ≤ 52*(eta0*c^3)+32*c := hfirst
    _ ≤ 52*(kappa/1024)+32*(kappa/128) :=
      add_le_add (mul_le_mul_of_nonneg_left he (by norm_num))
        (mul_le_mul_of_nonneg_left hcK (by norm_num))
    _ ≤ _ := by linarith

lemma exists_rank_four_hierarchy (kappa : ℝ) (hk : 0 < kappa) :
    ∃c : ℝ,0 < c ∧ c ≤ 1/8 ∧ c ≤ kappa/128 ∧ c ≤ 1/2 := by
  refine ⟨min (1/8) (kappa/128),by positivity,min_le_left _ _,min_le_right _ _,?_⟩
  exact (min_le_left _ _).trans (by norm_num)

/-- The full-rank stopping radius forces a positive-fraction dyadic depth.
This supplies the middle-window premise from an explicit pre-source cutoff. -/
lemma rank_four_middle_lower {delta r tau : ℝ} (hd : 0 < delta)
    (level m : ℕ) (hdy : delta=(2:ℝ)⁻¹^level)
    (hidentity : 48*((2^m:ℕ):ℝ)*r=1) (hr : r ≤ delta^(1/8:ℝ))
    (hsmall : delta^(1/16:ℝ) ≤ 1/48) (htau : tau ≤ 1/2) :
    boundaryWindow tau*(level:ℝ) ≤ (m:ℝ) := by
  have hleft : (2:ℝ)^(-(m:ℝ))=48*r := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,inv_eq_one_div]
    apply (div_eq_iff (show (2:ℝ)^m≠0 by positivity)).mpr
    have hh : 48*(2:ℝ)^m*r=1 := by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hidentity
    nlinarith only [hh]
  have hright : delta^(1/16:ℝ)=(2:ℝ)^(-(level:ℝ)/16) := by
    rw [delta_power hdy]
    congr 1
    ring
  have hpower : delta^(1/8:ℝ)=delta^(1/16:ℝ)*delta^(1/16:ℝ) := by
    rw [←Real.rpow_add hd]
    congr 1
    norm_num
  have h48 : 48*delta^(1/16:ℝ) ≤ 1 := by linarith only [hsmall]
  have hp : (2:ℝ)^(-(m:ℝ)) ≤ (2:ℝ)^(-(level:ℝ)/16) := by
    calc
      _ = 48*r := hleft
      _ ≤ 48*delta^(1/8:ℝ) := mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = (48*delta^(1/16:ℝ))*delta^(1/16:ℝ) := by rw [hpower]; ring
      _ ≤ 1*delta^(1/16:ℝ) := mul_le_mul_of_nonneg_right h48 (Real.rpow_nonneg hd.le _)
      _ = _ := by rw [one_mul,hright]
  have hexp := (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ)<2)).mp hp
  have hdepth : (level:ℝ)/16 ≤ (m:ℝ) := by linarith only [hexp]
  have hb : boundaryWindow tau ≤ 1/16 := by
    exact (min_le_left _ _).trans (by linarith only [htau])
  calc
    _ ≤ (1/16:ℝ)*(level:ℝ) := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _)
    _ = (level:ℝ)/16 := by ring
    _ ≤ _ := hdepth

/-- Choose all constant cutoffs after g, before D. One part supplies the
middle window, and the other makes the remaining kappa/2 gain contradictory. -/
theorem exists_scalar_cutoff (kappa : ℝ) (hk : 0 < kappa) (g : ℕ) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/8 ∧
      ∀delta : ℝ,0 < delta → delta ≤ delta0 →
        delta^(1/16:ℝ) ≤ 1/48 ∧ delta^(kappa/16) ≤ 1/(2*fixedConstant kappa g) := by
  obtain ⟨d1,hd1,_hd11,H1⟩ := NativeQuarterScaleParameters.exists_small_power_cutoff
    (show (0:ℝ)<1/16 by norm_num) (show (0:ℝ)<1/48 by norm_num)
  obtain ⟨d2,hd2,_hd21,H2⟩ := NativeQuarterScaleParameters.exists_small_power_cutoff
    (show 0 < kappa/16 by positivity)
    (show 0 < 1/(2*fixedConstant kappa g) by have hh := fixedConstant_pos kappa g; positivity)
  let delta0 := min (1/8) (min d1 d2)
  refine ⟨delta0,by dsimp [delta0]; positivity,min_le_left _ _,?_⟩
  intro delta hd hsmall
  have hpair := hsmall.trans (min_le_right (1/8) (min d1 d2))
  exact ⟨H1 delta hd (hpair.trans (min_le_left _ _)),H2 delta hd (hpair.trans (min_le_right _ _))⟩

lemma impossible_scale_power {delta r kappa E : ℝ} (hd : 0 < delta)
    (hr : 0 < r) (hr1 : r ≤ 1) (hk : 0 < kappa) (g : ℕ)
    (hscale : r ≤ delta^(1/8:ℝ)) (hE : E ≤ kappa/2)
    (hsmall : delta^(kappa/16) ≤ 1/(2*fixedConstant kappa g))
    (H : r^E ≤ fixedConstant kappa g*r^kappa) : False := by
  have hhalf : 0 < r^(kappa/2) := Real.rpow_pos_of_pos hr _
  have hC := fixedConstant_pos kappa g
  have hpow := (Real.rpow_le_rpow_of_exponent_ge hr hr1 hE).trans H
  have hsplit : r^kappa=r^(kappa/2)*r^(kappa/2) := by
    rw [←Real.rpow_add hr]
    congr 1
    ring
  have hOne : 1 ≤ fixedConstant kappa g*r^(kappa/2) := by
    apply (mul_le_mul_iff_right₀ hhalf).mp
    calc
      r^(kappa/2)*1 = r^(kappa/2) := mul_one _
      _ ≤ fixedConstant kappa g*r^kappa := hpow
      _ = r^(kappa/2)*(fixedConstant kappa g*r^(kappa/2)) := by rw [hsplit]; ring
  have hRsmall : r^(kappa/2) ≤ delta^(kappa/16) := by
    calc
      _ ≤ (delta^(1/8:ℝ))^(kappa/2) := Real.rpow_le_rpow hr.le hscale (by positivity)
      _ = _ := by rw [←Real.rpow_mul hd.le]; congr 1; ring
  have hPaid : fixedConstant kappa g*r^(kappa/2) ≤ 1/2 := by
    calc
      _ ≤ fixedConstant kappa g*(1/(2*fixedConstant kappa g)) :=
        mul_le_mul_of_nonneg_left (hRsmall.trans hsmall) hC.le
      _ = _ := by field_simp [hC.ne']
  linarith only [hOne,hPaid]

/-- Contradiction from the actual count, actual source profile, actual raw
costs and actual retained original mass. No exponent-budget conclusion or
rank-four obstruction is assumed. -/
theorem contradiction_from_counts {delta r q eta eta2 zeta seed tau kappa eta0 c : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hrdelta : r ≤ delta^(1/8:ℝ))
    (hk : 0 < kappa) (he0 : 0 < eta0) (heK : eta0 ≤ kappa/2)
    (hc : 0 < c) (hc8 : c ≤ 1/8) (hcK : c ≤ kappa/128)
    (heta : 0 ≤ eta) (heta2 : 0 ≤ eta2) (hzeta : 0 ≤ zeta) (hseed0 : 0 ≤ seed) (htau : 0 ≤ tau)
    (heSeed : eta ≤ seed/8) (hzSeed : zeta ≤ seed/256) (hseed : seed ≤ tau/16384)
    (g J : ℕ) (hTau : tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1)))
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hq : r^(2*c)/(2*delta^(-(1/(g:ℝ)))) ≤ q)
    (F1 F2 G Q1 Q2 N W Vcoarse Vfine : ℕ) (hF1 : 0 < F1) (hGF : G ≤ F2)
    (hN : 0 < N) (hVc : 0 < Vcoarse)
    (hret : r^(8*(eta0*c^3))*(N:ℝ) ≤ W)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta2) ≤ delta^(-((eta0*c^3)/32)))
    (hgeometry : (Vcoarse:ℝ)*((W:ℝ)/(N:ℝ))^5*(r^(eta0*c^3)/(4*((g:ℝ)+1)))^4*
        (delta^(seed/8+5*((eta0*c^3)/32)))^4*q^16 ≤
      rankFourConstant*(Q2:ℝ)^2*(3072*r)^4*(Vfine:ℝ))
    (hprofile : (r^(eta0*c^3)/(4*((g:ℝ)+1)))*delta^(2*eta+2*zeta+seed+tau/16)*
        (3072*r)^4*(Vfine:ℝ) ≤
      pointRatioConstant*(F1:ℝ)*G*(Q1:ℝ)^4*(3072*r)^kappa*(Vcoarse:ℝ))
    (hsmall : delta^(kappa/16) ≤ 1/(2*fixedConstant kappa g)) : False := by
  let e := eta0*c^3
  have he : 0 < e := by dsimp [e]; positivity
  have hbeta : r^(8*e) ≤ (W:ℝ)/(N:ℝ) :=
    (le_div_iff₀ (show (0:ℝ)<N by exact_mod_cast hN)).mpr hret
  have H := actual_count_power hd hd1 (show (0:ℝ)<3072*r by positivity) heta heta2
    (show 0 < r^e/(4*((g:ℝ)+1)) by positivity) F1 F2 G Q1 Q2 Vcoarse Vfine hF1 hGF hVc
    hcost1 hcost2 hgeometry hprofile
  have hL : 0 ≤ pointLoss eta zeta seed (tau/16) (seed/8) (e/32) := by
    unfold pointLoss
    positivity
  have Hforce := force_scale_power hd hr hrdelta hL g hbeta rfl hq rfl H
  have hE := exponent_le_half_kappa hk he0.le heK hc.le hc8 hcK htau hseed0 heSeed hzSeed hseed
    g J (grid_inverse_le_tau htau g hgrid) hTau
  exact impossible_scale_power hd hr hr1 hk g hrdelta hE hsmall Hforce

/-- A fully source-uniform exclusion threshold. The hierarchy and g are fixed
before delta; all actual source tolerances, counts, weights and cost radices
are quantified afterward. The middle-window cutoff is returned as well. -/
theorem exists_rank_four_exclusion (kappa eta0 c : ℝ)
    (hk : 0 < kappa) (he0 : 0 < eta0) (heK : eta0 ≤ kappa/2)
    (hc : 0 < c) (hc8 : c ≤ 1/8) (hcK : c ≤ kappa/128) (g J : ℕ) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/8 ∧
      ∀delta : ℝ,0 < delta → delta ≤ delta0 →
        delta^(1/16:ℝ) ≤ 1/48 ∧
      ∀r q eta eta2 zeta seed tau : ℝ,
        0 < r → r ≤ 1 → r ≤ delta^(1/8:ℝ) →
        0 ≤ eta → 0 ≤ eta2 → 0 ≤ zeta → 0 ≤ seed → 0 ≤ tau →
        eta ≤ seed/8 → zeta ≤ seed/256 → seed ≤ tau/16384 →
        tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1)) →
        1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4 →
        r^(2*c)/(2*delta^(-(1/(g:ℝ)))) ≤ q →
      ∀F1 F2 G Q1 Q2 N W Vcoarse Vfine : ℕ,
        0 < F1 → G ≤ F2 → 0 < N → 0 < Vcoarse →
        r^(8*(eta0*c^3))*(N:ℝ) ≤ W →
        (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)) →
        (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta2) ≤ delta^(-((eta0*c^3)/32)) →
        (Vcoarse:ℝ)*((W:ℝ)/(N:ℝ))^5*(r^(eta0*c^3)/(4*((g:ℝ)+1)))^4*
          (delta^(seed/8+5*((eta0*c^3)/32)))^4*q^16 ≤
            rankFourConstant*(Q2:ℝ)^2*(3072*r)^4*(Vfine:ℝ) →
        (r^(eta0*c^3)/(4*((g:ℝ)+1)))*delta^(2*eta+2*zeta+seed+tau/16)*
          (3072*r)^4*(Vfine:ℝ) ≤
            pointRatioConstant*(F1:ℝ)*G*(Q1:ℝ)^4*(3072*r)^kappa*(Vcoarse:ℝ) → False := by
  obtain ⟨delta0,hd0,hd08,H⟩ := exists_scalar_cutoff kappa hk g
  refine ⟨delta0,hd0,hd08,?_⟩
  intro delta hd hsmall
  obtain ⟨hmid,hcut⟩ := H delta hd hsmall
  refine ⟨hmid,?_⟩
  intro r q eta eta2 zeta seed tau hr hr1 hrdelta heta heta2 hzeta hseed0 htau
    heSeed hzSeed hseed hTau hgrid hq F1 F2 G Q1 Q2 N W Vcoarse Vfine hF1 hGF hN hVc hret
    hcost1 hcost2 hgeometry hprofile
  exact contradiction_from_counts hd (hsmall.trans (hd08.trans (by norm_num))) hr hr1 hrdelta
    hk he0 heK hc hc8 hcK heta heta2 hzeta hseed0 htau heSeed hzSeed hseed g J hTau hgrid hq
    F1 F2 G Q1 Q2 N W Vcoarse Vfine hF1 hGF hN hVc hret hcost1 hcost2 hgeometry hprofile hcut

end NativeRankFourScalarBudget
