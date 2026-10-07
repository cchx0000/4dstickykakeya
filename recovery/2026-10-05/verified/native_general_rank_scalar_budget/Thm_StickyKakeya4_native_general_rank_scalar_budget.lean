import Theorems.Thm_StickyKakeya4_native_rank_four_scalar_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeGeneralRankScalarBudget
open Classical Finset StickyKakeya4 NativeRankExponentHierarchy
open NativeRankFourScalarBudget NativeCompatibleWeightedRetention NativeMiddleWindowBalance
open NativeRawPointRankFourRatio NativeTwoAxisPowerInterpolation NativeAllTwoScaleConfiguration
open scoped BigOperators

/-- Tuple dimension is one more than the source's rank index. -/
def dimension (i : Fin 4) : ℕ := i.val+1

def gap (kappa : ℝ) (i : Fin 4) : ℝ := kappa+(dimension i:ℝ)-4

/-- Zero and negative candidate gaps do not constrain the hierarchy. -/
def positiveGap (kappa : ℝ) : ℝ :=
  min kappa (min (if 0<kappa-1 then kappa-1 else 1) (if 0<kappa-2 then kappa-2 else 1))

lemma positiveGap_pos {kappa : ℝ} (hk : 0 < kappa) : 0 < positiveGap kappa := by
  unfold positiveGap
  split_ifs <;> positivity

lemma positiveGap_le {kappa : ℝ} (i : Fin 4) (hi : 1 ≤ i.val)
    (hg : 0 < gap kappa i) : positiveGap kappa ≤ gap kappa i := by
  fin_cases i
  · simp at hi
  · have hk : 0 < kappa-2 := by norm_num [gap,dimension] at hg; linarith
    unfold positiveGap
    rw [if_pos hk]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans_eq (by norm_num [gap,dimension]; ring))
  · have hk : 0 < kappa-1 := by norm_num [gap,dimension] at hg; linarith
    unfold positiveGap
    rw [if_pos hk]
    exact (min_le_right _ _).trans ((min_le_left _ _).trans_eq (by norm_num [gap,dimension]; ring))
  · change positiveGap kappa ≤ kappa+(4:ℝ)-4
    rw [add_sub_cancel_right]
    exact min_le_left _ _

/-- This single c is chosen before the source selects its rank. -/
theorem exists_uniform_hierarchy (kappa eta0 : ℝ) (hk : 0 < kappa) (he : 0 ≤ eta0) :
    ∃c : ℝ,0 < c ∧ c ≤ 1/8 ∧ c ≤ 1/(eta0+1) ∧
      c ≤ positiveGap kappa/(256*(eta0+1)) := by
  have hg := positiveGap_pos hk
  refine ⟨min (1/8) (min (1/(eta0+1)) (positiveGap kappa/(256*(eta0+1)))),
    by positivity,min_le_left _ _,?_,?_⟩
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

lemma rankLoss_le_linear {eta0 c : ℝ} (he : 0 ≤ eta0) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (i : Fin 4) (hi : 1 ≤ i.val) : rankLoss eta0 c i ≤ eta0*c := by
  have hp : c^i.val ≤ c := by simpa using (pow_le_pow_of_le_one hc hc1 hi)
  exact mul_le_mul_of_nonneg_left hp he

lemma rankLoss_le_one {eta0 c : ℝ} (he : 0 ≤ eta0) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hsmall : c ≤ 1/(eta0+1)) (i : Fin 4) (hi : 1 ≤ i.val) : rankLoss eta0 c i ≤ 1 := by
  have hden : 0 < eta0+1 := by positivity
  have hh := (le_div_iff₀ hden).mp hsmall
  have hec := rankLoss_le_linear he hc hc1 i hi
  nlinarith only [hh,hec,hc]

lemma hierarchy_margin {kappa eta0 c : ℝ} (he : 0 ≤ eta0) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hsmall : c ≤ positiveGap kappa/(256*(eta0+1)))
    (i : Fin 4) (hi : 1 ≤ i.val) (hg : 0 < gap kappa i) :
    52*rankLoss eta0 c i+32*c ≤ gap kappa i/2 := by
  have hden : 0 < 256*(eta0+1) := by positivity
  have hh := (le_div_iff₀ hden).mp hsmall
  have hgap := positiveGap_le i hi hg
  have hec := rankLoss_le_linear he hc hc1 i hi
  have hec0 : 0 ≤ eta0*c := mul_nonneg he hc
  nlinarith only [hh,hgap,hec,hec0,hc]

/-- The same rich-layer constant works for each chain length at most four;
the threshold denominator 2*ell is bounded by eight. -/
def geometricConstant (ell : ℕ) : ℝ :=
  2*(8*(NativeActualRichPacketLayers.referenceConstant:ℝ))^ell*(41*(256*258):ℝ)^(4*ell)

def combinedConstant (ell : ℕ) : ℝ := geometricConstant ell*pointRatioConstant

lemma combinedConstant_pos (ell : ℕ) : 0 < combinedConstant ell := by
  have hC : (0:ℝ)<NativeActualRichPacketLayers.referenceConstant := by
    exact_mod_cast NativeActualRichPacketLayers.referenceConstant_pos
  have hP := pointRatioConstant_pos
  unfold combinedConstant geometricConstant
  positivity

def pointLoss (ell : ℕ) (eta zeta seed fine c1 c2 : ℝ) : ℝ :=
  ((ell:ℝ)+2)*c1+(5*(ell:ℝ)+1)*c2+2*eta+2*zeta+seed+fine

/-- Combine the literal general-rank count with the same squared source
profile. The original coarse count cancels only after its positivity is used. -/
theorem actual_count_power {delta Delta eta eta2 zeta seed fine c1 c2 kappa beta lambda q : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hDelta : 0 < Delta)
    (heta : 0 ≤ eta) (heta2 : 0 ≤ eta2) (hlambda : 0 < lambda)
    (ell F1 F2 G Q1 Q2 Vcoarse Vfine : ℕ) (hF1 : 0 < F1) (hGF : G ≤ F2)
    (hVc : 0 < Vcoarse)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta2) ≤ delta^(-c2))
    (hgeometry : (Vcoarse:ℝ)*beta^(ell+1)*lambda^ell*(delta^(c1+5*c2))^ell*q^(4*ell) ≤
      geometricConstant ell*(Q2:ℝ)^2*Delta^ell*(Vfine:ℝ))
    (hprofile : lambda*delta^(2*eta+2*zeta+seed+fine)*Delta^4*(Vfine:ℝ) ≤
      pointRatioConstant*(F1:ℝ)*G*(Q1:ℝ)^4*Delta^kappa*(Vcoarse:ℝ)) :
    beta^(ell+1)*lambda^(ell+1)*q^(4*ell)*delta^(pointLoss ell eta zeta seed fine c1 c2) ≤
      combinedConstant ell*Delta^(kappa+(ell:ℝ)-4) := by
  let p := 2*eta+2*zeta+seed+fine
  let s := (ell:ℝ)*c1+5*(ell:ℝ)*c2+p
  have hgeomPow : (delta^(c1+5*c2))^ell=delta^((ell:ℝ)*c1+5*(ell:ℝ)*c2) := by
    rw [←Real.rpow_mul_natCast hd.le]
    congr 1
    ring
  have hjoin : delta^((ell:ℝ)*c1+5*(ell:ℝ)*c2)*delta^p=delta^s := by rw [←Real.rpow_add hd]
  have hDeltaPow : Delta^ell*Delta^(4-(ell:ℝ))=Delta^4 := by
    rw [←Real.rpow_natCast,←Real.rpow_add hDelta]
    norm_num
  have hC : 0 < geometricConstant ell := by
    have hR : (0:ℝ)<NativeActualRichPacketLayers.referenceConstant := by
      exact_mod_cast NativeActualRichPacketLayers.referenceConstant_pos
    unfold geometricConstant
    positivity
  have hmul : (Vcoarse:ℝ)*(beta^(ell+1)*lambda^(ell+1)*q^(4*ell)*delta^s*Delta^(4-(ell:ℝ))) ≤
      (Vcoarse:ℝ)*(combinedConstant ell*((F1:ℝ)*G*(Q1:ℝ)^4*(Q2:ℝ)^2)*Delta^kappa) := by
    calc
      _ = (lambda*delta^p*Delta^(4-(ell:ℝ)))*
          ((Vcoarse:ℝ)*beta^(ell+1)*lambda^ell*(delta^(c1+5*c2))^ell*q^(4*ell)) := by
        rw [hgeomPow,←hjoin,pow_succ lambda]
        ring
      _ ≤ (lambda*delta^p*Delta^(4-(ell:ℝ)))*
          (geometricConstant ell*(Q2:ℝ)^2*Delta^ell*(Vfine:ℝ)) :=
        mul_le_mul_of_nonneg_left hgeometry (by positivity)
      _ = (geometricConstant ell*(Q2:ℝ)^2)*
          (lambda*delta^p*(Delta^ell*Delta^(4-(ell:ℝ)))*(Vfine:ℝ)) := by ring
      _ = (geometricConstant ell*(Q2:ℝ)^2)*(lambda*delta^p*Delta^4*(Vfine:ℝ)) := by rw [hDeltaPow]
      _ ≤ (geometricConstant ell*(Q2:ℝ)^2)*
          (pointRatioConstant*(F1:ℝ)*G*(Q1:ℝ)^4*Delta^kappa*(Vcoarse:ℝ)) :=
        mul_le_mul_of_nonneg_left hprofile (by positivity)
      _ = _ := by unfold combinedConstant; ring
  have hcancel := (mul_le_mul_iff_right₀ (show (0:ℝ)<Vcoarse by exact_mod_cast hVc)).mp hmul
  have hpaid := source_cost_product hd hd1 heta heta2 F1 F2 G Q1 Q2 hF1 hGF hcost1 hcost2
  have hbound := hcancel.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpaid (combinedConstant_pos ell).le) (Real.rpow_nonneg hDelta.le _))
  have hjoin2 : delta^s*delta^(2*c1+c2)=delta^(pointLoss ell eta zeta seed fine c1 c2) := by
    rw [←Real.rpow_add hd]
    congr 1
    dsimp [s,p,pointLoss]
    ring
  have hcancel2 : delta^(-(2*c1+c2))*delta^(2*c1+c2)=1 := by
    rw [←Real.rpow_add hd,neg_add_cancel,Real.rpow_zero]
  have hDeltaSplit : Delta^kappa=Delta^(kappa+(ell:ℝ)-4)*Delta^(4-(ell:ℝ)) := by
    rw [←Real.rpow_add hDelta]
    congr 1
    ring
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hDelta (4-(ell:ℝ)))).mp
  calc
    _ = (beta^(ell+1)*lambda^(ell+1)*q^(4*ell)*delta^s*Delta^(4-(ell:ℝ)))*delta^(2*c1+c2) := by
      rw [←hjoin2]
      ring
    _ ≤ (combinedConstant ell*delta^(-(2*c1+c2))*Delta^kappa)*delta^(2*c1+c2) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = combinedConstant ell*Delta^kappa*(delta^(-(2*c1+c2))*delta^(2*c1+c2)) := by ring
    _ = _ := by rw [hcancel2,mul_one,hDeltaSplit]; ring

def totalExponent (ell : ℕ) (e c a eta zeta seed fine c1 c2 : ℝ) (g : ℕ) : ℝ :=
  (2*(ell:ℝ)+1)*((ell:ℝ)+1)*e+8*(ell:ℝ)*c+
    (pointLoss ell eta zeta seed fine c1 c2+4*(ell:ℝ)/(g:ℝ))/a

def fixedConstant (ell : ℕ) (gamma : ℝ) (g : ℕ) : ℝ :=
  combinedConstant ell*(3072:ℝ)^gamma*(2:ℝ)^(4*ell)*(4*((g:ℝ)+1))^(ell+1)

lemma fixedConstant_pos (ell : ℕ) (gamma : ℝ) (g : ℕ) : 0 < fixedConstant ell gamma g := by
  have hC := combinedConstant_pos ell
  unfold fixedConstant
  positivity

/-- Preserve the actual beta, lambda and mesoscopic test-radius powers. -/
theorem force_scale_power {delta r e c a eta zeta seed fine c1 c2 gamma beta lambda q Delta : ℝ}
    (hd : 0 < delta) (hr : 0 < r) (ha : 0 < a) (hrdelta : r ≤ delta^a)
    (ell : ℕ) (hL : 0 ≤ pointLoss ell eta zeta seed fine c1 c2)
    (g : ℕ) (hbeta : r^(2*(ell:ℝ)*e) ≤ beta)
    (hlambda : lambda=r^e/(4*((g:ℝ)+1)))
    (hq : r^(2*c)/(2*delta^(-(1/(g:ℝ)))) ≤ q) (hDelta : Delta=3072*r)
    (H : beta^(ell+1)*lambda^(ell+1)*q^(4*ell)*delta^(pointLoss ell eta zeta seed fine c1 c2) ≤
      combinedConstant ell*Delta^gamma) :
    r^(totalExponent ell e c a eta zeta seed fine c1 c2 g) ≤ fixedConstant ell gamma g*r^gamma := by
  let d := 4*((g:ℝ)+1)
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hlpos : 0 < lambda := by rw [hlambda]; positivity
  have hbeta0 : 0 ≤ beta := (Real.rpow_nonneg hr.le _).trans hbeta
  have hb : r^(2*(ell:ℝ)*((ell:ℝ)+1)*e) ≤ beta^(ell+1) := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hr.le _) hbeta (ell+1)
    have heq : (r^(2*(ell:ℝ)*e))^(ell+1)=r^(2*(ell:ℝ)*((ell:ℝ)+1)*e) := by
      rw [←Real.rpow_mul_natCast hr.le]
      congr 1
      push_cast
      ring
    rwa [heq] at hh
  have hl : lambda^(ell+1)=r^(((ell:ℝ)+1)*e)/d^(ell+1) := by
    rw [hlambda,div_pow,←Real.rpow_mul_natCast hr.le]
    change r^(e*((ell+1:ℕ):ℝ))/d^(ell+1)=_
    congr 1
    congr 1
    push_cast
    ring
  have hql := actual_test_lower hd hr g hq
  have hqp : r^(8*(ell:ℝ)*c)*delta^(4*(ell:ℝ)/(g:ℝ))/(2:ℝ)^(4*ell) ≤ q^(4*ell) := by
    have hh := pow_le_pow_left₀ (show 0 ≤ (r^(2*c)*delta^(1/(g:ℝ)))/2 by positivity) hql (4*ell)
    have hR : (r^(2*c))^(4*ell)=r^(8*(ell:ℝ)*c) := by
      rw [←Real.rpow_mul_natCast hr.le]
      congr 1
      push_cast
      ring
    have hD : (delta^(1/(g:ℝ)))^(4*ell)=delta^(4*(ell:ℝ)/(g:ℝ)) := by
      rw [←Real.rpow_mul_natCast hd.le]
      congr 1
      push_cast
      ring
    simpa only [div_pow,mul_pow,hR,hD] using hh
  have hmul := mul_le_mul
    (mul_le_mul_of_nonneg_right hb (show 0 ≤ lambda^(ell+1) by positivity)) hqp
    (by positivity) (by positivity)
  have hmulD := mul_le_mul_of_nonneg_right hmul
    (Real.rpow_nonneg hd.le (pointLoss ell eta zeta seed fine c1 c2))
  have hRjoin : r^(2*(ell:ℝ)*((ell:ℝ)+1)*e)*r^(((ell:ℝ)+1)*e)*r^(8*(ell:ℝ)*c)=
      r^((2*(ell:ℝ)+1)*((ell:ℝ)+1)*e+8*(ell:ℝ)*c) := by
    rw [←Real.rpow_add hr,←Real.rpow_add hr]
    congr 1
    ring
  have hDjoin : delta^(4*(ell:ℝ)/(g:ℝ))*delta^(pointLoss ell eta zeta seed fine c1 c2)=
      delta^(pointLoss ell eta zeta seed fine c1 c2+4*(ell:ℝ)/(g:ℝ)) := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  have hlow : r^((2*(ell:ℝ)+1)*((ell:ℝ)+1)*e+8*(ell:ℝ)*c)*
      delta^(pointLoss ell eta zeta seed fine c1 c2+4*(ell:ℝ)/(g:ℝ))/
      ((2:ℝ)^(4*ell)*d^(ell+1)) ≤ combinedConstant ell*Delta^gamma := by
    calc
      _ = (r^(2*(ell:ℝ)*((ell:ℝ)+1)*e)*lambda^(ell+1)*
          (r^(8*(ell:ℝ)*c)*delta^(4*(ell:ℝ)/(g:ℝ))/(2:ℝ)^(4*ell)))*
          delta^(pointLoss ell eta zeta seed fine c1 c2) := by
        rw [hl,←hRjoin,←hDjoin]
        field_simp [hdpos.ne']
      _ ≤ _ := hmulD.trans H
  have hclear := (div_le_iff₀ (show 0 < (2:ℝ)^(4*ell)*d^(ell+1) by positivity)).mp hlow
  have hdelta := delta_loss_lower hd hr.le ha
    (show 0 ≤ pointLoss ell eta zeta seed fine c1 c2+4*(ell:ℝ)/(g:ℝ) by positivity) hrdelta
  have hlowR : r^(totalExponent ell e c a eta zeta seed fine c1 c2 g) ≤
      r^((2*(ell:ℝ)+1)*((ell:ℝ)+1)*e+8*(ell:ℝ)*c)*
        delta^(pointLoss ell eta zeta seed fine c1 c2+4*(ell:ℝ)/(g:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hdelta
      (Real.rpow_nonneg hr.le ((2*(ell:ℝ)+1)*((ell:ℝ)+1)*e+8*(ell:ℝ)*c))
    rw [←Real.rpow_add hr] at hh
    exact hh
  refine hlowR.trans (hclear.trans_eq ?_)
  rw [hDelta,Real.mul_rpow (by norm_num : (0:ℝ)≤3072) hr.le]
  dsimp [fixedConstant,d]
  ring

lemma tau_budget {a e tau : ℝ} (htau : 0 ≤ tau) (J : ℕ)
    (H : tau ≤ a*e/(1000*((J:ℝ)+1))) : 1000*tau ≤ a*e := by
  have hden : (0:ℝ)<1000*((J:ℝ)+1) := by positivity
  have hh := (le_div_iff₀ hden).mp H
  have hj : 0 ≤ tau*(J:ℝ) := mul_nonneg htau (Nat.cast_nonneg _)
  nlinarith only [hh,hj]

/-- The same actual source tolerance pays the losses at every admissible rank. -/
lemma exponent_budget {e c a eta zeta seed tau : ℝ} (he : 0 ≤ e) (hc : 0 ≤ c) (ha : 0 < a)
    (htau : 0 ≤ tau) (hseed0 : 0 ≤ seed)
    (heta : eta ≤ seed/8) (hzeta : zeta ≤ seed/256) (hseed : seed ≤ tau/16384)
    (ell : ℕ) (hell : ell ≤ 4) (g J : ℕ) (hgrid : 1/(g:ℝ) ≤ tau)
    (hTau : tau ≤ a*e/(1000*((J:ℝ)+1))) :
    totalExponent ell e c a eta zeta seed (tau/16) (seed/8) (a*e/4) g ≤ 52*e+32*c := by
  have hel : (ell:ℝ) ≤ 4 := by exact_mod_cast hell
  have he0 : (0:ℝ) ≤ ell := Nat.cast_nonneg _
  have hae : 0 ≤ a*e := mul_nonneg ha.le he
  have hseedtau : seed ≤ tau := by linarith
  have hL : pointLoss ell eta zeta seed (tau/16) (seed/8) (a*e/4) ≤ 21*a*e/4+4*tau := by
    have h1 := mul_le_mul_of_nonneg_right (show (ell:ℝ)+2≤6 by linarith) (show 0 ≤ seed/8 by positivity)
    have h2 := mul_le_mul_of_nonneg_right (show 5*(ell:ℝ)+1≤21 by linarith) (show 0≤a*e/4 by positivity)
    unfold pointLoss
    linarith
  have hg16 : 4*(ell:ℝ)/(g:ℝ) ≤ 16*tau := by
    calc
      _ ≤ 16/(g:ℝ) := div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      _ = 16*(1/(g:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgrid (by norm_num)
  have hpaid := tau_budget htau J hTau
  have hdiv : (pointLoss ell eta zeta seed (tau/16) (seed/8) (a*e/4)+4*(ell:ℝ)/(g:ℝ))/a ≤ 7*e := by
    apply (div_le_iff₀ ha).mpr
    nlinarith only [hL,hg16,hpaid,hae]
  have hcoef : (2*(ell:ℝ)+1)*((ell:ℝ)+1) ≤ 45 := by
    have hh := mul_le_mul (show 2*(ell:ℝ)+1≤9 by linarith) (show (ell:ℝ)+1≤5 by linarith)
      (by positivity : 0≤(ell:ℝ)+1) (by norm_num : (0:ℝ)≤9)
    norm_num at hh
    exact hh
  have hb := mul_le_mul_of_nonneg_right hcoef he
  have hc' := mul_le_mul_of_nonneg_right (show 8*(ell:ℝ)≤32 by linarith) hc
  unfold totalExponent
  linarith only [hb,hc',hdiv]

lemma rank_exponent_margin {kappa eta0 c eta zeta seed tau : ℝ}
    (he : 0 ≤ eta0) (hc : 0 < c) (hc1 : c ≤ 1)
    (hsmall : c ≤ positiveGap kappa/(256*(eta0+1)))
    (i : Fin 4) (hi : 1 ≤ i.val) (hg : 0 < gap kappa i)
    (htau : 0 ≤ tau) (hseed0 : 0 ≤ seed)
    (heta : eta ≤ seed/8) (hzeta : zeta ≤ seed/256) (hseed : seed ≤ tau/16384)
    (g J : ℕ) (hgrid : 1/(g:ℝ) ≤ tau)
    (hTau : tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1))) :
    totalExponent (dimension i) (rankLoss eta0 c i) c (cutoff c i)
      eta zeta seed (tau/16) (seed/8) (commonBudget eta0 c/4) g ≤ gap kappa i/2 := by
  have hident := cutoff_mul_rankLoss eta0 c i
  have hbound := exponent_budget (e:=rankLoss eta0 c i)
    (show 0 ≤ rankLoss eta0 c i from mul_nonneg he (pow_nonneg hc.le i.val)) hc.le
    (cutoff_bounds hc hc1 i).1 htau hseed0 heta hzeta hseed (dimension i)
    (by dsimp [dimension]; omega) g J hgrid (by rwa [hident])
  rw [hident] at hbound
  exact hbound.trans (hierarchy_margin he hc.le hc1 hsmall i hi hg)

/-- In the chosen hierarchy the middle-window tolerance is below the rank cutoff. -/
lemma tau_le_cutoff {eta0 c tau : ℝ} (he : 0 ≤ eta0) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcsmall : c ≤ 1/(eta0+1)) (i : Fin 4) (hi : 1 ≤ i.val)
    (htau : 0 ≤ tau) (J : ℕ)
    (hTau : tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1))) : tau ≤ 4*cutoff c i := by
  have hident := cutoff_mul_rankLoss eta0 c i
  have hh := tau_budget htau J (show tau ≤ cutoff c i*rankLoss eta0 c i/(1000*((J:ℝ)+1)) by rwa [hident])
  have hloss := rankLoss_le_one he hc.le hc1 hcsmall i hi
  have ha := (cutoff_bounds hc hc1 i).1
  have hm := mul_le_mul_of_nonneg_left hloss ha.le
  nlinarith only [hh,hm,ha]

/-- The middle window follows from the actual stopping identity at any rank. -/
lemma middle_lower {delta r tau a : ℝ} (hd : 0 < delta) (ha : 0 ≤ a)
    (level m : ℕ) (hdy : delta=(2:ℝ)⁻¹^level)
    (hidentity : 48*((2^m:ℕ):ℝ)*r=1) (hr : r ≤ delta^a)
    (hsmall : delta^(a/2) ≤ 1/48) (htau : tau ≤ 4*a) :
    boundaryWindow tau*(level:ℝ) ≤ (m:ℝ) := by
  have hleft : (2:ℝ)^(-(m:ℝ))=48*r := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,inv_eq_one_div]
    apply (div_eq_iff (show (2:ℝ)^m≠0 by positivity)).mpr
    have hh : 48*(2:ℝ)^m*r=1 := by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hidentity
    nlinarith only [hh]
  have hright : delta^(a/2)=(2:ℝ)^(-(level:ℝ)*(a/2)) := delta_power hdy _
  have hpower : delta^a=delta^(a/2)*delta^(a/2) := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  have h48 : 48*delta^(a/2) ≤ 1 := by linarith only [hsmall]
  have hp : (2:ℝ)^(-(m:ℝ)) ≤ (2:ℝ)^(-(level:ℝ)*(a/2)) := by
    calc
      _ = 48*r := hleft
      _ ≤ 48*delta^a := mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = (48*delta^(a/2))*delta^(a/2) := by rw [hpower]; ring
      _ ≤ 1*delta^(a/2) := mul_le_mul_of_nonneg_right h48 (Real.rpow_nonneg hd.le _)
      _ = _ := by rw [one_mul,hright]
  have hexp := (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ)<2)).mp hp
  have hdepth : (a/2)*(level:ℝ) ≤ (m:ℝ) := by nlinarith only [hexp]
  have hb : boundaryWindow tau ≤ a/2 := (min_le_left _ _).trans (by linarith only [htau,ha])
  exact (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _)).trans hdepth

/-- A single cutoff covers every eventual rank and every positive gap. -/
theorem exists_uniform_cutoff (kappa c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (g : ℕ) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/8 ∧
      ∀delta : ℝ,0 < delta → delta ≤ delta0 → ∀i : Fin 4,
        delta^(cutoff c i/2) ≤ 1/48 ∧
        (0 < gap kappa i → delta^(cutoff c i*gap kappa i/2) ≤
          1/(2*fixedConstant (dimension i) (gap kappa i) g)) := by
  have H : ∀i : Fin 4,∃di : ℝ,0 < di ∧ di ≤ 1/8 ∧
      ∀delta : ℝ,0 < delta → delta ≤ di →
        delta^(cutoff c i/2) ≤ 1/48 ∧
        (0 < gap kappa i → delta^(cutoff c i*gap kappa i/2) ≤
          1/(2*fixedConstant (dimension i) (gap kappa i) g)) := by
    intro i
    have ha := (cutoff_bounds hc hc1 i).1
    obtain ⟨d1,hd1,_hd11,H1⟩ := NativeQuarterScaleParameters.exists_small_power_cutoff
      (show 0<cutoff c i/2 by positivity) (show (0:ℝ)<1/48 by norm_num)
    by_cases hg : 0 < gap kappa i
    · obtain ⟨d2,hd2,_hd21,H2⟩ := NativeQuarterScaleParameters.exists_small_power_cutoff
        (show 0<cutoff c i*gap kappa i/2 by positivity)
        (show 0<1/(2*fixedConstant (dimension i) (gap kappa i) g) by
          have hh := fixedConstant_pos (dimension i) (gap kappa i) g
          positivity)
      refine ⟨min (1/8) (min d1 d2),by positivity,min_le_left _ _,?_⟩
      intro delta hd hsmall
      have hpair := hsmall.trans (min_le_right _ _)
      exact ⟨H1 delta hd (hpair.trans (min_le_left _ _)),fun _ => H2 delta hd (hpair.trans (min_le_right _ _))⟩
    · refine ⟨min (1/8) d1,by positivity,min_le_left _ _,?_⟩
      intro delta hd hsmall
      exact ⟨H1 delta hd (hsmall.trans (min_le_right _ _)),fun h => (hg h).elim⟩
  choose d hd hd8 H using H
  let delta0 := univ.inf' (univ_nonempty : (univ:Finset (Fin 4)).Nonempty) d
  have hle : ∀i,delta0 ≤ d i := fun i => inf'_le d (mem_univ i)
  refine ⟨delta0,?_,(hle 0).trans (hd8 0),?_⟩
  · exact (lt_inf'_iff _).mpr (fun i _ => hd i)
  · intro delta hdelta hsmall i
    exact H i delta hdelta (hsmall.trans (hle i))

lemma impossible_scale_power {delta r gamma E a : ℝ} (hd : 0 < delta)
    (hr : 0 < r) (hr1 : r ≤ 1) (hg : 0 < gamma) (ell g : ℕ)
    (hscale : r ≤ delta^a) (hE : E ≤ gamma/2)
    (hsmall : delta^(a*gamma/2) ≤ 1/(2*fixedConstant ell gamma g))
    (H : r^E ≤ fixedConstant ell gamma g*r^gamma) : False := by
  have hhalf : 0 < r^(gamma/2) := Real.rpow_pos_of_pos hr _
  have hC := fixedConstant_pos ell gamma g
  have hpow := (Real.rpow_le_rpow_of_exponent_ge hr hr1 hE).trans H
  have hsplit : r^gamma=r^(gamma/2)*r^(gamma/2) := by
    rw [←Real.rpow_add hr]
    congr 1
    ring
  have hOne : 1 ≤ fixedConstant ell gamma g*r^(gamma/2) := by
    apply (mul_le_mul_iff_right₀ hhalf).mp
    calc
      r^(gamma/2)*1 = r^(gamma/2) := mul_one _
      _ ≤ fixedConstant ell gamma g*r^gamma := hpow
      _ = r^(gamma/2)*(fixedConstant ell gamma g*r^(gamma/2)) := by rw [hsplit]; ring
  have hRsmall : r^(gamma/2) ≤ delta^(a*gamma/2) := by
    calc
      _ ≤ (delta^a)^(gamma/2) := Real.rpow_le_rpow hr.le hscale (by positivity)
      _ = _ := by rw [←Real.rpow_mul hd.le]; congr 1; ring
  have hPaid : fixedConstant ell gamma g*r^(gamma/2) ≤ 1/2 := by
    calc
      _ ≤ fixedConstant ell gamma g*(1/(2*fixedConstant ell gamma g)) :=
        mul_le_mul_of_nonneg_left (hRsmall.trans hsmall) hC.le
      _ = _ := by field_simp [hC.ne']
  linarith only [hOne,hPaid]

/-- One prechosen hierarchy and its simultaneous cutoff force the actual
transverse-dimension range. The only count inputs are the literal original
weighted count and squared source ratio; no dimension-range certificate is used. -/
theorem dimension_range_from_counts {delta r q eta eta2 zeta seed tau kappa eta0 c : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (he0 : 0 < eta0) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcGap : c ≤ positiveGap kappa/(256*(eta0+1)))
    (i : Fin 4) (hi : 1 ≤ i.val) (hrdelta : r ≤ delta^(cutoff c i))
    (heta : 0 ≤ eta) (heta2 : 0 ≤ eta2) (hzeta : 0 ≤ zeta) (hseed0 : 0 ≤ seed) (htau : 0 ≤ tau)
    (heSeed : eta ≤ seed/8) (hzSeed : zeta ≤ seed/256) (hseed : seed ≤ tau/16384)
    (g J : ℕ) (hTau : tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1)))
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hq : r^(2*c)/(2*delta^(-(1/(g:ℝ)))) ≤ q)
    (F1 F2 G Q1 Q2 N W Vcoarse Vfine : ℕ) (hF1 : 0 < F1) (hGF : G ≤ F2)
    (hN : 0 < N) (hVc : 0 < Vcoarse)
    (hret : r^(2*(dimension i:ℝ)*rankLoss eta0 c i)*(N:ℝ) ≤ W)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta2) ≤ delta^(-(commonBudget eta0 c/4)))
    (hgeometry : (Vcoarse:ℝ)*((W:ℝ)/(N:ℝ))^(dimension i+1)*
        (r^(rankLoss eta0 c i)/(4*((g:ℝ)+1)))^(dimension i)*
        (delta^(seed/8+5*(commonBudget eta0 c/4)))^(dimension i)*q^(4*dimension i) ≤
      geometricConstant (dimension i)*(Q2:ℝ)^2*(3072*r)^(dimension i)*(Vfine:ℝ))
    (hprofile : (r^(rankLoss eta0 c i)/(4*((g:ℝ)+1)))*delta^(2*eta+2*zeta+seed+tau/16)*
        (3072*r)^4*(Vfine:ℝ) ≤
      pointRatioConstant*(F1:ℝ)*G*(Q1:ℝ)^4*(3072*r)^kappa*(Vcoarse:ℝ))
    (hsmall : 0 < gap kappa i → delta^(cutoff c i*gap kappa i/2) ≤
      1/(2*fixedConstant (dimension i) (gap kappa i) g)) : kappa+(dimension i:ℝ) ≤ 4 := by
  by_contra hbad
  have hgap : 0 < gap kappa i := by unfold gap; linarith only [hbad]
  have he := rankLoss_pos he0 hc i
  have ht := commonBudget_pos he0 hc
  have ha := (cutoff_bounds hc hc1 i).1
  have hbeta : r^(2*(dimension i:ℝ)*rankLoss eta0 c i) ≤ (W:ℝ)/(N:ℝ) :=
    (le_div_iff₀ (show (0:ℝ)<N by exact_mod_cast hN)).mpr hret
  have H := actual_count_power hd hd1 (show (0:ℝ)<3072*r by positivity) heta heta2
    (show 0 < r^(rankLoss eta0 c i)/(4*((g:ℝ)+1)) by positivity)
    (dimension i) F1 F2 G Q1 Q2 Vcoarse Vfine hF1 hGF hVc hcost1 hcost2 hgeometry hprofile
  have hL : 0 ≤ pointLoss (dimension i) eta zeta seed (tau/16) (seed/8) (commonBudget eta0 c/4) := by
    unfold pointLoss
    positivity
  have Hforce := force_scale_power (gamma:=gap kappa i) hd hr ha hrdelta (dimension i) hL g hbeta rfl hq rfl H
  have hE := rank_exponent_margin he0.le hc hc1 hcGap i hi hgap htau hseed0 heSeed hzSeed hseed
    g J (grid_inverse_le_tau htau g hgrid) hTau
  exact impossible_scale_power hd hr hr1 hgap (dimension i) g hrdelta hE (hsmall hgap) Hforce

end NativeGeneralRankScalarBudget
