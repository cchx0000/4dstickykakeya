import Theorems.Thm_StickyKakeya4_native_retained_slice_budget_cutoff

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeRetainedSliceBudgetFinal
open NativeRetainedSliceBudgetSource NativeRetainedSliceBudgetExtra NativeRetainedSliceBudgetCutoff
open NativeReferenceSliceBudgetSource NativeReferenceSliceBudgetCutoff NativeRankExponentHierarchy
open NativeFixedCompactKakeyaExponent NativeHorizontalMenuScaleCost NativeAllTwoScaleConfiguration

theorem exists_initial_parameters (epsilon : ℝ) (he : 0 < epsilon) :
    ∃J : ℕ,0 < J ∧ 3/(J:ℝ) ≤ epsilon/8 ∧
      ∃etaMax cMax : ℝ,0 < etaMax ∧ etaMax ≤ 1 ∧ etaMax ≤ epsilon/336 ∧
        0 < cMax ∧ cMax ≤ 1/2 ∧ cMax ≤ quotientTolerance epsilon/24 := by
  obtain ⟨J,hJ,hgap,etaMax,he0,he1,heSmall⟩ := exists_fixed_ad_parameters (epsilon/2) (half_pos he)
  obtain ⟨heQ,heQ1,_heQsmall⟩ := quotientTolerance_bounds he
  refine ⟨J,hJ,by linarith only [hgap],etaMax,quotientTolerance epsilon/24,
    he0,he1,by linarith only [heSmall],by positivity,?_,le_rfl⟩
  linarith only [heQ1]

lemma source_eta_allowance {eta seed tau t : ℝ} (ht : 0 ≤ t)
    (heta : eta ≤ seed/8) (hseed : seed ≤ tau/16384) (htau : tau ≤ t/1024) :
    eta ≤ t/32 := by linarith only [ht,heta,hseed,htau]

/-- Pay the literal retained AD constant, including graph selection,
quotient ceiling, and the same third core. The third allowance is supplied
by exists_third_budget_cutoffs before D, uniformly over the actual S. -/
theorem actual_retained_constant_le_power
    {delta eta zeta lambda b tau seed c2 r q eta0 c epsilon : ℝ}
    (he : 0 < epsilon) (he0 : 0 < eta0) (he01 : eta0 ≤ 1) (heSmall : eta0 ≤ epsilon/336)
    (hc : 0 < c) (hcsmall : c ≤ 1/2) (hcQ : c ≤ quotientTolerance epsilon/24)
    (F1 F2 G Q1 Q2 F3 Q3 g K J m : ℕ) (i : Fin 4)
    (hJ : 0 < J) (hJloss : 3/(J:ℝ) ≤ epsilon/8) (hm6 : 6 ≤ m) (hell : i.val+1 ≤ 3)
    (hd : 0 < delta) (hsmall : delta ≤ sourceCutoff (epsilon/2) c g (half_pos he) hc)
    (hsmallExtra : delta ≤ extraCutoff epsilon c g K he hc) (heta : 0 ≤ eta)
    (hF1 : 0 < F1) (hG : 0 < G) (hQ1 : 1 ≤ Q1) (hQ2 : 0 < Q2) (hGF : G ≤ F2)
    (hF3 : 0 < F3) (hQ3 : 0 < Q3)
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
    actualRetainedConstant delta eta zeta lambda b F1 G Q2 tau seed c2
        (min (boundaryWindow tau) ((tau/16)/1000)) F3 Q3 q J m K (3-extremalExponent) ≤
      ((64:ℝ)/((2^m:ℕ):ℝ))^(-epsilon) := by
  let rho : ℝ := 64/((2^m:ℕ):ℝ)
  let w := min (boundaryWindow tau) ((tau/16)/1000)
  have hd1 := hsmall.trans (sourceCutoff_le_one (epsilon/2) c g (half_pos he) hc)
  have hc1 : c ≤ 1 := by linarith only [hcsmall]
  have ht := commonBudget_pos he0 hc
  have hloss := rankLoss_pos he0 hc i
  have hle := rankLoss_le_initial he0.le hc.le hc1 i
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    dsimp [rho]
    rw [parent_scale_dyadic_span m hm6]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hlambdapos : 0 < lambda := by rw [hlambda]; positivity
  have hbpos : 0 < b := (Real.rpow_pos_of_pos hr _).trans_le hb
  have hF1r : (0:ℝ)<F1 := by exact_mod_cast hF1
  have hGr : (0:ℝ)<G := by exact_mod_cast hG
  have hQ2n : 1 ≤ Q2 := hQ2
  have hQ2r : (1:ℝ) ≤ Q2 := by exact_mod_cast hQ2n
  have hF3r : (0:ℝ)<F3 := by exact_mod_cast hF3
  have hQ3r : (0:ℝ)<Q3 := by exact_mod_cast hQ3
  have Href := NativeReferenceSliceBudgetFinal.actual_reference_constant_le_power
    (half_pos he) he0 he01 (by linarith only [heSmall]) hc hcsmall F1 F2 G Q1 Q2 g J m i
    hJ (by linarith only [hJloss]) hm6 hell hd hsmall heta hF1 hG hQ1 hQ2 hGF H1 H2
    htau hseed hzeta hc2 hr hr1 hrdelta hlambda hb hscale
  have Hcompare := actualRetainedConstant_le (eta:=eta) (zeta:=zeta) (tau:=tau) (seed:=seed) (c2:=c2) (w:=w)
    (s:=3-extremalExponent) J m K hd hlambdapos hbpos hF1r hGr hQ2r hF3r hQ3r hq
  have Hqlow := actual_quotient_test hd hr hr1 he he0.le he01 heSmall hc hc1 hcQ i
    hrdelta htau0 g htau hgrid hqraw
  obtain ⟨heQ,heQ1,heQsmall⟩ := quotientTolerance_bounds he
  have Hextra := extra_coefficient_bound hd hd1 heta F1 F2 G Q1 Q2 F3 Q3 g (i.val+1) K
    hF1 hG hQ1 hQ2n hGF H1 H2 H3 ht.le htau hseed hc2 hr hr1 hloss.le (hle.trans he01)
    hell hrdelta (cutoff_mul_rankLoss eta0 c i).symm hlambda hb hrho hrho1 hscale hq hq1 heQ.le heQ1 Hqlow
  have Hpaid := extraCutoff_pays epsilon c g K he hc delta hd hsmallExtra rho r (cutoff c i)
    hrho (cutoff_bounds hc hc1 i).2.2 hrdelta hscale
  have hexp : 18*rankLoss eta0 c i+4*quotientTolerance epsilon/3 ≤ epsilon/4 := by
    linarith only [hle.trans heSmall,heQsmall,he]
  have HextraPaid : max 1 (extraCoefficient delta eta lambda b F1 G F3 Q3 q K) ≤ rho^(-(epsilon/2)) :=
    Hextra.trans (calc
      _ ≤ rho^(-(epsilon/4))*rho^(-(18*rankLoss eta0 c i+4*quotientTolerance epsilon/3)) :=
        mul_le_mul_of_nonneg_right Hpaid (by positivity)
      _ = rho^(-(epsilon/4+(18*rankLoss eta0 c i+4*quotientTolerance epsilon/3))) := by
        rw [←Real.rpow_add hrho]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hrho hrho1 (by linarith only [hexp]))
  exact Hcompare.trans (calc
    _ ≤ rho^(-(epsilon/2))*rho^(-(epsilon/2)) :=
      mul_le_mul Href HextraPaid (by positivity) (by positivity)
    _ = _ := by rw [←Real.rpow_add hrho]; congr 1; ring)

end NativeRetainedSliceBudgetFinal
