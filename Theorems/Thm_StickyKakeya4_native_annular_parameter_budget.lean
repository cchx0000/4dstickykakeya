import Theorems.Thm_StickyKakeya4_native_original_radial_reduction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Theorems.Thm_StickyKakeya4_original_radial_near_diagonal

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace NativeAnnularParameterBudget
open Filter
open OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl

/-- The actual source choice eta'=(4+12/t)eta pays both oriented annular
deletions with a positive exponent margin, uniformly for sigma<=1. -/
theorem native_annular_loss_power (delta eta t sigma : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta) (ht : 0<t) (hsigma : sigma≤1) :
    (delta^(2*eta/t))^(-3*sigma)*delta^((4+12/t)*eta-eta)≤delta^(3*eta) := by
  rw [← Real.rpow_mul hd.le,← Real.rpow_add hd]
  apply Real.rpow_le_rpow_of_exponent_ge hd hd1
  have h1 : 0≤(12-6*sigma)/t := div_nonneg (by linarith only [hsigma]) ht.le
  have h2 := mul_nonneg heta h1
  have heq : (2*eta/t)*(-3*sigma)+((4+12/t)*eta-eta)=
      3*eta+eta*((12-6*sigma)/t) := by ring
  rw [heq]
  linarith only [h2]

/-- The original chosen exclusion scale cancels the annular threshold's
negative power exactly. -/
theorem native_annular_top_power (delta eta' a : ℝ) (hd : 0<delta) (ha : 0<a) :
    delta^(-eta')*(delta^(2*eta'/a))^a=delta^eta' := by
  rw [← Real.rpow_mul hd.le,← Real.rpow_add hd]
  congr 1
  field_simp
  ring

/-- The densest-scale lower occupancy pays for the entire original inner
Frostman ball, with no lower bound transported to a restricted source. -/
theorem original_inner_ball_budget
    (Pts : Finset Point) (delta eta eta' rho t sigma s zeta m : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (hrho : 0<rho) (hrho1 : rho≤1)
    (ha : sigma ≤ t) (hsigma1 : sigma ≤ 1) (hm : 0 ≤ m)
    (heps : eta'≤zeta+sigma-s-eta)
    (hgain : delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m) :
    delta^(-eta)*rho^t*(Pts.card : ℝ)≤4*delta^eta'*m := by
  let F := delta^(zeta+sigma-s-eta)*rho^(t-sigma)
  have hF : 0≤F := by dsimp [F]; positivity
  have hdpow : delta^(zeta+sigma-s-eta)≤delta^eta' :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 heps
  have hrpow : rho^(t-sigma)≤1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hrho hrho1 (sub_nonneg.mpr ha)
  have hFbound : F≤delta^eta' := by
    calc
      _ ≤ delta^(zeta+sigma-s-eta)*1 :=
        mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ ≤ _ := by simpa only [mul_one] using hdpow
  have htwo : (2:ℝ)^(sigma+1)≤4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show sigma+1≤2 by linarith only [hsigma1])
    norm_num only [Real.rpow_two,show (2:ℝ)^2=4 by norm_num] at h
    exact h
  have hid : F*(delta^(s-sigma-zeta)*rho^sigma)=delta^(-eta)*rho^t := by
    dsimp [F]
    calc
      _ = (delta^(zeta+sigma-s-eta)*delta^(s-sigma-zeta))*(rho^(t-sigma)*rho^sigma) := by ring
      _ = _ := by rw [← Real.rpow_add hd,← Real.rpow_add hrho]; congr 2 <;> ring
  have hg := mul_le_mul_of_nonneg_left hgain hF
  rw [← mul_assoc,hid] at hg
  have hright : F*(2^(sigma+1)*m)≤4*delta^eta'*m := by
    have hprod := mul_le_mul hFbound htwo (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _) (by positivity)
    have hh := mul_le_mul_of_nonneg_right hprod hm
    nlinarith only [hh]
  exact hg.trans hright

/-- A fixed polynomial loss in the actual dyadic menu is absorbed by a
positive power of the original real scale. The cutoff is chosen before n. -/
theorem exists_original_menu_power_cutoff (C : ℝ) (_hC : 0≤C) {eta : ℝ} (heta : 0<eta) :
    ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧
      ∀ delta : ℝ, 0<delta → delta≤delta0 → ∀ n : ℕ,
        delta≤dyadicRadius n → dyadicRadius n≤2*delta →
        C*((n:ℝ)+5)*delta^eta≤1 := by
  let a : ℝ := Real.log 2*eta
  have ha : 0<a := mul_pos (Real.log_pos (by norm_num)) heta
  have hlim : Tendsto (fun n : ℕ =>
      Real.exp (a*((n:ℝ)+5))/((n:ℝ)+5)^(1:ℝ)) atTop atTop :=
    (tendsto_exp_mul_div_rpow_atTop 1 a ha).comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  obtain ⟨n0,hn0raw⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (eventually_ge_atTop (C*Real.exp (a*5))))
  have hn0 (n : ℕ) (hn : n0≤n) : C*((n:ℝ)+5)≤(2:ℝ)^(eta*(n:ℝ)) := by
    have hh := (le_div_iff₀ (Real.rpow_pos_of_pos
      (by positivity : (0:ℝ)<(n:ℝ)+5) 1)).mp (hn0raw n hn)
    rw [Real.rpow_one,
      show a*((n:ℝ)+5)=a*(n:ℝ)+a*5 by ring,Real.exp_add] at hh
    have hstep : C*((n:ℝ)+5)≤Real.exp (a*(n:ℝ)) := by
      apply (mul_le_mul_iff_left₀ (Real.exp_pos (a*5))).mp
      nlinarith only [hh]
    convert hstep using 1
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    congr 1
    dsimp [a]
    ring
  let delta0 := dyadicRadius n0/4
  have hqpos : 0<dyadicRadius n0 := by dsimp [dyadicRadius]; positivity
  have hqone : dyadicRadius n0≤1 :=
    pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num)
  refine ⟨delta0,by dsimp [delta0]; positivity,by dsimp [delta0]; linarith,?_⟩
  intro delta hd hsmall n hmesh hbottom
  have hnn : n0≤n := by
    by_contra hh
    have hle : n≤n0 := by omega
    have hq : dyadicRadius n0≤dyadicRadius n :=
      pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤1/2) (by norm_num) hle
    dsimp [delta0] at hsmall
    linarith only [hq,hbottom,hsmall,hqpos]
  have hbudget : C*((n:ℝ)+5)≤(2:ℝ)^(eta*(n:ℝ)) := by
    exact hn0 n hnn
  have hdq : delta^eta≤(dyadicRadius n)^eta := Real.rpow_le_rpow hd.le hmesh heta.le
  have hqid : (dyadicRadius n)^eta=(2:ℝ)^(-(eta*(n:ℝ))) := by
    simp only [dyadicRadius,one_div,inv_pow]
    rw [← Real.rpow_neg_eq_inv_rpow,
      ← Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  have hproduct := mul_le_mul hbudget hdq (Real.rpow_nonneg hd.le eta) (by positivity)
  rw [hqid,← Real.rpow_add (by norm_num : (0:ℝ)<2),add_neg_cancel,Real.rpow_zero] at hproduct
  exact hproduct

end NativeAnnularParameterBudget
