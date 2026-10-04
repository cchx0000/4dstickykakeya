import Theorems.Thm_StickyKakeya4_original_weak_scalar_word_cost
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
noncomputable section

namespace OriginalWeakScalarPowerComparison
open OriginalWeakScalarWordCost

lemma original_zero_removal_power {delta eta u : ℝ} (hd : 0 < delta) (hu : 0 < u) :
    delta^(-eta)*(delta^(2*eta/u))^u=delta^eta := by
  rw [← Real.rpow_mul hd.le,div_mul_cancel₀ _ hu.ne',← Real.rpow_add hd]
  congr 1
  ring

/-- The same actual small cutoff that pays zero removal also absorbs the
factor two in both the retained profile and original coefficient diameter. -/
theorem original_profile_normalization_budget {delta eta kappa : ℝ}
    (hd : 0 < delta) (hkappa : 0 ≤ kappa) (hsmall : delta^eta ≤ 1/2) :
    (2*delta^(-eta))*(2*delta^(-eta))^kappa ≤ delta^(-(2*eta*(1+kappa))) := by
  have hid : delta^eta*delta^(-eta)=1 := by
    rw [← Real.rpow_add hd]
    simp only [add_neg_cancel,Real.rpow_zero]
  have hr : 2 ≤ delta^(-eta) := by
    have hh := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hd.le (-eta))
    nlinarith only [hh,hid]
  have hsq : 2*delta^(-eta) ≤ (delta^(-eta))^2 := by nlinarith only [hr]
  have hp := Real.rpow_le_rpow (show 0≤2*delta^(-eta) by positivity) hsq hkappa
  have hh := mul_le_mul hsq hp (Real.rpow_nonneg (by positivity : 0≤2*delta^(-eta)) kappa)
    (sq_nonneg _)
  have he : (delta^(-eta))^2=delta^(-2*eta) := by
    rw [← Real.rpow_mul_natCast hd.le]
    congr 1
    ring
  rw [he,← Real.rpow_mul hd.le,← Real.rpow_add hd] at hh
  have hexp : -2*eta+(-2*eta)*kappa= -(2*eta*(1+kappa)) := by ring
  simpa only [hexp] using hh

/-- Explicit power bounds for the already derived finite obstruction.
This is arithmetic on its actual source parameters, not an assumed gain. -/
theorem original_power_obstruction_upper (W d : ℕ)
    {delta epsilon eta zeta q u gap a g C N : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heps : 0 ≤ epsilon)
    (heta : 0 ≤ eta) (hzeta : 0 ≤ zeta) (hdim : 1 ≤ d)
    (hC : 0 < C) (hN : 0 ≤ N) (hNupper : N ≤ delta^(-1+gap))
    (hnear : 2*g ≤ q*u-eta-costExponent W d epsilon eta zeta)
    (hfar : 2*g ≤ gap-q-a-costExponent W d epsilon eta zeta) :
    wordCost W d (delta^(-eta)) (delta^zeta) (delta^(-epsilon))*
      (4*delta^(-eta)*(delta^q)^u+192*delta*N/(delta^q*C*delta^a)) ≤
      costConstant W d*(4+192/C)*delta^(2*g) := by
  let E := costExponent W d epsilon eta zeta
  have hcost := original_word_cost_power W d hd hd1 heps heta hzeta hdim
  have hden : 0 < delta^q*C*delta^a := by positivity
  have hNmul := mul_le_mul_of_nonneg_left hNupper (show 0≤192*delta by positivity)
  have hdiv := (div_le_div_iff_of_pos_right hden).mpr hNmul
  have hprod : delta*delta^(-1+gap)=delta^gap := by
    have hh := Real.rpow_add hd 1 (-1+gap)
    rw [Real.rpow_one] at hh
    simpa only [show (1:ℝ)+(-1+gap)=gap by ring] using hh.symm
  have hfarEq : 192*delta*delta^(-1+gap)/(delta^q*C*delta^a)=
      (192/C)*delta^(gap-q-a) := by
    calc
      _ = (192/C)*((delta*delta^(-1+gap))/(delta^q*delta^a)) := by
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      _ = (192/C)*(delta^gap/delta^(q+a)) := by rw [hprod,← Real.rpow_add hd]
      _ = _ := by
        rw [← Real.rpow_sub hd]
        congr 1
        ring
  rw [hfarEq] at hdiv
  have hB : 0 ≤ 4*delta^(-eta)*(delta^q)^u+192*delta*N/(delta^q*C*delta^a) := by positivity
  have htop : 0 ≤ costConstant W d*delta^(-E) := by
    exact mul_nonneg (costConstant_pos W d).le (Real.rpow_nonneg hd.le _)
  have hbase := mul_le_mul hcost (add_le_add (le_refl (4*delta^(-eta)*(delta^q)^u)) hdiv) hB htop
  have hnEq : delta^(-E)*(4*delta^(-eta)*(delta^q)^u)=4*delta^(q*u-eta-E) := by
    rw [← Real.rpow_mul hd.le]
    calc
      _ = 4*(delta^(-E)*(delta^(-eta)*delta^(q*u))) := by ring
      _ = _ := by
        rw [← Real.rpow_add hd,← Real.rpow_add hd]
        congr 1
        ring
  have hfEq : delta^(-E)*((192/C)*delta^(gap-q-a))=(192/C)*delta^(gap-q-a-E) := by
    calc
      _ = (192/C)*(delta^(-E)*delta^(gap-q-a)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hd]
        congr 1
        ring
  have hbaseEq : (costConstant W d*delta^(-E))*
      (4*delta^(-eta)*(delta^q)^u+(192/C)*delta^(gap-q-a)) =
      costConstant W d*(4*delta^(q*u-eta-E)+(192/C)*delta^(gap-q-a-E)) := by
    rw [mul_assoc,mul_add,hnEq,hfEq]
  rw [hbaseEq] at hbase
  have hn := Real.rpow_le_rpow_of_exponent_ge hd hd1 hnear
  have hf := Real.rpow_le_rpow_of_exponent_ge hd hd1 hfar
  have hn' := mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ)≤4)
  have hf' := mul_le_mul_of_nonneg_left hf (show 0≤192/C by positivity)
  have hs := mul_le_mul_of_nonneg_left (add_le_add hn' hf') (costConstant_pos W d).le
  exact hbase.trans (by nlinarith only [hs])

end OriginalWeakScalarPowerComparison
