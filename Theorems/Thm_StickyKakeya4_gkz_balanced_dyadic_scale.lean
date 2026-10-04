import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section

namespace GKZBalancedDyadicScale

def gamma (sigma : ℝ) : ℝ := (1-sigma)/(2+sigma)
def gainPower (sigma : ℝ) : ℝ := gamma sigma*sigma

lemma gamma_bounds {sigma : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma < 1) :
    0 < gamma sigma ∧ gamma sigma*2 < 1 := by
  have hden : 0 < 2+sigma := by linarith only [hsigma]
  constructor
  · exact div_pos (sub_pos.mpr hsigma1) hden
  · have hh : gamma sigma < 1/2 := by
      unfold gamma
      apply (div_lt_iff₀ hden).mpr
      linarith only [hsigma]
    linarith only [hh]

lemma gainPower_pos {sigma : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma < 1) :
    0 < gainPower sigma := mul_pos (gamma_bounds hsigma hsigma1).1 hsigma

/-- Choose the actual dyadic ratio scale and balance both terms of the
finite original sum-product comparison with one positive power of delta. -/
theorem exists_balanced_dyadic_scale {delta sigma : ℝ}
    (hd : 0 < delta) (hdquarter : delta ≤ 1/4)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) :
    ∃ m : ℕ,
      2*delta ≤ delta^(gamma sigma) ∧ delta^(gamma sigma) ≤ 1 ∧
      delta ≤ ((2:ℝ)^m)⁻¹*(delta^(gamma sigma))^2 ∧
      ((2:ℝ)^m)⁻¹*delta^(-sigma)+(delta^(gamma sigma))^sigma ≤
        3*delta^(gainPower sigma) := by
  have hd1 : delta ≤ 1 := by linarith only [hdquarter]
  obtain ⟨hgpos,hgsmall⟩ := gamma_bounds hsigma hsigma1
  let h : ℝ := delta^(gamma sigma)
  have hhpos : 0 < h := Real.rpow_pos_of_pos hd _
  have hhne : h≠0 := ne_of_gt hhpos
  have hhhi : h ≤ 1 := Real.rpow_le_one hd.le hd1 hgpos.le
  have hhpow : h^2=delta^(gamma sigma*2) := by
    rw [Real.rpow_mul hd.le, Real.rpow_two]
  have hdh : delta ≤ h^2 := by
    rw [hhpow]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hd hd1 hgsmall.le
  have hhlo : 2*delta ≤ h := by
    have hm := mul_le_mul_of_nonneg_right hdquarter hd.le
    nlinarith only [hdh,hm,hhpos.le,hd.le]
  let x : ℝ := delta/h^2
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := (div_le_one (sq_pos_of_pos hhpos)).mpr hdh
  obtain ⟨m,hmlo,hmhi⟩ := exists_nat_pow_near_of_lt_one hx hx1
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  have hpow (j : ℕ) : (1/2:ℝ)^j=((2:ℝ)^j)⁻¹ := by simp only [one_div,inv_pow]
  let s : ℝ := ((2:ℝ)^m)⁻¹
  have hslo : x ≤ s := by simpa only [hpow] using hmhi
  have hshi : s ≤ 2*x := by
    rw [pow_succ,hpow] at hmlo
    change s*(1/2:ℝ) < x at hmlo
    linarith only [hmlo]
  have hscale : delta ≤ s*h^2 := by
    have hm := mul_le_mul_of_nonneg_right hslo (sq_nonneg h)
    have hid : x*h^2=delta := by dsimp [x]; field_simp
    simpa only [hid] using hm
  have hexp : gamma sigma*2+gainPower sigma=1-sigma := by
    dsimp [gainPower,gamma]
    have hden : 2+sigma≠0 := ne_of_gt (by linarith only [hsigma] : 0 < 2+sigma)
    field_simp
  have hidentity : h^2*delta^(gainPower sigma)=delta*delta^(-sigma) := by
    calc
      _ = delta^(gamma sigma*2+gainPower sigma) := by rw [hhpow,← Real.rpow_add hd]
      _ = delta^(1-sigma) := by rw [hexp]
      _ = delta^(1+(-sigma)) := by rfl
      _ = delta^(1:ℝ)*delta^(-sigma) := Real.rpow_add hd _ _
      _ = _ := by rw [Real.rpow_one]
  have herr : s*delta^(-sigma) ≤ 2*delta^(gainPower sigma) := by
    have hm := mul_le_mul_of_nonneg_right hshi (Real.rpow_nonneg hd.le (-sigma))
    have hid : (2*x)*delta^(-sigma)=2*delta^(gainPower sigma) := by
      calc
        _ = (2*(delta*delta^(-sigma)))/h^2 := by dsimp [x]; ring
        _ = (2*(h^2*delta^(gainPower sigma)))/h^2 := by rw [← hidentity]
        _ = _ := by field_simp
    exact hm.trans_eq hid
  have hhgain : h^sigma=delta^(gainPower sigma) :=
    (Real.rpow_mul hd.le (gamma sigma) sigma).symm
  refine ⟨m,hhlo,hhhi,hscale,?_⟩
  change s*delta^(-sigma)+h^sigma ≤ 3*delta^(gainPower sigma)
  rw [hhgain]
  linarith only [herr]

end GKZBalancedDyadicScale
