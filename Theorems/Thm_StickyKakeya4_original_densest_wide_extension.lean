import Theorems.Thm_StickyKakeya4_original_densest_tube_control
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace OriginalDensestWideExtension
open OriginalPairStripGeometry OriginalPhysicalPairTube
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl

/-- Clip widths above one with the proved full-original-P density. -/
theorem original_all_larger_width_control
    (Pts : Finset Point) (z : Pair) (sigma rho R m : ℝ)
    (hsigma : 0≤sigma) (hm : 0≤m) (hrhopos : 0<rho)
    (hlocal : ∀ R : ℝ, rho≤R → R≤1 →
      ((physicalPairTube Pts R z).card : ℝ)≤2^(sigma+1)*(R/rho)^sigma*m)
    (hsource : rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m)
    (hRlow : rho≤R) :
    ((physicalPairTube Pts R z).card : ℝ)≤2^(sigma+1)*(R/rho)^sigma*m := by
  classical
  have hRpos : 0<R := hrhopos.trans_le hRlow
  by_cases hRhigh : R≤1
  · exact hlocal R hRlow hRhigh
  · have hRone : 1≤R := (lt_of_not_ge hRhigh).le
    have hpow : 1≤R^sigma := by
      have h := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1) hRone hsigma
      simpa only [Real.one_rpow] using h
    have hcard : ((physicalPairTube Pts R z).card : ℝ)≤Pts.card :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
    calc
      _ ≤ (Pts.card : ℝ) := hcard
      _ ≤ 2^(sigma+1)*m/rho^sigma :=
        (le_div_iff₀ (Real.rpow_pos_of_pos hrhopos sigma)).mpr (by nlinarith only [hsource])
      _ ≤ 2^(sigma+1)*m*R^sigma/rho^sigma := by
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hrhopos.le sigma)
        have h := mul_le_mul_of_nonneg_left hpow (show 0≤(2:ℝ)^(sigma+1)*m by positivity)
        simpa only [mul_one] using h
      _ = _ := by rw [Real.div_rpow hRpos.le hrhopos.le]; ring

theorem original_source_density_of_native_gain
    (Pts : Finset Point) (delta sigma s zeta rho m : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (hrho : 0≤rho) (hgap : s-sigma≤zeta)
    (hgain : delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m) :
    rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m := by
  have hp := Real.rpow_le_rpow_of_exponent_ge hd hd1
    (show s-sigma-zeta≤0 by linarith only [hgap])
  rw [Real.rpow_zero] at hp
  have hh := mul_le_mul_of_nonneg_right hp
    (mul_nonneg (Real.rpow_nonneg hrho sigma) (Nat.cast_nonneg Pts.card))
  nlinarith only [hh,hgain]
end OriginalDensestWideExtension
