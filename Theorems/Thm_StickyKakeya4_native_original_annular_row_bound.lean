import Theorems.Thm_StickyKakeya4_original_annular_row_charge
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace NativeOriginalAnnularRowBound
open OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl
open OriginalAnnularRowCover OriginalAnnularRowCharge

/-- Exact cancellation of original annular exponents, keeping all geometric
constants and both original error parameters. -/
theorem annular_power_identity (delta r rho tau t sigma m eta eta' : ℝ)
    (hd : 0<delta) (hr : 0<r) (hrho : 0<rho) (htau : 0<tau) :
    (2^(sigma+1)*((38*(r^(-3:ℝ)*rho)/tau)/rho)^sigma*m)*
        (delta^(-eta)*(2*tau)^t) =
      (delta^(-eta')*tau^(t-sigma)*m)*
        (2^(sigma+1)*38^sigma*2^t*r^(-3*sigma)*delta^(eta'-eta)) := by
  have hwidth : (38*(r^(-3:ℝ)*rho)/tau)/rho=38*r^(-3:ℝ)/tau := by field_simp
  have htpow : tau^t=tau^(t-sigma)*tau^sigma := by
    rw [← Real.rpow_add htau,sub_add_cancel]
  have hdpow : delta^(-eta)=delta^(-eta')*delta^(eta'-eta) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  rw [hwidth,Real.div_rpow (by positivity : (0:ℝ)≤38*r^(-3:ℝ)) htau.le,
    Real.mul_rpow (by norm_num : (0:ℝ)≤38) (Real.rpow_nonneg hr.le _),
    ← Real.rpow_mul hr.le,Real.mul_rpow (by norm_num : (0:ℝ)≤2) htau.le,
    htpow,hdpow]
  field_simp

/-- Native source (223) from ORIGINAL Frostman data and the actual original
G2 maximum-density profile. The bad row is constructed by its actual rich
annular support test. Maximal disjoint annular supports replace angular
rectangles, yielding the stronger r^(-3sigma) loss with an explicit 608. -/
theorem native_original_annular_bad_row
    (Pts : Finset Point) (G : Finset Pair) (p : Point) (n : ℕ)
    (delta eta eta' t sigma rho m r tau : ℝ)
    (hd : 0<delta) (ht2 : t≤2) (hsigma : 0≤sigma) (hsigma1 : sigma≤1)
    (hm : 0<m) (hr : 0<r) (hr1 : r≤1) (htau : 0<tau) (htauhalf : tau≤1/2)
    (hquerylow : delta≤2*tau) (hrho : rho∈scaleMenu n)
    (hpP : p∈Pts) (hbox : ∀ z∈Pts, |z.1|≤1 ∧ |z.2|≤1)
    (hdistinct : ∀ z∈G, z.1≠z.2)
    (hlocal : ∀ z∈G, ∀ R : ℝ, rho≤R → R≤1 →
      ((physicalPairTube Pts R z).card : ℝ)≤2^(sigma+1)*(R/rho)^sigma*m)
    (hsource : rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m)
    (hfrostman : ∀ q∈Pts, ∀ R : ℝ, delta≤R → R≤1 →
      ((Pts.filter (fun v => euclideanDistance q v≤R)).card : ℝ)≤delta^(-eta)*R^t*Pts.card) :
    ((badPartners Pts G p (r^(-3:ℝ)*rho) tau
      (delta^(-eta')*tau^(t-sigma)*m)).card : ℝ)≤
      608*r^(-3*sigma)*delta^(eta'-eta)*Pts.card := by
  have hrhopos := ((scale_menu_bounds n).2.2 rho hrho).1
  have htau1 : tau≤1 := by linarith only [htauhalf]
  have hrpow : 1≤r^(-3:ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num : (-3:ℝ)≤0)
    simpa only [Real.rpow_zero] using h
  have hwidth : rho≤38*(r^(-3:ℝ)*rho)/tau := by
    apply (le_div_iff₀ htau).mpr
    have h1 := mul_le_mul_of_nonneg_right hrpow hrhopos.le
    have h2 := mul_le_mul_of_nonneg_left htau1 hrhopos.le
    nlinarith only [h1,h2,hrhopos]
  have hH : 0<delta^(-eta')*tau^(t-sigma)*m := by positivity
  have hbound := original_annular_row_frostman_charge Pts G p n delta eta t sigma rho m
    (r^(-3:ℝ)*rho) tau (delta^(-eta')*tau^(t-sigma)*m)
    hd hsigma hm.le (by positivity) htau htau1 hH hquerylow (by linarith only [htauhalf])
    hrho hwidth hpP hbox hdistinct hlocal hsource hfrostman
  have hid := annular_power_identity delta r rho tau t sigma m eta eta' hd hr hrhopos htau
  have hbound' : ((badPartners Pts G p (r^(-3:ℝ)*rho) tau
      (delta^(-eta')*tau^(t-sigma)*m)).card : ℝ)≤
      (2^(sigma+1)*38^sigma*2^t*r^(-3*sigma)*delta^(eta'-eta))*Pts.card := by
    apply (mul_le_mul_iff_of_pos_left hH).mp
    calc
      _ ≤ _ := hbound
      _ = _ := by rw [← mul_assoc,hid]; ring
  have h2s : (2:ℝ)^(sigma+1)≤4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show sigma+1≤2 by linarith only [hsigma1])
    norm_num only [Real.rpow_two,show (2:ℝ)^2=4 by norm_num] at h
    exact h
  have h38 : (38:ℝ)^sigma≤38 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤38) hsigma1
    simpa only [Real.rpow_one] using h
  have h2t : (2:ℝ)^t≤4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) ht2
    norm_num only [Real.rpow_two,show (2:ℝ)^2=4 by norm_num] at h
    exact h
  have hc : (2:ℝ)^(sigma+1)*38^sigma*2^t≤608 := by
    have h1 := mul_le_mul h2s h38 (Real.rpow_nonneg (by norm_num : (0:ℝ)≤38) sigma) (by norm_num : (0:ℝ)≤4)
    have h2 := mul_le_mul h1 h2t (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) t) (by norm_num : (0:ℝ)≤4*38)
    norm_num only [show (4:ℝ)*38*4=608 by norm_num] at h2
    exact h2
  have htotal := mul_le_mul_of_nonneg_right hc
    (show 0≤r^(-3*sigma)*delta^(eta'-eta)*(Pts.card : ℝ) by positivity)
  nlinarith only [hbound',htotal]

end NativeOriginalAnnularRowBound
