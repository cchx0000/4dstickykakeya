import Theorems.Thm_StickyKakeya4_original_representative_shading
import Theorems.Thm_StickyKakeya4_original_retained_tube_ball_profile
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
namespace OriginalShadingCenterProfile
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open NativeRadialClassPruning OriginalRepresentativeShading OriginalRetainedTubeBallProfile
open OriginalPhysicalTubeScaleSelection OriginalAnnularRowCover OriginalAnnularGraphDeletion
open OriginalAnnularOffRootMass OriginalDensestTubeControl

def shadingCoefficient (n : ℕ) (delta eta' tau0 : ℝ) : ℝ :=
  ((n:ℝ)+5)*delta^(-eta')/tau0^2

/-- Every actual shaded center has the original annular ball bound, via
its actual original partner line and surviving original annuli. -/
theorem original_shaded_center_ball_count
    (Pts : Finset Point) (G : Finset Pair) (n : ℕ) (z : Pair) (p : Point)
    (delta eta eta' t sigma s zeta rho m w tau0 R : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (ha : sigma≤t) (hsigma1 : sigma≤1)
    (hm : 0 ≤ m) (hrho : rho∈scaleMenu n) (hquery : delta≤rho)
    (hRlow : rho≤R) (hRhigh : R≤tau0) (htop : tau0≤1)
    (hwidth : 24*rho≤w) (heps : -eta'≤zeta+sigma-s-eta)
    (hGP : G⊆Pts.product Pts) (hbox : ∀ x∈Pts, |x.1|≤1 ∧ |x.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2)
    (hgain : delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m)
    (hfrostman : ∀ q∈Pts, ∀ L : ℝ, delta≤L → L≤1 →
      ((Pts.filter (fun v => euclideanDistance q v≤L)).card : ℝ)≤delta^(-eta)*L^t*Pts.card)
    (hann : ∀ u∈G, ∀ tau∈annularScales n rho tau0,
      ((annularSupport Pts u.1 u.2 w tau).card : ℝ)<delta^(-eta')*tau^(t-sigma)*m ∧
      ((annularSupport Pts u.2 u.1 w tau).card : ℝ)<delta^(-eta')*tau^(t-sigma)*m)
    (hp : p∈originalShading Pts G rho z) :
    (((originalShading Pts G rho z).filter (fun q => euclideanDistance p q≤R)).card : ℝ)≤
      ((n:ℝ)+5)*delta^(-eta')*R^(t-sigma)*m := by
  obtain ⟨q,hqG,hsupport⟩ := original_shading_center_tube_witness
    Pts G rho z p hGP hbox hdistinct hp
  have hret : (p,q)∈retainedAnnularGraph Pts G (annularScales n rho tau0) w
      (fun tau => delta^(-eta')*tau^(t-sigma)*m) :=
    Finset.mem_filter.mpr ⟨hqG,hann (p,q) hqG⟩
  have hball := (retained_original_wide_tube_ball_profile Pts G n (p,q)
    delta eta eta' t sigma s zeta rho m w tau0 R hd hd1 ha hsigma1 hm hrho hquery
    hRlow hRhigh htop heps (hGP hqG) hgain hfrostman hret).1
  have hsub : (originalShading Pts G rho z).filter (fun q => euclideanDistance p q≤R)⊆
      (physicalPairTube Pts w (p,q)).filter (fun q => euclideanDistance p q≤R) := by
    intro x hx
    obtain ⟨hxY,hxR⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨physical_tube_mono Pts (p,q) hwidth (hsupport hxY),hxR⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hball

private theorem large_radius_coefficient (n : ℕ) (delta eta' tau0 b R : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (heta' : 0≤eta')
    (htau : 0<tau0) (htau1 : tau0≤1) (hb : 0≤b) (hb1 : b≤1) (hR : tau0≤R) :
    1≤shadingCoefficient n delta eta' tau0*R^b := by
  have hdp : 1≤delta^(-eta') := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hd hd1
      (show -eta'≤0 by linarith)
  have hA : 1≤((n:ℝ)+5)*delta^(-eta') := by nlinarith [show (0:ℝ)≤n by positivity]
  have htaupow : tau0^2≤tau0^b := by
    have hh := Real.rpow_le_rpow_of_exponent_ge htau htau1 (show b≤2 by linarith)
    simpa only [Real.rpow_two] using hh
  have hRpow : tau0^b≤R^b := Real.rpow_le_rpow htau.le hR hb
  have hnumer : tau0^2≤((n:ℝ)+5)*delta^(-eta')*R^b := by
    have hh := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (htau.le.trans hR) b)
    nlinarith only [hh,htaupow,hRpow]
  unfold shadingCoefficient
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (sq_pos_of_pos htau)).mpr (by simpa only [one_mul] using hnumer)

/-- Normalization uses the actual reverse-class root mass. Radii above
tau0 use total original shading mass, so every R≥rho is covered. -/
theorem original_shaded_center_frostman
    (Pts : Finset Point) (G : Finset Pair) (n : ℕ) (z : Pair) (p : Point)
    (delta eta eta' t sigma s zeta rho m w tau0 R : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (heta' : 0≤eta')
    (ha : sigma≤t) (hsigma1 : sigma≤1) (hm : 0 ≤ m)
    (hrho : rho∈scaleMenu n) (hquery : delta≤rho)
    (htau : 0<tau0) (htop : tau0≤1) (hRlow : rho≤R)
    (hwidth : 24*rho≤w) (heps : -eta'≤zeta+sigma-s-eta)
    (hz : z∈G) (hGP : G⊆Pts.product Pts)
    (hbox : ∀ x∈Pts, |x.1|≤1 ∧ |x.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2)
    (hgain : delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m)
    (hfrostman : ∀ q∈Pts, ∀ L : ℝ, delta≤L → L≤1 →
      ((Pts.filter (fun v => euclideanDistance q v≤L)).card : ℝ)≤delta^(-eta)*L^t*Pts.card)
    (hann : ∀ u∈G, ∀ tau∈annularScales n rho tau0,
      ((annularSupport Pts u.1 u.2 w tau).card : ℝ)<delta^(-eta')*tau^(t-sigma)*m ∧
      ((annularSupport Pts u.2 u.1 w tau).card : ℝ)<delta^(-eta')*tau^(t-sigma)*m)
    (hreverse : tau0^2*m≤((G.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ))
    (hp : p∈originalShading Pts G rho z) :
    (((originalShading Pts G rho z).filter (fun q => euclideanDistance p q≤R)).card : ℝ)≤
      shadingCoefficient n delta eta' tau0*R^(min (t-sigma) 1)*(originalShading Pts G rho z).card := by
  have hrhop := ((scale_menu_bounds n).2.2 rho hrho).1
  have hRp : 0<R := hrhop.trans_le hRlow
  have hb : 0≤min (t-sigma) 1 := le_min (sub_nonneg.mpr ha) (by norm_num)
  have hb1 : min (t-sigma) 1≤1 := min_le_right _ _
  by_cases hsmall : R≤tau0
  · have hball := original_shaded_center_ball_count Pts G n z p delta eta eta' t sigma s zeta
      rho m w tau0 R hd hd1 ha hsigma1 hm hrho hquery hRlow hsmall htop hwidth heps
      hGP hbox hdistinct hgain hfrostman hann hp
    have hmass : tau0^2*m≤((originalShading Pts G rho z).card : ℝ) := by
      have hh := original_representative_shading_lower Pts G rho (tau0^2*m/2) z hrhop hz
        hGP hbox hdistinct (by nlinarith only [hreverse])
      nlinarith only [hh]
    have hpow : R^(t-sigma)≤R^(min (t-sigma) 1) :=
      Real.rpow_le_rpow_of_exponent_ge hRp (hsmall.trans htop) (min_le_left _ _)
    have hfactor : 0≤shadingCoefficient n delta eta' tau0*R^(min (t-sigma) 1) := by
      dsimp [shadingCoefficient]; positivity
    calc
      _ ≤ ((n:ℝ)+5)*delta^(-eta')*R^(t-sigma)*m := hball
      _ ≤ ((n:ℝ)+5)*delta^(-eta')*R^(min (t-sigma) 1)*m := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by positivity)) hm
      _ = (shadingCoefficient n delta eta' tau0*R^(min (t-sigma) 1))*(tau0^2*m) := by
        dsimp [shadingCoefficient]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass hfactor
  · have hfac := large_radius_coefficient n delta eta' tau0 (min (t-sigma) 1) R
      hd hd1 heta' htau htop hb hb1 (le_of_not_ge hsmall)
    have hcard : (((originalShading Pts G rho z).filter
        (fun q => euclideanDistance p q≤R)).card : ℝ)≤(originalShading Pts G rho z).card :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
    exact hcard.trans (by
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right hfac
        (Nat.cast_nonneg (originalShading Pts G rho z).card)))

/-- The coefficient is legal for the existing coarse-shading engine. -/
theorem original_shading_coefficient_one_le (n : ℕ) (delta eta' tau0 : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (heta' : 0≤eta') (htau : 0<tau0) (htau1 : tau0≤1) :
    1≤shadingCoefficient n delta eta' tau0 := by
  have hh := large_radius_coefficient n delta eta' tau0 0 1
    hd hd1 heta' htau htau1 (by norm_num) (by norm_num) htau1
  simpa only [Real.rpow_zero,mul_one] using hh

end OriginalShadingCenterProfile
