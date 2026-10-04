import Theorems.Thm_StickyKakeya4_gkz_original_linear_upper
import Theorems.Thm_StickyKakeya4_gkz_original_linear_expansion
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open Classical

namespace GKZOriginalSumProductComparison
open ActualRoundedAdditiveEnergy GKZOriginalRatioGap GKZOriginalGapEnergy
open GKZOriginalProductOverlap GKZOriginalLinearUpper GKZOriginalAnchorProfile
open GKZOriginalLinearExpansion GKZOriginalNineSumCover

private lemma gap_comparison {C D K sigma h e N I q : ℝ}
    (hC : 0 < C) (hD : 0 < D) (hK : 1 ≤ K) (hsigma1 : sigma ≤ 1) (hh : 0 ≤ h)
    (he : 0 < e) (hN : 0 < N)
    (hlo : q^2*e^sigma*N ≤ (2:ℝ)^sigma*K^2*h^sigma*I)
    (hhi : I ≤ C*K*e^sigma*D^36*N) :
    q^2 ≤ 2*C*K^3*h^sigma*D^36 := by
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hW : 0 < e^sigma*N := mul_pos (Real.rpow_pos_of_pos he sigma) hN
  have hmul := mul_le_mul_of_nonneg_left hhi
    (show 0 ≤ (2:ℝ)^sigma*K^2*h^sigma by positivity)
  have hchain := hlo.trans hmul
  have hn : q^2 ≤ (2:ℝ)^sigma*C*K^3*h^sigma*D^36 := by
    apply (mul_le_mul_iff_left₀ hW).mp
    nlinarith only [hchain]
  have htwo : (2:ℝ)^sigma ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hsigma1
  have hm := mul_le_mul_of_nonneg_right htwo
    (show 0 ≤ C*K^3*h^sigma*D^36 by positivity)
  nlinarith only [hn,hm]

private lemma dense_comparison {C D K sigma delta h s e N I q : ℝ}
    (hC : 0 < C) (hD : 0 < D) (hK : 1 ≤ K)
    (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1) (hd : 0 < delta) (hh : 0 ≤ h)
    (hs : 0 ≤ s) (he : 0 < e) (he1 : e ≤ 1) (hN : 0 < N)
    (hpop : delta^sigma*N=1)
    (hlo : q^2 ≤ (32*s+K^2*(2*delta/e)^sigma*h^sigma)*I)
    (hhi : I ≤ C*K*e^sigma*D^36*N) :
    q^2 ≤ C*K^3*D^36*(32*s*N+2*h^sigma) := by
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hratio : (2*delta/e)^sigma*e^sigma=(2:ℝ)^sigma*delta^sigma := by
    rw [Real.div_rpow (by positivity) he.le,
      div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos he sigma))]
    exact Real.mul_rpow (by norm_num) hd.le
  have hm := mul_le_mul_of_nonneg_left hhi
    (show 0 ≤ 32*s+K^2*(2*delta/e)^sigma*h^sigma by positivity)
  have hid : (32*s+K^2*(2*delta/e)^sigma*h^sigma)*(C*K*e^sigma*D^36*N)=
      32*s*C*K*D^36*N*e^sigma + C*K^3*D^36*h^sigma*(2:ℝ)^sigma := by
    calc
      _ = 32*s*C*K*D^36*N*e^sigma +
          (C*K^3*D^36*h^sigma)*((2*delta/e)^sigma*e^sigma)*N := by ring
      _ = 32*s*C*K*D^36*N*e^sigma +
          (C*K^3*D^36*h^sigma)*((2:ℝ)^sigma*delta^sigma)*N := by rw [hratio]
      _ = 32*s*C*K*D^36*N*e^sigma +
          (C*K^3*D^36*h^sigma*(2:ℝ)^sigma)*(delta^sigma*N) := by ring
      _ = _ := by rw [hpop,mul_one]
  rw [hid] at hm
  have hepow : e^sigma ≤ 1 := Real.rpow_le_one he.le he1 hsigma
  have hKpow : K ≤ K^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (show (1:ℕ) ≤ 3 by norm_num)
  have htwo : (2:ℝ)^sigma ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hsigma1
  have hfirst := mul_le_mul_of_nonneg_left hepow
    (show 0 ≤ 32*s*C*K*D^36*N by positivity)
  have hfirst' := mul_le_mul_of_nonneg_left hKpow
    (show 0 ≤ 32*s*C*D^36*N by positivity)
  have hsecond := mul_le_mul_of_nonneg_left htwo
    (show 0 ≤ C*K^3*D^36*h^sigma by positivity)
  nlinarith only [hlo.trans hm,hfirst,hfirst',hsecond]

/-- A genuine finite sum-product expansion inequality. Both original covers
drive the popular-dilate upper bound; the original ratio dichotomy drives the
lower bound. The distant-pair failure is handled as an explicit growth case. -/
theorem original_sum_product_comparison (A : Finset ℝ) (m : ℕ)
    {delta h D K sigma : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta) (hhlo : 2*delta ≤ h) (hhhi : h ≤ 1)
    (hD : 0 < D) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (hcard : (A.card : ℝ)=delta^(-sigma))
    (hbox : ∀ a∈A, 1 ≤ a ∧ a ≤ 2)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|)
    (hproduct : ((productCells delta A).card : ℝ) ≤ D*A.card)
    (hsum : (((A.product A).image (fun p => rounded delta (p.1+p.2))).card : ℝ) ≤ D*A.card)
    (hprofile : ScalarFrostman A delta K sigma)
    (hscale : delta ≤ ((2:ℝ)^m)⁻¹*h^2) :
    1 ≤ (128*upperConstant)*K^3*D^40*
      (((2:ℝ)^m)⁻¹*(A.card : ℝ)+h^sigma) := by
  let s : ℝ := ((2:ℝ)^m)⁻¹
  let q : ℝ := (1/D)^2/2
  have hs : 0 < s := by dsimp [s]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hN : 0 < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hh0 : 0 ≤ h := by linarith only [hd,hhlo]
  have hd1 : delta ≤ 1 := by linarith only [hhlo,hhhi,hd]
  have hK1 := original_profile_constant_ge_one A hA hd1 hbox hprofile
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK1
  have hC1 : 1 ≤ upperConstant := by norm_num [upperConstant]
  have hC : 0 < upperConstant := lt_of_lt_of_le (by norm_num) hC1
  have hD1 : 1 ≤ D := by
    have hc := (original_product_incidence_mass A hA hd
      (fun a ha => (hbox a ha).1) hsep).2.2
    have hcR : (A.card : ℝ) ≤ (productCells delta A).card := Nat.cast_le.mpr hc
    nlinarith only [hcR,hproduct,hN]
  have hqnorm : q^2*(4*D^4)=1 := by dsimp [q]; field_simp; norm_num
  have hqlinear : q*(2*D^2)=1 := by dsimp [q]; field_simp
  change 1 ≤ (128*upperConstant)*K^3*D^40*(s*(A.card : ℝ)+h^sigma)
  by_cases hsmall : K*h^sigma < q
  · obtain ⟨V,hVA,hVmass,hupper⟩ := exists_original_linear_image_upper A hA hd hd1
      hD hsigma hsigma1 hbox hsep hproduct hsum hprofile
    have hpop : delta^sigma*(A.card : ℝ)=1 := by
      rw [hcard,← Real.rpow_add hd,add_neg_cancel,Real.rpow_zero]
    rcases original_linear_expansion_alternative A V m hA hd hhlo hhhi hK0 hq hcard hVA
      hVmass (fun a ha => hbox a (hVA ha)) hprofile hsmall hscale with hgap | hdense
    · obtain ⟨e1,e2,hcoeff,helo,_hehi,hnorm,hgrow⟩ := hgap
      have hlo := hgrow V q (Finset.Subset.refl _) hq hVmass
      have hhi := hupper V e1 e2 (Finset.Subset.refl _)
        (gap_coefficients_are_expansion_coefficients V hcoeff) helo hnorm
      have he : 0 < |e2| := (by positivity : 0 < 2*delta).trans_le helo
      have hc := gap_comparison hC hD hK1 hsigma1 hh0 he hN hlo hhi
      have hscaled : 1 ≤ 8*upperConstant*K^3*D^40*h^sigma := by
        calc
          _ = q^2*(4*D^4) := hqnorm.symm
          _ ≤ (2*upperConstant*K^3*h^sigma*D^36)*(4*D^4) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
          _ = _ := by ring
      have hterm : 8*h^sigma ≤ 128*(s*(A.card : ℝ)+h^sigma) := by
        nlinarith only [show 0 ≤ s*(A.card : ℝ) by positivity, Real.rpow_nonneg hh0 sigma]
      have hm := mul_le_mul_of_nonneg_left hterm
        (show 0 ≤ upperConstant*K^3*D^40 by positivity)
      nlinarith only [hscaled,hm]
    · obtain ⟨x,hx,x',hx',y,hy,y',hy',hden,hdenhi,hr0,hr1,hlo⟩ := hdense
      have he : 0 < |y-y'| := (by linarith only [hd,hhlo] : 0 < h).trans hden
      have hratio : |(x-x')/(y-y')| ≤ 1 := abs_le.mpr ⟨by linarith only [hr0],hr1⟩
      rw [abs_div] at hratio
      have hnorm : |x-x'| ≤ |y-y'| := (div_le_one he).mp hratio
      have hhi := hupper V (x-x') (y-y') (Finset.Subset.refl _)
        (dense_coefficients_are_expansion_coefficients V hx hx' hy hy')
        (hhlo.trans hden.le) hnorm
      have hc := dense_comparison hC hD hK1 hsigma hsigma1 hd hh0 hs.le he hdenhi hN hpop hlo hhi
      have hscaled : 1 ≤ upperConstant*K^3*D^40*(128*s*(A.card : ℝ)+8*h^sigma) := by
        calc
          _ = q^2*(4*D^4) := hqnorm.symm
          _ ≤ (upperConstant*K^3*D^36*(32*s*(A.card : ℝ)+2*h^sigma))*(4*D^4) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
          _ = _ := by ring
      have hterm : 128*s*(A.card : ℝ)+8*h^sigma ≤ 128*(s*(A.card : ℝ)+h^sigma) := by
        nlinarith only [Real.rpow_nonneg hh0 sigma]
      have hm := mul_le_mul_of_nonneg_left hterm
        (show 0 ≤ upperConstant*K^3*D^40 by positivity)
      nlinarith only [hscaled,hm]
  · have hweak : q ≤ K*h^sigma := le_of_not_gt hsmall
    have hraw : 1 ≤ 2*K*D^2*h^sigma := by
      calc
        _ = q*(2*D^2) := hqlinear.symm
        _ ≤ (K*h^sigma)*(2*D^2) := mul_le_mul_of_nonneg_right hweak (by positivity)
        _ = _ := by ring
    have hKpow : K ≤ K^3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hK1 (show (1:ℕ) ≤ 3 by norm_num)
    have hDpow : D^2 ≤ D^40 := pow_le_pow_right₀ hD1 (by norm_num)
    have hfactor : (2:ℝ) ≤ 128*upperConstant := by nlinarith only [hC1]
    have hm1 : 2*K*D^2*h^sigma ≤ (128*upperConstant)*K^3*D^40*h^sigma := by
      gcongr
    have hm2 : (128*upperConstant)*K^3*D^40*h^sigma ≤
        (128*upperConstant)*K^3*D^40*(s*(A.card : ℝ)+h^sigma) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [show 0 ≤ s*(A.card : ℝ) by positivity]
    exact hraw.trans (hm1.trans hm2)

end GKZOriginalSumProductComparison
