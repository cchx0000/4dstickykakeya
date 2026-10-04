import Theorems.Thm_StickyKakeya4_gkz_original_sum_product_comparison
import Theorems.Thm_StickyKakeya4_gkz_balanced_dyadic_scale
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open Classical

namespace GKZOriginalPositivePower
open ActualRoundedAdditiveEnergy GKZOriginalGapEnergy GKZOriginalProductOverlap
open GKZOriginalLinearUpper GKZOriginalAnchorProfile GKZOriginalSumProductComparison
open GKZBalancedDyadicScale

def gainConstant : ℝ := 384*upperConstant
def growthExponent (sigma : ℝ) : ℝ := gainPower sigma/40
def growthConstant (K : ℝ) : ℝ := (gainConstant*K^3)^(-(1/40:ℝ))
def sumCells (delta : ℝ) (A : Finset ℝ) : Finset ℤ :=
  (A.product A).image (fun p => rounded delta (p.1+p.2))

lemma growthExponent_pos {sigma : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma < 1) :
    0 < growthExponent sigma := div_pos (gainPower_pos hsigma hsigma1) (by norm_num)

lemma growthExponent_formula (sigma : ℝ) :
    growthExponent sigma=sigma*(1-sigma)/(40*(2+sigma)) := by
  unfold growthExponent gainPower gamma
  by_cases hden : 2+sigma=0
  · simp [hden]
  · field_simp [hden]

lemma growthConstant_pos {K : ℝ} (hK : 0 < K) : 0 < growthConstant K := by
  have hC : 0 < gainConstant := by norm_num [gainConstant,upperConstant]
  exact Real.rpow_pos_of_pos (mul_pos hC (pow_pos hK 3)) _

/-- A genuine positive power follows from the original finite covers and
profile, with a uniform mesh range and explicit polynomial losses. -/
theorem original_sum_product_positive_power (A : Finset ℝ) {delta D K sigma : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta) (hdquarter : delta ≤ 1/4)
    (hD : 0 < D) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hcard : (A.card : ℝ)=delta^(-sigma))
    (hbox : ∀ a∈A, 1 ≤ a ∧ a ≤ 2)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|)
    (hproduct : ((productCells delta A).card : ℝ) ≤ D*A.card)
    (hsum : ((sumCells delta A).card : ℝ) ≤ D*A.card)
    (hprofile : ScalarFrostman A delta K sigma) :
    1 ≤ gainConstant*K^3*D^40*delta^(gainPower sigma) := by
  obtain ⟨m,hhlo,hhhi,hscale,hbalance⟩ := exists_balanced_dyadic_scale
    hd hdquarter hsigma hsigma1
  have hc := original_sum_product_comparison A m hA hd hhlo hhhi hD
    hsigma.le hsigma1.le hcard hbox hsep hproduct hsum hprofile hscale
  have hK1 := original_profile_constant_ge_one A hA (by linarith only [hdquarter]) hbox hprofile
  have hK : 0 ≤ K := le_trans (by norm_num) hK1
  have hC : 0 ≤ upperConstant := by norm_num [upperConstant]
  rw [hcard] at hc
  have hm := mul_le_mul_of_nonneg_left hbalance
    (show 0 ≤ (128*upperConstant)*K^3*D^40 by positivity)
  unfold gainConstant
  nlinarith only [hc,hm]

/-- The fortieth-root form makes the positive mesh exponent explicit. -/
theorem original_sum_product_growth (A : Finset ℝ) {delta D K sigma : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta) (hdquarter : delta ≤ 1/4)
    (hD : 0 < D) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hcard : (A.card : ℝ)=delta^(-sigma))
    (hbox : ∀ a∈A, 1 ≤ a ∧ a ≤ 2)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|)
    (hproduct : ((productCells delta A).card : ℝ) ≤ D*A.card)
    (hsum : ((sumCells delta A).card : ℝ) ≤ D*A.card)
    (hprofile : ScalarFrostman A delta K sigma) :
    growthConstant K*delta^(-growthExponent sigma) ≤ D := by
  have hc := original_sum_product_positive_power A hA hd hdquarter hD hsigma hsigma1
    hcard hbox hsep hproduct hsum hprofile
  have hK1 := original_profile_constant_ge_one A hA (by linarith only [hdquarter]) hbox hprofile
  have hK : 0 < K := lt_of_lt_of_le (by norm_num) hK1
  have hC : 0 < gainConstant := by norm_num [gainConstant,upperConstant]
  have hden : 0 < gainConstant*K^3*delta^(gainPower sigma) := by positivity
  have hinv : (gainConstant*K^3*delta^(gainPower sigma))⁻¹ ≤ D^40 := by
    rw [← one_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hc]
  have hroot := Real.rpow_le_rpow (inv_nonneg.mpr hden.le) hinv
    (by norm_num : (0:ℝ) ≤ 1/40)
  have hDroot : (D^40)^(1/40:ℝ)=D := by
    rw [← Real.rpow_natCast_mul hD.le 40 (1/40:ℝ)]
    norm_num
  rw [hDroot] at hroot
  have hfactor : ((gainConstant*K^3*delta^(gainPower sigma))⁻¹)^(1/40:ℝ)=
      growthConstant K*delta^(-growthExponent sigma) := by
    rw [← Real.rpow_neg_eq_inv_rpow]
    rw [Real.mul_rpow (show 0 ≤ gainConstant*K^3 by positivity)
      (Real.rpow_nonneg hd.le (gainPower sigma))]
    rw [← Real.rpow_mul hd.le]
    unfold growthConstant growthExponent
    congr 2
    ring
  rw [hfactor] at hroot
  exact hroot

/-- An unconditional discretized scalar sum-product gain for the actual
original occupied cells. No small-image, energy, or projection certificate
appears among the hypotheses. -/
theorem original_occupied_sum_product_growth (A : Finset ℝ) {delta K sigma : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta) (hdquarter : delta ≤ 1/4)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hcard : (A.card : ℝ)=delta^(-sigma))
    (hbox : ∀ a∈A, 1 ≤ a ∧ a ≤ 2)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|)
    (hprofile : ScalarFrostman A delta K sigma) :
    growthConstant K*delta^(-growthExponent sigma)*A.card ≤
      ((sumCells delta A).card : ℝ)+(productCells delta A).card := by
  let T : ℝ := ((sumCells delta A).card : ℝ)+(productCells delta A).card
  let D : ℝ := T/A.card
  have hN : 0 < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hprod : ((productCells delta A).card : ℝ) ≤ T := by
    dsimp [T]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hsum : ((sumCells delta A).card : ℝ) ≤ T := by
    dsimp [T]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hT : 0 < T := by
    have hc := (original_product_incidence_mass A hA hd
      (fun a ha => (hbox a ha).1) hsep).2.2
    have hcR : (A.card : ℝ) ≤ (productCells delta A).card := Nat.cast_le.mpr hc
    exact hN.trans_le (hcR.trans hprod)
  have hD : 0 < D := div_pos hT hN
  have hnorm : D*(A.card : ℝ)=T := div_mul_cancel₀ _ (ne_of_gt hN)
  have hg := original_sum_product_growth A hA hd hdquarter hD hsigma hsigma1 hcard hbox hsep
    (by rw [hnorm]; exact hprod) (by rw [hnorm]; exact hsum) hprofile
  have hm := mul_le_mul_of_nonneg_right hg hN.le
  rw [hnorm] at hm
  exact hm

end GKZOriginalPositivePower
