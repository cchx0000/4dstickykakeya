import Theorems.Thm_StickyKakeya4_gkz_original_nine_sum_cover
import Theorems.Thm_StickyKakeya4_gkz_original_anchor_profile
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace GKZOriginalLinearUpper
open ActualRoundedAdditiveEnergy GKZOriginalRatioGap GKZOriginalGapEnergy
open GKZOriginalProductOverlap GKZOriginalNineSumCover GKZOriginalAnchorProfile

def upperConstant : ℝ := 252*(110592:ℝ)^9

/-- The full original finite input produces a popular carrier and actual
denominator-sensitive linear-image upper bounds. No mixed-sum or expansion
certificate is assumed: the original covers drive the entire construction. -/
theorem exists_original_linear_image_upper (A : Finset ℝ)
    {delta D K sigma : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hD : 0 < D) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (hbox : ∀ a∈A, 1 ≤ a ∧ a ≤ 2)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|)
    (hproduct : ((productCells delta A).card : ℝ) ≤ D*A.card)
    (hsum : (((A.product A).image (fun p => rounded delta (p.1+p.2))).card : ℝ) ≤ D*A.card)
    (hprofile : ScalarFrostman A delta K sigma) :
    ∃ V : Finset ℝ, V ⊆ A ∧ ((1/D)^2/2)*(A.card : ℝ) ≤ V.card ∧
      ∀ (A1 : Finset ℝ) (e1 e2 : ℝ), A1 ⊆ V →
        OriginalExpansionCoefficients V e1 e2 → 2*delta ≤ |e2| → |e1| ≤ |e2| →
        (((A1.product A1).image (linearCode delta e1 e2)).card : ℝ) ≤
          upperConstant*K*|e2|^sigma*D^36*A.card := by
  obtain ⟨b, hb, V, hVA, hVmass, hpoly⟩ := exists_original_nine_sum_cover
    A hA hd hD hbox hsep hproduct hsum
  have hK1 := original_profile_constant_ge_one A hA hd1 hbox hprofile
  have hK : 0 ≤ K := le_trans (by norm_num) hK1
  have hthree : (3:ℝ)^sigma ≤ 3 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hsigma1
  refine ⟨V, hVA, hVmass, ?_⟩
  intro A1 e1 e2 hA1 hcoeff he2 hnorm
  rcases A1.eq_empty_or_nonempty with rfl | hA1ne
  · simp only [Finset.product_eq_sprod, Finset.empty_product, Finset.image_empty,
      Finset.card_empty, Nat.cast_zero]
    unfold upperConstant
    positivity
  let S := (A1.product A1).image (fun p => e2*p.1+e1*p.2)
  obtain ⟨c,hcenter⟩ := original_linear_sum_radius A1 hA1ne
    (fun a ha => hbox a (hVA (hA1 ha))) hnorm
  have hrecover := original_denominator_cover_recovery A S hA hd hd1
    (hbox b hb).1 hsigma he2 hbox hcenter hprofile
  have hanchor := hpoly A1 e1 e2 hA1 hcoeff
  have hI : ((S.image (rounded delta)).card : ℝ) =
      ((A1.product A1).image (linearCode delta e1 e2)).card := by
    dsimp only [S]
    rw [Finset.image_image]
    rfl
  rw [hI] at hrecover
  have hmul := mul_le_mul_of_nonneg_left hanchor
    (show 0 ≤ 4*(3:ℝ)^sigma*K*|e2|^sigma by positivity)
  have hchain := hrecover.trans hmul
  have hthreeScaled := mul_le_mul_of_nonneg_right hthree
    (show 0 ≤ 84*(110592:ℝ)^9*K*|e2|^sigma*D^36*(A.card : ℝ) by positivity)
  unfold upperConstant
  nlinarith only [hchain,hthreeScaled]

end GKZOriginalLinearUpper
