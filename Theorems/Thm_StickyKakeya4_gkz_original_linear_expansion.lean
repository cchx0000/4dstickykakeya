import Theorems.Thm_StickyKakeya4_gkz_original_dense_gain
import Theorems.Thm_StickyKakeya4_gkz_original_bounded_gap_coefficients
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace GKZOriginalLinearExpansion
open GKZOriginalRatioGap GKZOriginalGapEnergy GKZOriginalGapPopulationGain
open GKZOriginalRatioDichotomy GKZOriginalDenseGain ActualRoundedAdditiveEnergy
open GKZOriginalBoundedGapCoefficients

/-- A source-faithful finite GKZ expansion alternative. The ratio dichotomy,
original quadruple averaging, both energy estimates, and Cauchy are all proved
from the original real carrier. No expansion or energy engine is assumed. -/
theorem original_linear_expansion_alternative (A A1 : Finset ℝ) (m : ℕ)
    {delta h K sigma rho : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta) (hhlo : 2*delta ≤ h) (hhhi : h ≤ 1)
    (hK : 0 ≤ K) (hrho : 0 < rho) (hcard : (A.card : ℝ)=delta^(-sigma))
    (hA1 : A1 ⊆ A) (hmass : rho*(A.card : ℝ) ≤ A1.card)
    (hbox : ∀ x ∈ A1, 1 ≤ x ∧ x ≤ 2)
    (hprofile : ScalarFrostman A delta K sigma)
    (hsmall : K*h^sigma < rho) (hscale : delta ≤ ((2:ℝ)^m)⁻¹*h^2) :
    (∃ e1 e2 : ℝ, OriginalCoefficients A1 e1 e2 ∧
      2*delta ≤ |e2| ∧ |e2| ≤ 2 ∧ |e1| ≤ |e2| ∧
      ∀ (A2 : Finset ℝ) (eta : ℝ), A2 ⊆ A1 → 0 < eta →
        eta*(A.card : ℝ) ≤ A2.card →
        eta^2 * |e2|^sigma * A.card ≤ (2:ℝ)^sigma*K^2*h^sigma*
          ((A2.product A2).image (linearCode delta e1 e2)).card) ∨
    (∃ x ∈ A1, ∃ x' ∈ A1, ∃ y ∈ A1, ∃ y' ∈ A1,
      h < |y-y'| ∧ |y-y'| ≤ 1 ∧
      0 ≤ (x-x')/(y-y') ∧ (x-x')/(y-y') ≤ 1 ∧
      rho^2 ≤ (32*((2:ℝ)^m)⁻¹ + K^2*(2*delta/|y-y'|)^sigma*h^sigma)*
        ((A1.product A1).image (linearCode delta (x-x') (y-y'))).card) := by
  have hdh : delta ≤ h := by linarith
  have hpair := original_distant_pair A A1 hA hA1 hrho hmass hdh hhhi hsmall hprofile
  rcases original_bounded_ratio_gap_or_dense A1 m hd hdh hbox hpair hscale with hgap | hdense
  · left
    obtain ⟨e1, e2, hcoeff, helo, hehi, henorm, hgapscale, havoid⟩ := hgap
    refine ⟨e1, e2, hcoeff, helo, hehi, henorm, ?_⟩
    intro A2 eta hA2 heta hmass2
    exact original_gap_population_gain A A1 A2 hA hd hK heta hcard hA1 hA2 hmass2
      hdh hhhi helo hehi (by positivity) hgapscale havoid hprofile
  · right
    exact exists_original_dense_image_gain A A1 hA hd hhlo hhhi (by positivity)
      hscale hK hrho hA1 hmass hbox hprofile hdense

end GKZOriginalLinearExpansion
