import Theorems.Thm_StickyKakeya4_gkz_original_gap_gain
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace GKZOriginalGapPopulationGain
open GKZOriginalRatioGap GKZOriginalGapEnergy GKZOriginalGapGain

/-- Quantitative GKZ gap growth relative to the original population, with
the original dense-refinement loss and the denominator power explicit. -/
theorem original_gap_population_gain
    (A A1 A2 : Finset ℝ) {delta h gap e1 e2 K sigma rho : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta) (hK : 0 ≤ K) (hrho : 0 < rho)
    (hcard : (A.card : ℝ)=delta^(-sigma))
    (hA1 : A1 ⊆ A) (hA2 : A2 ⊆ A1) (hmass : rho*(A.card : ℝ) ≤ A2.card)
    (hhlo : delta ≤ h) (hh1 : h ≤ 1)
    (he2lo : 2*delta ≤ |e2|) (he2hi : |e2| ≤ 2)
    (hgap : 0 < gap) (hscale : delta ≤ gap * |e2| * h)
    (havoid : ∀ z ∈ cutoffRatios A1 h, gap ≤ |z-e1/e2|)
    (hprofile : ScalarFrostman A delta K sigma) :
    rho^2 * |e2|^sigma * A.card ≤ (2:ℝ)^sigma*K^2*h^sigma*
      ((A2.product A2).image (linearCode delta e1 e2)).card := by
  have hg := original_gap_image_gain A A1 A2 hA hd hK hrho hA1 hA2 hmass
    hhlo hh1 he2lo he2hi hgap hscale havoid hprofile
  have hepos : 0 < |e2| := (by positivity : 0 < 2*delta).trans_le he2lo
  have hepow : |e2|^sigma≠0 := ne_of_gt (Real.rpow_pos_of_pos hepos sigma)
  have hratio : (2*delta/|e2|)^sigma * |e2|^sigma=(2:ℝ)^sigma*delta^sigma := by
    rw [Real.div_rpow (by positivity) (abs_nonneg e2),div_mul_cancel₀ _ hepow]
    exact Real.mul_rpow (by norm_num) hd.le
  have hpop : delta^sigma*(A.card : ℝ)=1 := by
    rw [hcard,← Real.rpow_add hd,add_neg_cancel,Real.rpow_zero]
  have hm := mul_le_mul_of_nonneg_right hg
    (show 0 ≤ |e2|^sigma*(A.card : ℝ) by positivity)
  calc
    _ = rho^2*(|e2|^sigma*(A.card : ℝ)) := by ring
    _ ≤ (K^2*h^sigma*(2*delta/|e2|)^sigma*
        ((A2.product A2).image (linearCode delta e1 e2)).card)*
          (|e2|^sigma*(A.card : ℝ)) := hm
    _ = (K^2*h^sigma*((A2.product A2).image (linearCode delta e1 e2)).card)*
          ((2*delta/|e2|)^sigma * |e2|^sigma)*(A.card : ℝ) := by ring
    _ = (K^2*h^sigma*((A2.product A2).image (linearCode delta e1 e2)).card)*
          ((2:ℝ)^sigma*delta^sigma)*(A.card : ℝ) := by rw [hratio]
    _ = ((2:ℝ)^sigma*K^2*h^sigma*
          ((A2.product A2).image (linearCode delta e1 e2)).card)*
            (delta^sigma*(A.card : ℝ)) := by ring
    _ = _ := by rw [hpop,mul_one]

end GKZOriginalGapPopulationGain
