import Theorems.Thm_StickyKakeya4_original_grid_bourgain_transfer
import Theorems.Thm_StickyKakeya4_original_integer_structured_difference
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalStructuredGraphGrowth
open ActualRoundedAdditiveEnergy IntegerBinRealNearEnergy GKZOriginalGapEnergy
open OriginalWeakScalarPositivePower OriginalDenseCoefficientProjection
open OriginalGridBourgainTransfer OriginalIntegerStructuredDifference

/-- A single ACTUAL original coefficient expands EVERY nonempty original
subgraph of the structured Cartesian carrier. The two needed difference
bounds are derived from its actual small sumset and population balance. -/
theorem exists_original_structured_graph_growth (u gap : ℝ)
    (hu : 0 < u) (hu1 : u ≤ 1) (hgap : 0 < gap) (hgap1 : gap ≤ 1) :
    ∃ epsilon eta delta0 : ℝ, 0 < epsilon ∧ 0 < eta ∧ 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (A B : Finset ℤ) (D : Finset ℝ) (delta K lambda : ℝ),
        A.Nonempty → D.Nonempty → 0 < delta → delta ≤ delta0 → 0 ≤ K → 0 < lambda →
        lambda*(A.card:ℝ) ≤ B.card → ((A+B).card:ℝ) ≤ K*A.card →
        (A.card:ℝ) ≤ delta^(-1+gap) →
        ScalarFrostman (realGrid delta A) delta (delta^(-eta)) u →
        ScalarFrostman D delta (delta^(-eta)) u →
        (∀ x∈D, |x| ≤ delta^(-eta)) →
        ∃ x∈D, ∀ G : Finset (ℤ × ℤ), G⊆A.product B → G.Nonempty →
          (G.card:ℝ)*lambda^2*delta^(-epsilon) <
            2*K^5*A.card*(G.image (OriginalBourgainGraphTransfer.code x)).card := by
  obtain ⟨epsilon,eta,delta0,heps,heta,hd0,hd01,hgrowth⟩ :=
    exists_original_weak_scalar_growth u gap hu hu1 hgap hgap1
  refine ⟨epsilon,eta,delta0,heps,heta,hd0,hd01,?_⟩
  intro A B D delta K lambda hA hD hd hsmall hK hlambda hBmass hsum hcard hAprofile hDprofile hDbox
  have hrealNon : (realGrid delta A).Nonempty := hA.image _
  have hrealCard := real_grid_card hd A
  have hrealUpper : ((realGrid delta A).card:ℝ) ≤ delta^(-1+gap) := by
    simpa only [hrealCard] using hcard
  obtain ⟨x,hx,hgain⟩ := hgrowth (realGrid delta A) D delta hrealNon hD hd hsmall
    (real_grid_separated hd A) hrealUpper hAprofile hDprofile hDbox
  rw [hrealCard] at hgain
  have hdiff := (original_difference_bounds A B hA hK hlambda.le hBmass hsum).2.2
  refine ⟨x,hx,?_⟩
  intro G hG hGNon
  have hN : (0:ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  have hGpos : (0:ℝ) < G.card := Nat.cast_pos.mpr hGNon.card_pos
  have htransfer : (G.card:ℝ)*(sumCover (realGrid delta A) delta x).card ≤
      2*((A-A).card:ℝ)*(B-A).card*(G.image (OriginalBourgainGraphTransfer.code x)).card := by
    exact_mod_cast original_grid_graph_transfer A B G hd x hG
  have h1 := mul_lt_mul_of_pos_left hgain (show 0<lambda^2*(G.card:ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left htransfer (sq_nonneg lambda)
  have h3 := mul_le_mul_of_nonneg_right hdiff
    (show 0≤2*((G.image (OriginalBourgainGraphTransfer.code x)).card:ℝ) by positivity)
  apply (mul_lt_mul_iff_left₀ hN).mp
  nlinarith only [h1,h2,h3]

end OriginalStructuredGraphGrowth
