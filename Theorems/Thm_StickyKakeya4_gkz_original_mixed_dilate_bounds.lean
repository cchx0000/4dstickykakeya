import Theorems.Thm_StickyKakeya4_gkz_finite_anchored_plunnecke
import Theorems.Thm_StickyKakeya4_gkz_dilate_rounded_sums
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped Pointwise

namespace GKZOriginalMixedDilateBounds
open ActualRoundedAdditiveEnergy GKZOriginalProductOverlap GKZDilateRoundedSums
open GKZFiniteAnchoredPlunnecke

/-- Original occupied sum and product covers produce a literal popular
multiplier family with controlled positive and negative anchored sumsets. -/
theorem exists_original_mixed_dilate_family (A : Finset ℝ) {delta K : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta) (hK : 0 < K)
    (hbox : ∀ a∈A, 1 ≤ a ∧ a ≤ 2)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|)
    (hproduct : ((productCells delta A).card : ℝ) ≤ K*A.card)
    (hsum : (((A.product A).image (fun p => rounded delta (p.1+p.2))).card : ℝ) ≤ K*A.card) :
    ∃ b∈A, ∃ V : Finset ℝ, V ⊆ A ∧
      ((1/K)^2/2)*(A.card : ℝ) ≤ V.card ∧
      ∀ a∈V,
        ((dilateCells delta A b+dilateCells delta A a).card : ℝ) ≤ 4608*K^4*A.card ∧
        ((dilateCells delta A b-dilateCells delta A a).card : ℝ) ≤ 4608*K^4*A.card ∧
        ((dilateCells delta A b+dilateCells delta A (-a)).card : ℝ) ≤ 18432*K^4*A.card := by
  obtain ⟨b, hb, V, hVA, hVmass, hoverlap⟩ := exists_original_popular_multiplier A hA hd hK
    (fun a ha => (hbox a ha).1) hsep hproduct
  refine ⟨b, hb, V, hVA, hVmass, ?_⟩
  have hN : 0 < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hself (a : ℝ) (ha : a∈A) :
      ((dilateCells delta A a+dilateCells delta A a).card : ℝ) ≤ (48*K)*A.card := by
    have habs : |a| ≤ 2 := abs_le.mpr ⟨by linarith [(hbox a ha).1], (hbox a ha).2⟩
    have hc := original_dilate_selfsum_cover A hd habs
    have hm := mul_le_mul_of_nonneg_left hsum (show (0:ℝ) ≤ 48 by norm_num)
    nlinarith only [hc,hm]
  intro a ha
  let X := dilateCells delta A b
  let Y := dilateCells delta A a
  let q : ℝ := (1/K)^2/2
  have hq : 0 < q := by dsimp [q]; positivity
  have hmixed := original_overlap_mixed_bounds X Y (X∩Y) hN
    (show 0 ≤ 48*K by positivity) Finset.inter_subset_left Finset.inter_subset_right
    (hoverlap a ha) (hself b hb) (hself a (hVA ha))
  change q*((X+Y).card : ℝ) ≤ (48*K)^2*A.card ∧
    q*((X-Y).card : ℝ) ≤ (48*K)^2*A.card at hmixed
  have hid : ((48*K)^2*(A.card : ℝ))/q=4608*K^4*A.card := by
    dsimp [q]
    field_simp
    ring
  have hplus : ((X+Y).card : ℝ) ≤ 4608*K^4*A.card := by
    rw [← hid]
    apply (le_div_iff₀ hq).mpr
    nlinarith only [hmixed.1]
  have hminus : ((X-Y).card : ℝ) ≤ 4608*K^4*A.card := by
    rw [← hid]
    apply (le_div_iff₀ hq).mpr
    nlinarith only [hmixed.2]
  refine ⟨hplus, hminus, ?_⟩
  have hneg := negative_dilate_anchor_cover X A hd (a := a)
  have hmul := mul_le_mul_of_nonneg_left hminus (show (0:ℝ) ≤ 4 by norm_num)
  change ((X+dilateCells delta A (-a)).card : ℝ) ≤ _
  nlinarith only [hneg, hmul]

end GKZOriginalMixedDilateBounds
