import Theorems.Thm_StickyKakeya4_gkz_original_ratio_dichotomy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
namespace GKZOriginalBoundedGapCoefficients
open GKZOriginalRatioGap GKZOriginalRatioDichotomy ActualRoundedAdditiveEnergy
open GKZFiniteGapDichotomy

/-- Keep the original unit-interval ratio information needed for the
small-diameter target sum in the denominator-scale recovery. -/
theorem original_bounded_ratio_gap_or_dense (A : Finset ℝ) (m : ℕ) {delta h : ℝ}
    (hd : 0 < delta) (hhlo : delta ≤ h)
    (hbox : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 2)
    (hpair : ∃ a ∈ A, ∃ b ∈ A, h < |a-b|)
    (hscale : delta ≤ ((2:ℝ)^m)⁻¹*h^2) :
    (∃ e1 e2 : ℝ, OriginalCoefficients A e1 e2 ∧
      2*delta ≤ |e2| ∧ |e2| ≤ 2 ∧ |e1| ≤ |e2| ∧
      delta ≤ ((2:ℝ)^m)⁻¹*|e2| *h ∧
      (∀ z ∈ cutoffRatios A h, ((2:ℝ)^m)⁻¹ ≤ |z-e1/e2|)) ∨
    1 ≤ 8*((2:ℝ)^m)⁻¹ *
      (((cutoffRatios A h).filter (fun b => 0 ≤ b ∧ b ≤ 1)).image
        (rounded (((2:ℝ)^m)⁻¹))).card := by
  have hh : 0 < h := hd.trans_le hhlo
  obtain ⟨a, ha, b, hb, hab⟩ := hpair
  obtain ⟨hz, ho⟩ := zero_one_mem_of_original_gap A hh.le ha hb hab
  rcases original_gap_or_dense (cutoffRatios A h) m hz ho with hg | hg
  · left
    obtain ⟨q, hq, hq0, hq1, hqgap⟩ := hg
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hvp, hvden⟩ := Finset.mem_filter.mp hv
    obtain ⟨hxpair, hypair⟩ := Finset.mem_product.mp hvp
    obtain ⟨hx, hx'⟩ := Finset.mem_product.mp hxpair
    obtain ⟨hy, hy'⟩ := Finset.mem_product.mp hypair
    have hden : v.2.1-v.2.2 ≠ 0 := abs_pos.mp (hh.trans hvden)
    have hratio : |(v.1.1-v.1.2)/(v.2.1-v.2.2)| ≤ 1 :=
      abs_le.mpr ⟨by linarith, hq1⟩
    rw [abs_div] at hratio
    have hnum : |v.1.1-v.1.2| ≤ |v.2.1-v.2.2| :=
      (div_le_one (abs_pos.mpr hden)).mp hratio
    have heq : |2*(v.2.1-v.2.2)| = 2*|v.2.1-v.2.2| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have helow : 2*delta ≤ |2*(v.2.1-v.2.2)| := by rw [heq]; linarith
    have hehi : |2*(v.2.1-v.2.2)| ≤ 2 := by
      rw [heq]
      have hybox := hbox _ hy
      have hybox' := hbox _ hy'
      have habs : |v.2.1-v.2.2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have hes : delta ≤ ((2:ℝ)^m)⁻¹*|2*(v.2.1-v.2.2)| *h := by
      apply hscale.trans
      have hdenlo : h ≤ |2*(v.2.1-v.2.2)| := by rw [heq]; linarith
      have hm := mul_le_mul_of_nonneg_left hdenlo
        (show 0 ≤ ((2:ℝ)^m)⁻¹*h by positivity)
      nlinarith
    rcases hqgap with hqgap | hqgap
    · refine ⟨v.1.1-v.1.2, 2*(v.2.1-v.2.2),
        ⟨v.1.1, hx, v.1.2, hx', v.2.1, hy, v.2.2, hy', rfl, Or.inl rfl⟩,
        helow, hehi, ?_, hes, ?_⟩
      · rw [heq]
        linarith [abs_nonneg (v.2.1-v.2.2)]
      · intro z hz
        have hid : (v.1.1-v.1.2)/(2*(v.2.1-v.2.2)) =
            ((v.1.1-v.1.2)/(v.2.1-v.2.2))/2 := by field_simp
        rw [hid, abs_sub_comm]
        exact hqgap z hz
    · refine ⟨(v.1.1-v.1.2)+(v.2.1-v.2.2), 2*(v.2.1-v.2.2),
        ⟨v.1.1, hx, v.1.2, hx', v.2.1, hy, v.2.2, hy', rfl, Or.inr rfl⟩,
        helow, hehi, ?_, hes, ?_⟩
      · rw [heq]
        exact (abs_add_le _ _).trans (by linarith)
      · intro z hz
        have hid : ((v.1.1-v.1.2)+(v.2.1-v.2.2))/(2*(v.2.1-v.2.2)) =
            (((v.1.1-v.1.2)/(v.2.1-v.2.2))+1)/2 := by field_simp
        rw [hid, abs_sub_comm]
        exact hqgap z hz
  · exact Or.inr hg

end GKZOriginalBoundedGapCoefficients
