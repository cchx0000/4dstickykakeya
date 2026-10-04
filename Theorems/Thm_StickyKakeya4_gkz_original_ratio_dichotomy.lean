import Theorems.Thm_StickyKakeya4_gkz_finite_gap_dichotomy
import Theorems.Thm_StickyKakeya4_gkz_original_gap_population_gain
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace GKZOriginalRatioDichotomy
open GKZOriginalRatioGap GKZOriginalGapEnergy ActualRoundedAdditiveEnergy
open GKZFiniteGapDichotomy

/-- The original point profile forces an actual distant original pair in any
dense refinement, whenever its mass exceeds the original interval cap. -/
theorem original_distant_pair (A A1 : Finset ℝ) {delta h K sigma rho : ℝ}
    (hA : A.Nonempty) (hA1 : A1 ⊆ A) (hrho : 0 < rho)
    (hmass : rho*(A.card : ℝ) ≤ A1.card)
    (hhlo : delta ≤ h) (hhhi : h ≤ 1) (hsmall : K*h^sigma < rho)
    (hprofile : ScalarFrostman A delta K sigma) :
    ∃ a ∈ A1, ∃ b ∈ A1, h < |a-b| := by
  have hcard : 0 < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hpos : 0 < (A1.card : ℝ) := (mul_pos hrho hcard).trans_le hmass
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.cast_pos.mp hpos)
  by_contra hnot
  have hsub : A1 ⊆ A.filter (fun x => |x-a| ≤ h) := by
    intro b hb
    refine Finset.mem_filter.mpr ⟨hA1 hb, ?_⟩
    by_contra hbad
    exact hnot ⟨a, ha, b, hb, by simpa only [abs_sub_comm] using lt_of_not_ge hbad⟩
  have hc : (A1.card : ℝ) ≤ (A.filter (fun x => |x-a| ≤ h)).card :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  have hu := hprofile a h hhlo hhhi
  have hstrict := mul_lt_mul_of_pos_right hsmall hcard
  linarith

def OriginalCoefficients (A : Finset ℝ) (e1 e2 : ℝ) : Prop :=
  ∃ x ∈ A, ∃ x' ∈ A, ∃ y ∈ A, ∃ y' ∈ A,
    e2 = 2*(y-y') ∧ (e1=x-x' ∨ e1=(x-x')+(y-y'))

/-- The gap alternative in GKZ Lemma 4.1 supplies literal differences of
original elements, including the exact denominator and scale bounds. -/
theorem original_ratio_gap_or_dense (A : Finset ℝ) (m : ℕ) {delta h : ℝ}
    (hd : 0 < delta) (hhlo : delta ≤ h)
    (hbox : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 2)
    (hpair : ∃ a ∈ A, ∃ b ∈ A, h < |a-b|)
    (hscale : delta ≤ ((2:ℝ)^m)⁻¹*h^2) :
    (∃ e1 e2 : ℝ, OriginalCoefficients A e1 e2 ∧
      2*delta ≤ |e2| ∧ |e2| ≤ 2 ∧
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
    obtain ⟨q, hq, _, _, hqgap⟩ := hg
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hvp, hvden⟩ := Finset.mem_filter.mp hv
    obtain ⟨hxpair, hypair⟩ := Finset.mem_product.mp hvp
    obtain ⟨hx, hx'⟩ := Finset.mem_product.mp hxpair
    obtain ⟨hy, hy'⟩ := Finset.mem_product.mp hypair
    have hden : v.2.1-v.2.2 ≠ 0 := abs_pos.mp (hh.trans hvden)
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
        helow, hehi, hes, ?_⟩
      intro z hz
      have hid : (v.1.1-v.1.2)/(2*(v.2.1-v.2.2)) =
          ((v.1.1-v.1.2)/(v.2.1-v.2.2))/2 := by field_simp
      rw [hid, abs_sub_comm]
      exact hqgap z hz
    · refine ⟨(v.1.1-v.1.2)+(v.2.1-v.2.2), 2*(v.2.1-v.2.2),
        ⟨v.1.1, hx, v.1.2, hx', v.2.1, hy, v.2.2, hy', rfl, Or.inr rfl⟩,
        helow, hehi, hes, ?_⟩
      intro z hz
      have hid : ((v.1.1-v.1.2)+(v.2.1-v.2.2))/(2*(v.2.1-v.2.2)) =
          (((v.1.1-v.1.2)/(v.2.1-v.2.2))+1)/2 := by field_simp
      rw [hid, abs_sub_comm]
      exact hqgap z hz
  · exact Or.inr hg

end GKZOriginalRatioDichotomy
