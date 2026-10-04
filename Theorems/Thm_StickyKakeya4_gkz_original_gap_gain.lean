import Theorems.Thm_StickyKakeya4_gkz_original_gap_energy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical

namespace GKZOriginalGapGain
open GKZOriginalRatioGap GKZOriginalGapEnergy TwoTubePathCollisionCount

/-- Ratio gaps of an original refinement persist on every further original
refinement, with the same denominator cutoff. -/
lemma cutoff_ratios_mono {A B : Finset ℝ} (hAB : A ⊆ B) (h : ℝ) :
    cutoffRatios A h ⊆ cutoffRatios B h := by
  intro z hz
  obtain ⟨w,hw,hwz⟩ := Finset.mem_image.mp hz
  obtain ⟨hwA,hwcut⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwn,hwd⟩ := Finset.mem_product.mp hwA
  obtain ⟨hwn1,hwn2⟩ := Finset.mem_product.mp hwn
  obtain ⟨hwd1,hwd2⟩ := Finset.mem_product.mp hwd
  exact Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨hAB hwn1,hAB hwn2⟩,
      Finset.mem_product.mpr ⟨hAB hwd1,hAB hwd2⟩⟩,hwcut⟩,hwz⟩

/-- A genuine cutoff-ratio gap forces quantitative growth of an actual
linear image, uniformly over dense original refinements. The lower bound
is derived from original Frostman counts and finite Cauchy, not assumed. -/
theorem original_gap_image_gain
    (A A1 A2 : Finset ℝ) {delta h gap e1 e2 K sigma rho : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta) (hK : 0 ≤ K) (hrho : 0 < rho)
    (hA1 : A1 ⊆ A) (hA2 : A2 ⊆ A1) (hmass : rho*(A.card : ℝ) ≤ A2.card)
    (hhlo : delta ≤ h) (hh1 : h ≤ 1)
    (he2lo : 2*delta ≤ |e2|) (he2hi : |e2| ≤ 2)
    (hgap : 0 < gap) (hscale : delta ≤ gap * |e2| * h)
    (havoid : ∀ z ∈ cutoffRatios A1 h, gap ≤ |z-e1/e2|)
    (hprofile : ScalarFrostman A delta K sigma) :
    rho^2 ≤ K^2 * h^sigma * (2*delta/|e2|)^sigma *
      ((A2.product A2).image (linearCode delta e1 e2)).card := by
  let I := (A2.product A2).image (linearCode delta e1 e2)
  let E := collisions (A2.product A2) (linearCode delta e1 e2)
  change rho^2 ≤ K^2*h^sigma*(2*delta/|e2|)^sigma*(I.card : ℝ)
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hA2pos : (0 : ℝ) < A2.card := (mul_pos hrho hApos).trans_le hmass
  have havoid2 : ∀ z ∈ cutoffRatios A2 h, gap ≤ |z-e1/e2| :=
    fun z hz => havoid z (cutoff_ratios_mono hA2 h hz)
  have henergy := original_gap_collision_energy A A2 hd hK (hA2.trans hA1)
    hhlo hh1 he2lo he2hi hgap hscale havoid2 hprofile
  have hcs : (A2.card : ℝ)^4 ≤ (I.card : ℝ)*E.card := by
    have hc : ((A2.product A2).card : ℝ)^2 ≤ (I.card : ℝ)*E.card := by
      exact_mod_cast square_card_le_image_mul_collisions (A2.product A2) (linearCode delta e1 e2)
    have hp : (A2.product A2).card=A2.card*A2.card := by
      simp only [Finset.product_eq_sprod,Finset.card_product]
    rw [hp,Nat.cast_mul] at hc
    convert hc using 1
    ring
  have hupper := mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg I.card)
  have hchain := hcs.trans hupper
  have htwo : (A2.card : ℝ)^2 ≤
      K^2*h^sigma*(2*delta/|e2|)^sigma*(A.card : ℝ)^2*I.card := by
    apply (mul_le_mul_iff_left₀ (show 0 < (A2.card : ℝ)^2 by positivity)).mp
    nlinarith only [hchain]
  have hmass2 := pow_le_pow_left₀ (show 0 ≤ rho*(A.card : ℝ) by positivity) hmass 2
  apply (mul_le_mul_iff_left₀ (show 0 < (A.card : ℝ)^2 by positivity)).mp
  nlinarith only [hmass2,htwo]

end GKZOriginalGapGain
