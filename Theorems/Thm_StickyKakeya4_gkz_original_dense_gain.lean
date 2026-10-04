import Theorems.Thm_StickyKakeya4_gkz_original_dense_energy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace GKZOriginalDenseGain
open GKZOriginalRatioGap GKZOriginalGapEnergy GKZOriginalDenseEnergy
open TwoTubePathCollisionCount ActualRoundedAdditiveEnergy

/-- A genuine dense-case lower bound for a linear image with coefficients
chosen as differences of original elements. Its energy is derived, not supplied. -/
theorem exists_original_dense_image_gain (A A1 : Finset ℝ)
    {delta h s K sigma rho : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta) (hhlo : 2*delta ≤ h) (hhhi : h ≤ 1)
    (hs : 0 < s) (hscale : delta ≤ s*h^2) (hK : 0 ≤ K) (hrho : 0 < rho)
    (hA1 : A1 ⊆ A) (hmass : rho*(A.card : ℝ) ≤ A1.card)
    (hbox : ∀ x ∈ A1, 1 ≤ x ∧ x ≤ 2)
    (hprofile : ScalarFrostman A delta K sigma)
    (hdense : 1 ≤ 8*s*
      (((cutoffRatios A1 h).filter (fun b => 0 ≤ b ∧ b ≤ 1)).image (rounded s)).card) :
    ∃ x ∈ A1, ∃ x' ∈ A1, ∃ y ∈ A1, ∃ y' ∈ A1,
      h < |y-y'| ∧ |y-y'| ≤ 1 ∧
      0 ≤ (x-x')/(y-y') ∧ (x-x')/(y-y') ≤ 1 ∧
      rho^2 ≤ (32*s + K^2*(2*delta/|y-y'|)^sigma*h^sigma)*
        ((A1.product A1).image (linearCode delta (x-x') (y-y'))).card := by
  obtain ⟨x, hx, x', hx', y, hy, y', hy', hdenlo, hdenhi, hr0, hr1, henergy⟩ :=
    exists_original_dense_energy A A1 hd hhlo hhhi hs hscale hK hA1 hbox hprofile hdense
  refine ⟨x, hx, x', hx', y, hy, y', hy', hdenlo, hdenhi, hr0, hr1, ?_⟩
  let I := (A1.product A1).image (linearCode delta (x-x') (y-y'))
  let E := collisions (A1.product A1) (linearCode delta (x-x') (y-y'))
  let M := K^2*(2*delta/|y-y'|)^sigma*h^sigma
  change rho^2 ≤ (32*s+M)*(I.card : ℝ)
  have hApos : 0 < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hA1pos : 0 < (A1.card : ℝ) := (mul_pos hrho hApos).trans_le hmass
  have hcard : (A1.card : ℝ) ≤ A.card := Nat.cast_le.mpr (Finset.card_le_card hA1)
  have henergy' : (E.card : ℝ) ≤
      32*s*(A1.card : ℝ)^4 + M*(A.card : ℝ)^2*(A1.card : ℝ)^2 := by
    change (E.card : ℝ) ≤ _ at henergy
    convert henergy using 1
    dsimp [M]
    ring
  have hcs : (A1.card : ℝ)^4 ≤ (I.card : ℝ)*E.card := by
    have hc : ((A1.product A1).card : ℝ)^2 ≤ (I.card : ℝ)*E.card := by
      exact_mod_cast square_card_le_image_mul_collisions (A1.product A1)
        (linearCode delta (x-x') (y-y'))
    have hp : (A1.product A1).card=A1.card*A1.card := by
      simp only [Finset.product_eq_sprod, Finset.card_product]
    rw [hp, Nat.cast_mul] at hc
    convert hc using 1
    ring
  have hchain := hcs.trans (mul_le_mul_of_nonneg_left henergy' (Nat.cast_nonneg I.card))
  have htwo : (A1.card : ℝ)^2 ≤
      (32*s*(A1.card : ℝ)^2+M*(A.card : ℝ)^2)*I.card := by
    apply (mul_le_mul_iff_left₀ (show 0 < (A1.card : ℝ)^2 by positivity)).mp
    nlinarith only [hchain]
  have hcard2 := pow_le_pow_left₀ (Nat.cast_nonneg A1.card) hcard 2
  have hmass2 := pow_le_pow_left₀ (show 0 ≤ rho*(A.card : ℝ) by positivity) hmass 2
  have hbound : (32*s*(A1.card : ℝ)^2+M*(A.card : ℝ)^2)*I.card ≤
      (32*s+M)*(A.card : ℝ)^2*I.card := by
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard2 (show 0 ≤ 32*s by positivity))
      (Nat.cast_nonneg I.card)
    nlinarith only [hm]
  apply (mul_le_mul_iff_left₀ (show 0 < (A.card : ℝ)^2 by positivity)).mp
  nlinarith only [hmass2, htwo.trans hbound]

end GKZOriginalDenseGain
