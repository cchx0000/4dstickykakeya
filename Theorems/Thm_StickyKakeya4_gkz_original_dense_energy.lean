import Theorems.Thm_StickyKakeya4_gkz_original_short_denominator_energy
import Theorems.Thm_StickyKakeya4_gkz_original_large_denominator_energy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace GKZOriginalDenseEnergy
open GKZOriginalRatioGap GKZOriginalGapEnergy GKZOriginalDenseRatioSelection
open GKZOriginalShortDenominatorEnergy GKZOriginalLargeDenominatorEnergy
open TwoTubePathCollisionCount ActualRoundedAdditiveEnergy

/-- The actual dense ratio selection and original small-denominator profile
together give a collision upper bound for a literal original linear image. -/
theorem exists_original_dense_energy (A A1 : Finset ℝ) {delta h s K sigma : ℝ}
    (hd : 0 < delta) (hhlo : 2*delta ≤ h) (hhhi : h ≤ 1)
    (hs : 0 < s) (hscale : delta ≤ s*h^2) (hK : 0 ≤ K)
    (hA1 : A1 ⊆ A) (hbox : ∀ x ∈ A1, 1 ≤ x ∧ x ≤ 2)
    (hprofile : ScalarFrostman A delta K sigma)
    (hdense : 1 ≤ 8*s*
      (((cutoffRatios A1 h).filter (fun b => 0 ≤ b ∧ b ≤ 1)).image (rounded s)).card) :
    ∃ x ∈ A1, ∃ x' ∈ A1, ∃ y ∈ A1, ∃ y' ∈ A1,
      h < |y-y'| ∧ |y-y'| ≤ 1 ∧
      0 ≤ (x-x')/(y-y') ∧ (x-x')/(y-y') ≤ 1 ∧
      ((collisions (A1.product A1) (linearCode delta (x-x') (y-y'))).card : ℝ) ≤
        32*s*(A1.card : ℝ)^4 +
        (K*(2*delta/|y-y'|)^sigma*A.card)*(K*h^sigma*A.card)*(A1.card : ℝ)^2 := by
  obtain ⟨x, hx, x', hx', y, hy, y', hy', hden, hr0, hr1, hlight⟩ :=
    exists_original_light_ratio A1 hs hdense
  have hh : 0 < h := (by positivity : 0 < 2*delta).trans_le hhlo
  have hdenhi : |y-y'| ≤ 1 := by
    have hybox := hbox y hy
    have hybox' := hbox y' hy'
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨x, hx, x', hx', y, hy, y', hy', hden, hdenhi, hr0, hr1, ?_⟩
  let E := collisions (A1.product A1) (linearCode delta (x-x') (y-y'))
  have hlarge := original_large_denominator_energy A1 hd hh hs hden.le hscale
    (e1 := x-x')
  have hl : ((E.filter (fun e => h < |e.1.2-e.2.2|)).card : ℝ) ≤
      32*s*(A1.card : ℝ)^4 := (Nat.cast_le.mpr hlarge).trans hlight
  have hsml := original_short_denominator_energy A A1 hd hK hA1
    (show delta ≤ h by linarith) hhhi (hhlo.trans hden.le)
    (hdenhi.trans (by norm_num)) hprofile (e1 := x-x')
  have heq : (E.filter (fun e => h < |e.1.2-e.2.2|)).card +
      (E.filter (fun e => |e.1.2-e.2.2| ≤ h)).card = E.card := by
    simpa only [not_lt] using Finset.card_filter_add_card_filter_not
      (s := E) (fun e => h < |e.1.2-e.2.2|)
  have heqR : ((E.filter (fun e => h < |e.1.2-e.2.2|)).card : ℝ) +
      (E.filter (fun e => |e.1.2-e.2.2| ≤ h)).card = (E.card : ℝ) := by
    exact_mod_cast heq
  change (E.card : ℝ) ≤ _
  change ((E.filter (fun e => |e.1.2-e.2.2| ≤ h)).card : ℝ) ≤ _ at hsml
  linarith

end GKZOriginalDenseEnergy
