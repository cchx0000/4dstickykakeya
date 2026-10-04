import Theorems.Thm_StickyKakeya4_original_tensor_frostman

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
noncomputable section
open Classical

namespace OriginalCoefficientZeroRemoval
open GKZOriginalGapEnergy

/-- The original full profile pays for removing coefficients near zero,
so all later reciprocal bounds concern actual retained original points. -/
theorem original_remove_zero_mass (D : Finset ℝ) {delta K u tau : ℝ}
    (htau : delta ≤ tau) (htau1 : tau ≤ 1)
    (hprofile : ScalarFrostman D delta K u) (hsmall : K*tau^u ≤ 1/2) :
    (D.card:ℝ)/2 ≤ (D.filter (fun x => tau < |x|)).card := by
  have hcap := hprofile 0 tau htau htau1
  simp only [sub_zero] at hcap
  have hp : ((D.filter (fun x => |x| ≤ tau)).card:ℝ)+
      (D.filter (fun x => tau < |x|)).card=D.card := by
    exact_mod_cast (by simpa only [not_le] using
      Finset.card_filter_add_card_filter_not (s:=D) (fun x : ℝ => |x| ≤ tau))
  have hbound := mul_le_mul_of_nonneg_right hsmall (show (0:ℝ)≤D.card from Nat.cast_nonneg _)
  linarith only [hp,hcap,hbound]

/-- Full original weak regularity is retained, with its exact factor-two
mass loss and unchanged original mesh. -/
theorem original_remove_zero_profile (D : Finset ℝ) {delta K u tau : ℝ}
    (hdelta : 0 ≤ delta) (hK : 0 ≤ K) (htau : delta ≤ tau) (htau1 : tau ≤ 1)
    (hprofile : ScalarFrostman D delta K u) (hsmall : K*tau^u ≤ 1/2) :
    ScalarFrostman (D.filter (fun x => tau < |x|)) delta (2*K) u := by
  have hmass := original_remove_zero_mass D htau htau1 hprofile hsmall
  intro c r hr hr1
  have hsub : ((D.filter (fun x => tau < |x|)).filter (fun x => |x-c| ≤ r)) ⊆
      D.filter (fun x => |x-c| ≤ r) := Finset.filter_subset_filter _ (Finset.filter_subset _ _)
  have hcount : (((D.filter (fun x => tau < |x|)).filter (fun x => |x-c| ≤ r)).card:ℝ) ≤
      K*r^u*D.card := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hprofile c r hr hr1)
  have hfactor : 0 ≤ K*r^u := mul_nonneg hK (Real.rpow_nonneg (hdelta.trans hr) u)
  have hm := mul_le_mul_of_nonneg_left hmass hfactor
  nlinarith only [hcount,hm]

end OriginalCoefficientZeroRemoval
