import Theorems.Thm_StickyKakeya4_original_affine_alphabet_recode
import Theorems.Thm_StickyKakeya4_original_coefficient_profile_mesh_transfer
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open Classical

namespace OriginalRecodedAlphabetProfile
open GKZOriginalGapEnergy OriginalAffineAlphabetRecode IntegerBinRealNearEnergy
open OriginalCoefficientProfileMeshTransfer

/-- The actual re-rounded alphabet inherits a full source profile at the
new mesh, paying both inverse geometry and the old minimum radius. -/
theorem original_recoded_profile (A : Finset ℝ) {delta sigma w K u J : ℝ}
    (hd : 0 < delta) (hs : 0 < sigma) (hK : 1 ≤ K) (hu : 0 ≤ u)
    (hscale : 4*sigma ≤ |w| *delta) (hJ : 0 ≤ J)
    (hgeom : 4/|w| ≤ J) (hmesh : delta ≤ J*sigma)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|)
    (hprofile : ScalarFrostman A delta K u) :
    ScalarFrostman (realLabels A sigma w) sigma (K*J^u) u := by
  have hscale' : sigma ≤ |w| *delta := by linarith only [hscale,hs]
  have hinj := original_real_label_injective A hd hs hscale' hsep
  have hinv := original_recode_inverse_lipschitz A hd hs hscale hsep
  have hg : 2*(2/|w|) ≤ J := by
    rw [show (2:ℝ)*(2/|w|)=4/|w| by ring]
    exact hgeom
  have hh := original_inverse_profile_at_finer_mesh A
    (fun x => sigma*(label sigma w x:ℝ)) delta sigma K u (2/|w|) J hd hs hK hu
    (by positivity) hJ hg hmesh hinj hinv hprofile
  rw [original_real_labels_image]
  exact hh

/-- The literal mesh used to normalize the third query preserves the
original scalar profile with an explicit polynomial transversality cost. -/
theorem original_transverse_weighted_profile (A : Finset ℝ) {delta h w K u : ℝ}
    (hd : 0 < delta) (hh : 0 < h) (hK : 1 ≤ K) (hu : 0 ≤ u)
    (hw : h/2 ≤ |w|)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta/4 ≤ |x-y|)
    (hprofile : ScalarFrostman A (delta/4) K u) :
    ScalarFrostman (realLabels A (h*delta/64) w) (h*delta/64) (K*(16/h)^u) u := by
  have hwpos : 0 < |w| := (show 0<h/2 by positivity).trans_le hw
  have hscale : 4*(h*delta/64) ≤ |w| *(delta/4) := by
    have hm := mul_le_mul_of_nonneg_right hw hd.le
    nlinarith only [hm,mul_pos hh hd]
  have hgeom : 4/|w| ≤ 16/h := by
    apply (div_le_div_iff₀ hwpos hh).mpr
    nlinarith only [hw,hh]
  have hmesh : delta/4 ≤ (16/h)*(h*delta/64) := by
    have he : (16/h)*(h*delta/64)=(h/h)*(delta/4) := by ring
    rw [he,div_self hh.ne',one_mul]
  exact original_recoded_profile A (by positivity) (by positivity) hK hu hscale
    (by positivity) hgeom hmesh hsep hprofile

/-- Restriction to a true relative-mass original subset preserves weak
regularity; its cardinality loss is kept explicit. -/
theorem original_scalar_profile_restrict (A S : Finset ℝ) {delta K u theta : ℝ}
    (hd : 0 ≤ delta) (hK : 0 ≤ K) (htheta : 0 < theta) (hSA : S⊆A)
    (hmass : theta*(A.card:ℝ) ≤ S.card) (hprofile : ScalarFrostman A delta K u) :
    ScalarFrostman S delta (K/theta) u := by
  intro c r hr hr1
  have hcount : ((S.filter (fun x => |x-c| ≤ r)).card:ℝ) ≤ K*r^u*A.card :=
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hSA))).trans (hprofile c r hr hr1)
  have hcoef : 0 ≤ K*r^u := mul_nonneg hK (Real.rpow_nonneg (hd.trans hr) u)
  have hm := mul_le_mul_of_nonneg_left hmass hcoef
  have hc := mul_le_mul_of_nonneg_left hcount htheta.le
  apply (mul_le_mul_iff_left₀ htheta).mp
  have he : (K/theta*r^u*(S.card:ℝ))*theta=K*r^u*S.card := by field_simp
  rw [he]
  nlinarith only [hm,hc]

end OriginalRecodedAlphabetProfile
