import Theorems.Thm_StickyKakeya4_integer_bin_real_near_energy
import Theorems.Thm_StickyKakeya4_gkz_original_gap_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open Classical

namespace OriginalAffineAlphabetRecode
open ActualRoundedAdditiveEnergy IntegerBinRealNearEnergy GKZOriginalGapEnergy

def label (sigma w x : ℝ) : ℤ := rounded sigma (w*x)
def labels (A : Finset ℝ) (sigma w : ℝ) : Finset ℤ := A.image (label sigma w)
def realLabels (A : Finset ℝ) (sigma w : ℝ) : Finset ℝ := realGrid sigma (labels A sigma w)

/-- Fine re-rounding of a nondegenerate original dilation is injective
on the actual original separated alphabet. -/
theorem original_label_injective (A : Finset ℝ) {delta sigma w : ℝ}
    (_hd : 0 < delta) (hs : 0 < sigma) (hscale : sigma ≤ |w| *delta)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|) :
    Set.InjOn (label sigma w) A := by
  intro x hx y hy he
  by_contra hne
  have hxy := hsep x hx y hy hne
  have hp := mul_le_mul_of_nonneg_left hxy (abs_nonneg w)
  have hbound : sigma ≤ |w*x-w*y| := by
    rw [← mul_sub,abs_mul]
    exact hscale.trans hp
  have hxerr := round_error hs (w*x)
  have hyerr := round_error hs (w*y)
  change rounded sigma (w*x)=rounded sigma (w*y) at he
  rw [he] at hxerr
  have hclose : |w*x-w*y| < sigma := abs_lt.mpr
    ⟨by linarith only [hxerr.1,hyerr.2],by linarith only [hxerr.2,hyerr.1]⟩
  linarith only [hbound,hclose]

lemma original_labels_card (A : Finset ℝ) {delta sigma w : ℝ}
    (hd : 0 < delta) (hs : 0 < sigma) (hscale : sigma ≤ |w| *delta)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|) :
    (labels A sigma w).card=A.card :=
  Finset.card_image_iff.mpr (original_label_injective A hd hs hscale hsep)

lemma original_real_labels_card (A : Finset ℝ) {delta sigma w : ℝ}
    (hd : 0 < delta) (hs : 0 < sigma) (hscale : sigma ≤ |w| *delta)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|) :
    (realLabels A sigma w).card=A.card := by
  rw [realLabels,real_grid_card hs,original_labels_card A hd hs hscale hsep]

lemma original_real_labels_image (A : Finset ℝ) (sigma w : ℝ) :
    realLabels A sigma w=A.image (fun x => sigma*(label sigma w x:ℝ)) := by
  unfold realLabels realGrid labels
  rw [Finset.image_image]
  rfl

lemma original_label_error {sigma : ℝ} (hs : 0 < sigma) (w x : ℝ) :
    |w*x-sigma*(label sigma w x:ℝ)| ≤ sigma := by
  have hh := round_error hs (w*x)
  exact (abs_of_nonneg hh.1).le.trans hh.2.le

/-- The real-grid version of the recoding also preserves actual source
points injectively. -/
lemma original_real_label_injective (A : Finset ℝ) {delta sigma w : ℝ}
    (hd : 0 < delta) (hs : 0 < sigma) (hscale : sigma ≤ |w| *delta)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|) :
    Set.InjOn (fun x => sigma*(label sigma w x:ℝ)) A := by
  intro x hx y hy he
  exact original_label_injective A hd hs hscale hsep hx hy (real_grid_injective hs he)

/-- Original spacing exceeds the rounding error, so the actual re-rounded
map has a quantitative inverse Lipschitz estimate. -/
theorem original_recode_inverse_lipschitz (A : Finset ℝ) {delta sigma w : ℝ}
    (hd : 0 < delta) (hs : 0 < sigma) (hscale : 4*sigma ≤ |w| *delta)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|) :
    ∀ x∈A, ∀ y∈A, |x-y| ≤ (2/|w|)*
      |sigma*(label sigma w x:ℝ)-sigma*(label sigma w y:ℝ)| := by
  have hw : 0 < |w| := (mul_pos_iff_of_pos_right hd).mp
    ((show 0<4*sigma by positivity).trans_le hscale)
  intro x hx y hy
  by_cases he : x=y
  · subst y
    simp only [sub_self,abs_zero,mul_zero,le_refl]
  · have hxy := hsep x hx y hy he
    have hgap := hscale.trans (mul_le_mul_of_nonneg_left hxy (abs_nonneg w))
    have hxerr := original_label_error hs w x
    have hyerr := original_label_error hs w y
    have h1 := abs_sub_le (w*x) (sigma*(label sigma w x:ℝ)) (w*y)
    have h2 := abs_sub_le (sigma*(label sigma w x:ℝ)) (sigma*(label sigma w y:ℝ)) (w*y)
    rw [abs_sub_comm (sigma*(label sigma w y:ℝ)) (w*y)] at h2
    rw [← mul_sub,abs_mul] at h1
    rw [show (2/|w|)*|sigma*(label sigma w x:ℝ)-sigma*(label sigma w y:ℝ)| =
      (2*|sigma*(label sigma w x:ℝ)-sigma*(label sigma w y:ℝ)|)/|w| by ring]
    apply (le_div_iff₀ hw).mpr
    nlinarith only [hgap,hxerr,hyerr,h1,h2]

end OriginalAffineAlphabetRecode
