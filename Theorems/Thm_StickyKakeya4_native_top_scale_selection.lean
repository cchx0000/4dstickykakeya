import Theorems.Thm_StickyKakeya4_native_source_size_bounds
import Theorems.Thm_StickyKakeya4_native_dyadic_tube_stopping

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace NativeTopScaleSelection
open NativeDyadicTubeStopping
noncomputable section

/-- A sufficiently small original scale has an actual dyadic top scale in
 the fixed interval required by the native preparation. -/
lemma exists_top_scale {delta : ℝ} (hdelta : 0 < delta)
    (hsmall : delta ≤ (128:ℝ)⁻¹^2) :
    ∃ N : ℕ, (1:ℝ)/128 < scale delta N ∧ scale delta N ≤ (1:ℝ)/64 := by
  have hden : 0 < 64*delta := by positivity
  have hdelta64 : delta ≤ (1:ℝ)/64 := hsmall.trans (by norm_num)
  have hratio : 1 ≤ 1/(64*delta) := (le_div_iff₀ hden).mpr (by nlinarith only [hdelta64])
  obtain ⟨N,hlo,hhi⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ) < 2)
  have hu := (le_div_iff₀ hden).mp hlo
  have hl := (div_lt_iff₀ hden).mp hhi
  rw [pow_succ] at hl
  refine ⟨N,?_,?_⟩
  · change (1:ℝ)/128 < delta*(2:ℝ)^N
    nlinarith only [hl]
  · change delta*(2:ℝ)^N ≤ (1:ℝ)/64
    nlinarith only [hu]

/-- The threshold depends only on the requested original dyadic depth. -/
def deltaThreshold (Nmin : ℕ) : ℝ :=
  min ((128:ℝ)⁻¹^2) ((128:ℝ)⁻¹/(2:ℝ)^Nmin)

lemma deltaThreshold_pos (Nmin : ℕ) : 0 < deltaThreshold Nmin := by
  unfold deltaThreshold
  positivity

lemma choose_top_scale (Nmin : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    (hthreshold : delta ≤ deltaThreshold Nmin) :
    ∃ N : ℕ, Nmin ≤ N ∧ delta ≤ (128:ℝ)⁻¹^2 ∧
      (1:ℝ)/128 < scale delta N ∧ scale delta N ≤ (1:ℝ)/64 := by
  have hsmall : delta ≤ (128:ℝ)⁻¹^2 := hthreshold.trans (min_le_left _ _)
  obtain ⟨N,hlo,hhi⟩ := exists_top_scale hdelta hsmall
  have hlowScale : scale delta Nmin ≤ (1:ℝ)/128 := by
    have h := hthreshold.trans (min_le_right _ _)
    change delta ≤ (128:ℝ)⁻¹/(2:ℝ)^Nmin at h
    have hm := (le_div_iff₀ (by positivity : 0 < (2:ℝ)^Nmin)).mp h
    simpa only [scale, one_div] using hm
  have hdepth : Nmin < N := (scale_strictMono hdelta).lt_iff_lt.mp (hlowScale.trans_lt hlo)
  exact ⟨N,hdepth.le,hsmall,hlo,hhi⟩

theorem exists_delta0 (Nmin : ℕ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
      ∃ N : ℕ, Nmin ≤ N ∧ delta ≤ (128:ℝ)⁻¹^2 ∧
        (1:ℝ)/128 < scale delta N ∧ scale delta N ≤ (1:ℝ)/64 := by
  exact ⟨deltaThreshold Nmin,deltaThreshold_pos Nmin,fun _ hdelta hthreshold =>
    choose_top_scale Nmin hdelta hthreshold⟩

end
end NativeTopScaleSelection
