import Theorems.Thm_StickyKakeya4_actual_rounded_additive_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace SeparatedDyadicCardinality
open ActualRoundedAdditiveEnergy

lemma original_rounded_label_bounds {x : ℝ} (n B : ℕ) (hx : |x|≤(B:ℝ)) :
    rounded (((2:ℝ)^n)⁻¹) x ∈ Finset.Icc (-(B:ℤ)*2^n) ((B:ℤ)*2^n) := by
  have hp : 0 < (2:ℝ)^n := by positivity
  obtain ⟨hl,hu⟩ := abs_le.mp hx
  have hscaledlo : ((-(B:ℤ)*2^n : ℤ):ℝ) ≤ x/((2:ℝ)^n)⁻¹ := by
    push_cast
    simp only [div_inv_eq_mul]
    nlinarith
  have hscaledhi : x/((2:ℝ)^n)⁻¹ ≤ (((B:ℤ)*2^n : ℤ):ℝ) := by
    push_cast
    simp only [div_inv_eq_mul]
    exact mul_le_mul_of_nonneg_right hu hp.le
  exact Finset.mem_Icc.mpr ⟨Int.le_floor.mpr hscaledlo,
    by simpa only [rounded,Int.floor_intCast] using Int.floor_mono hscaledhi⟩

/-- The original δ-separated real set supplies the binary chain-size budget;
no cardinality bound is taken as a replacement for its physical support. -/
theorem original_cardinality_bound (X : Finset ℝ) (n B : ℕ)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x≠y → ((2:ℝ)^n)⁻¹≤|x-y|)
    (hbound : ∀ x∈X, |x|≤(B:ℝ)) :
    X.card ≤ (2*B+1)*2^n := by
  classical
  have hδ : 0 < ((2:ℝ)^n)⁻¹ := by positivity
  have hc := rounded_card X hδ hsep
  have hsub : X.image (rounded (((2:ℝ)^n)⁻¹)) ⊆
      Finset.Icc (-(B:ℤ)*2^n) ((B:ℤ)*2^n) := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
    exact original_rounded_label_bounds n B (hbound x hx)
  have hi : (Finset.Icc (-(B:ℤ)*2^n) ((B:ℤ)*2^n)).card = 2*B*2^n+1 := by
    rw [Int.card_Icc]
    have h : (B:ℤ)*2^n+1-(-(B:ℤ)*2^n) = ((2*B*2^n+1 : ℕ):ℤ) := by push_cast; ring
    rw [h]
    exact Int.toNat_natCast _
  have hh := Finset.card_le_card hsub
  rw [hc,hi] at hh
  have hp : 1 ≤ (2:ℕ)^n := one_le_pow₀ (by norm_num)
  nlinarith

end SeparatedDyadicCardinality
