import Theorems.Thm_StickyKakeya4_native_angular_test_scale
import Theorems.Thm_StickyKakeya4_native_conditional_grid_power_cost

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable section
namespace NativeConfigurationBaseScale
open NativeAngularTestScale NativeCommonDirectionPhaseMenu NativeConditionalGridPowerCost

/-- Reuse the existing dyadic selector. The chosen configuration depth d
is distinct from the original parent depth m; the source is never changed. -/
theorem exists_base_above_error (m : ℕ) (error : ℝ) (herror : error≤ 1) :
    ∃d : ℕ,d≤ m ∧
      max error ((2:ℝ)⁻¹^m)≤ (2:ℝ)⁻¹^d ∧
      (2:ℝ)⁻¹^d≤ 2*max error ((2:ℝ)⁻¹^m) := by
  have hmu : 0< (2:ℝ)⁻¹^m := by positivity
  have hmu1 : (2:ℝ)⁻¹^m≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht : 0< max error ((2:ℝ)⁻¹^m) := hmu.trans_le (le_max_right _ _)
  have ht1 : max error ((2:ℝ)⁻¹^m)≤ 1 := max_le herror hmu1
  obtain ⟨s,hs,hlo,hhi⟩ := exists_dyadic_angular_scale ht ht1
  let d := s-6
  have he : (64:ℝ)/((2^s:ℕ):ℝ)=(2:ℝ)⁻¹^d := by
    rw [dyadic_sigma s hs,Nat.cast_pow,Nat.cast_ofNat,one_div,inv_pow]
  rw [he] at hlo hhi
  have hDepth : d≤ m :=
    (pow_le_pow_iff_right_of_lt_one₀ (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
      (by norm_num : (2:ℝ)⁻¹<1)).mp ((le_max_right error _).trans hlo)
  exact ⟨d,hDepth,hlo,hhi⟩

/-- The coarse physical rounding and tube-representative errors are paid
along with the affine graph residual, before the new base scale is chosen.
The three coefficients must be read from their actual geometric bounds. -/
theorem total_error_envelope (m : ℕ) (hm : 6≤ m) (epsilon : ℝ) (he : 0≤ epsilon)
    (Caff Cphysical Ctube affineError physicalError tubeError : ℝ)
    (hPhysical : 0≤ Cphysical) (hTube : 0≤ Ctube)
    (Haff : affineError≤ Caff*((64:ℝ)/((2^m:ℕ):ℝ))^(1-2*epsilon))
    (Hphysical : physicalError≤ Cphysical*((64:ℝ)/((2^m:ℕ):ℝ)))
    (Htube : tubeError≤ Ctube*((64:ℝ)/((2^m:ℕ):ℝ))) :
    affineError+physicalError+tubeError≤
      (Caff+Cphysical+Ctube)*((64:ℝ)/((2^m:ℕ):ℝ))^(1-2*epsilon) := by
  have hR : 0< (64:ℝ)/((2^m:ℕ):ℝ) := by positivity
  have hR1 : (64:ℝ)/((2^m:ℕ):ℝ)≤ 1 := by
    rw [middle_width_dyadic m hm]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hScale : (64:ℝ)/((2^m:ℕ):ℝ)≤ ((64:ℝ)/((2^m:ℕ):ℝ))^(1-2*epsilon) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hR hR1
      (show 1-2*epsilon≤ 1 by linarith only [he])
  have hp := Hphysical.trans (mul_le_mul_of_nonneg_left hScale hPhysical)
  have ht := Htube.trans (mul_le_mul_of_nonneg_left hScale hTube)
  nlinarith only [Haff,hp,ht]

/-- A pre-source smallness cutoff can force d≥K as well. Then the final
eta grid may use d, while all parent/source normalization continues to use m. -/
theorem exists_base_with_minimum_depth (m K : ℕ) (error : ℝ)
    (Hsmall : max error ((2:ℝ)⁻¹^m)≤ ((2:ℝ)⁻¹^K)/2) :
    ∃d : ℕ,K≤ d ∧ d≤ m ∧
      max error ((2:ℝ)⁻¹^m)≤ (2:ℝ)⁻¹^d ∧
      (2:ℝ)⁻¹^d≤ 2*max error ((2:ℝ)⁻¹^m) := by
  have hK1 : (2:ℝ)⁻¹^K≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have herror : error≤ 1 := by
    have he := (le_max_left error ((2:ℝ)⁻¹^m)).trans Hsmall
    linarith only [he,hK1]
  obtain ⟨d,hdm,hlo,hhi⟩ := exists_base_above_error m error herror
  have hdk : (2:ℝ)⁻¹^d≤ (2:ℝ)⁻¹^K := hhi.trans (by linarith only [Hsmall])
  have hKd : K≤ d :=
    (pow_le_pow_iff_right_of_lt_one₀ (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
      (by norm_num : (2:ℝ)⁻¹<1)).mp hdk
  exact ⟨d,hKd,hdm,hlo,hhi⟩

end NativeConfigurationBaseScale
