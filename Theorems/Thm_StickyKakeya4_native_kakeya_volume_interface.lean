import Theorems.Thm_StickyKakeya4_native_finite_kakeya_exponent
import Theorems.Thm_StickyKakeya4_wz_carrier_pruning
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeKakeyaVolumeInterface
open Classical MeasureTheory StickyKakeya4 NativeFiniteKakeyaExponent
open scoped ENNReal

/-- Fixed positive finite coefficients in the existing native interface are
absorbed by epsilon slack; the original admissible source class stays identical. -/
theorem bound_zero_of_finite_volume (h : HasWangZakharovFiniteVolumeEstimate) : KakeyaBound 0 := by
  intro epsilon hepsilon
  obtain ⟨eta, heta, A, hA0, hAT, d0, hd0, hbound⟩ := h (epsilon / 2) (half_pos hepsilon)
  obtain ⟨da, hda, _hda1, habs⟩ := exists_positive_rpow_absorption_threshold
    (half_pos hepsilon) (ENNReal.toReal_nonneg (a := A)) (by norm_num : (0 : ℝ) < 1)
  refine ⟨eta, heta, min d0 da, lt_min hd0 hda, ?_⟩
  intro n D hsmall hinput
  have hd := hinput.1.2.1
  let e := ENNReal.ofReal D.thickness
  have he0 : e ≠ 0 := by dsimp [e]; positivity
  have heT : e ≠ ⊤ := ENNReal.ofReal_ne_top
  have habs' : A * e.rpow (epsilon / 2) ≤ 1 := by
    have hh := ENNReal.ofReal_le_ofReal
      (habs D.thickness hd (hsmall.trans (min_le_right _ _)))
    simpa only [e, ENNReal.rpow_eq_pow, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hAT,
      ENNReal.ofReal_rpow_of_pos hd, ENNReal.ofReal_one] using hh
  have hsmallpow : e.rpow (epsilon / 2) ≤ A⁻¹ := by
    have hh : e.rpow (epsilon / 2) ≤ (1 : ℝ≥0∞) / A :=
      (ENNReal.le_div_iff_mul_le (Or.inl hA0) (Or.inl hAT)).mpr (by simpa [mul_comm] using habs')
    simpa using hh
  calc
    e.rpow (0 + epsilon) = e.rpow (epsilon / 2) * e.rpow (epsilon / 2) := by
      simp only [ENNReal.rpow_eq_pow]
      rw [← ENNReal.rpow_add _ _ he0 heT]
      congr 1
      ring
    _ ≤ A⁻¹ * e.rpow (epsilon / 2) := mul_le_mul' hsmallpow le_rfl
    _ ≤ _ := hbound n D (hsmall.trans (min_le_left _ _)) hinput

theorem bound_zero_iff_finite_volume : KakeyaBound 0 ↔ HasWangZakharovFiniteVolumeEstimate :=
  ⟨finite_volume_of_bound_zero, bound_zero_of_finite_volume⟩

/-- Exact axiom-free reduction of the existing finite-volume target to the
nonnegative extremal exponent of the SAME original native families. -/
theorem extremal_zero_iff_finite_volume :
    extremalExponent = 0 ↔ HasWangZakharovFiniteVolumeEstimate := by
  constructor
  · intro hzero
    apply finite_volume_of_bound_zero
    simpa only [hzero] using bound_extremal
  · intro hvol
    apply le_antisymm
    · exact csInf_le exponents_bddBelow ⟨le_rfl, bound_zero_of_finite_volume hvol⟩
    · exact extremalExponent_nonneg

/-- Either the existing finite-volume target holds, or the actual positive
extremal exponent lies in (0,3] and satisfies its native universal bound. -/
theorem finite_volume_or_positive_extremal :
    HasWangZakharovFiniteVolumeEstimate ∨
      (0 < extremalExponent ∧ extremalExponent ≤ 3 ∧ KakeyaBound extremalExponent) := by
  by_cases hz : extremalExponent = 0
  · exact Or.inl (extremal_zero_iff_finite_volume.mp hz)
  · exact Or.inr ⟨lt_of_le_of_ne extremalExponent_nonneg (Ne.symm hz),
      extremalExponent_le_three, bound_extremal⟩
end NativeKakeyaVolumeInterface
