import Theorems.Thm_StickyKakeya4_native_fixed_compact_normalized_near
import Theorems.Thm_StickyKakeya4_native_padded_source_count_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeFixedCompactMultiplicity
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalPrunedMass
open NativePaddedSourceCountBudget NativeFiniteKakeyaCounts NativeUnitParentNormalization
open NativeFixedCompactKakeyaExponent
open scoped ENNReal

/-- An absolute mass constant derived from actual three-dimensional direction
packing and actual unit-tube volumes; no shading upper profile is postulated. -/
def massConstant : ℝ := 373248*volumeConstant

lemma massConstant_pos : 0 < massConstant := mul_pos (by norm_num) volumeConstant_pos

theorem total_shading_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) :
    wzTotalShadingVolume D ≤ ENNReal.ofReal massConstant := by
  have hd := h.1.2.1
  have hc := original_card_upper h
  have hreal : (n:ℝ)*D.thickness^3 ≤ 373248 := by
    calc
      _ ≤ (373248*(1/D.thickness)^3)*D.thickness^3 := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by field_simp
  have hcount : (n:ℝ≥0∞)*(ENNReal.ofReal D.thickness)^3 ≤ 373248 := by
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg n),ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow hd.le,ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hreal
  have hmass : wzTotalShadingVolume D ≤
      (n:ℝ≥0∞)*(ENNReal.ofReal volumeConstant*(ENNReal.ofReal D.thickness)^3) := by
    simpa only [shadingMass,wzTotalShadingVolume,card_univ,Fintype.card_fin] using shadingMass_upper h univ
  calc
    _ ≤ _ := hmass
    _ = ENNReal.ofReal volumeConstant*((n:ℝ≥0∞)*(ENNReal.ofReal D.thickness)^3) := by ring
    _ ≤ ENNReal.ofReal volumeConstant*373248 := mul_le_mul' le_rfl hcount
    _ = _ := by
      rw [massConstant,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 373248),ENNReal.ofReal_ofNat]
      ring

/-- Apply the attained fixed-class extremal volume bound to the actual source.
Its actual total shading upper bound gives the multiplicity upper exponent.
This is the analytic upper-bound ingredient in (107)--(109), whenever the
coarse or normalized source has been genuinely admitted to this SAME class. -/
theorem fixed_compact_multiplicity_upper {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃eta : ℝ,0 < eta ∧ ∃delta0 : ℝ,0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n),D.thickness ≤ delta0 →
        IsWangZakharovNativeFiniteInput D eta → (∀i,D.line i∈fixedCompactClass) →
        NativeFiniteKakeyaCounts.multiplicity D ≤
          (ENNReal.ofReal D.thickness).rpow (-extremalExponent-epsilon) := by
  obtain ⟨eta,heta,dv,hdv,hvolume⟩ := bound_extremal (epsilon/2) (half_pos hepsilon)
  obtain ⟨dc,hdc,_hdc1,habs⟩ := exists_positive_rpow_absorption_threshold
    (half_pos hepsilon) massConstant_pos.le (show (0:ℝ) < 1 by norm_num)
  refine ⟨eta,heta,min dv dc,lt_min hdv hdc,?_⟩
  intro n D hsmall hinput hDK
  have hd := hinput.1.2.1
  let d := ENNReal.ofReal D.thickness
  have hd0 : d ≠ 0 := by dsimp [d]; positivity
  have hdT : d ≠ ⊤ := ENNReal.ofReal_ne_top
  have hvol : d.rpow (extremalExponent+epsilon/2) ≤ volume (sourceUnion D) :=
    hvolume n D (hsmall.trans (min_le_left _ _)) hinput hDK
  have hc : ENNReal.ofReal massConstant*d.rpow (epsilon/2) ≤ 1 := by
    have hh := ENNReal.ofReal_le_ofReal (habs D.thickness hd (hsmall.trans (min_le_right _ _)))
    simpa only [d,ENNReal.ofReal_mul massConstant_pos.le,ENNReal.rpow_eq_pow,
      ENNReal.ofReal_rpow_of_pos hd,ENNReal.ofReal_one] using hh
  unfold NativeFiniteKakeyaCounts.multiplicity
  calc
    _ ≤ ENNReal.ofReal massConstant/d.rpow (extremalExponent+epsilon/2) :=
      ENNReal.div_le_div (total_shading_upper hinput) hvol
    _ = (ENNReal.ofReal massConstant*d.rpow (epsilon/2))*d.rpow (-extremalExponent-epsilon) := by
      simp only [div_eq_mul_inv,ENNReal.rpow_eq_pow]
      rw [←ENNReal.rpow_neg,mul_assoc,←ENNReal.rpow_add _ _ hd0 hdT]
      congr 2
      ring
    _ ≤ 1*d.rpow (-extremalExponent-epsilon) := mul_le_mul' hc le_rfl
    _ = _ := one_mul _

/-- The lower near-extremal multiplicity and the universal upper multiplicity
hold on ONE ACTUAL constructed normalized source in fixed K0. No matching
certificate and no identification with the unrestricted exponent is used. -/
theorem exists_matched_normalized_source (hk : 0 < extremalExponent)
    {theta0 delta0 epsilon : ℝ} (htheta0 : 0 < theta0) (hdelta0 : 0 < delta0)
    (hepsilon : 0 < epsilon) :
    ∃theta : ℝ,0 < theta ∧ theta < theta0 ∧ ∃ (n : ℕ) (D : FiniteScaleSource n),
      0 < D.thickness ∧ D.thickness < delta0 ∧ IsWangZakharovNativeFiniteInput D theta ∧
      (∀i,D.line i∈fixedCompactClass) ∧
      volume (sourceUnion D) ≤ (ENNReal.ofReal D.thickness).rpow (extremalExponent-theta) ∧
      (ENNReal.ofReal D.thickness).rpow (-extremalExponent+theta) ≤ NativeFiniteKakeyaCounts.multiplicity D ∧
      NativeFiniteKakeyaCounts.multiplicity D ≤ (ENNReal.ofReal D.thickness).rpow (-extremalExponent-epsilon) := by
  obtain ⟨eta,heta,dm,hdm,hupper⟩ := fixed_compact_multiplicity_upper hepsilon
  obtain ⟨theta,htheta,hthSmall,n,D,hd,hsmall,hinput,hDK,hvol,hmu⟩ :=
    NativeFixedCompactNormalizedNear.exists_normalized_source hk
      (lt_min htheta0 heta) (lt_min hdelta0 hdm)
  refine ⟨theta,htheta,hthSmall.trans_le (min_le_left _ _),n,D,hd,
    hsmall.trans_le (min_le_left _ _),hinput,hDK,hvol,hmu,?_⟩
  exact hupper n D (hsmall.le.trans (min_le_right _ _))
    (input_mono hinput (hthSmall.le.trans (min_le_right _ _))) hDK
end NativeFixedCompactMultiplicity
