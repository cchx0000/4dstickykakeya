import Theorems.Thm_StickyKakeya4_native_compact_normalized_source
import Theorems.Thm_StickyKakeya4_compact_source_finite_readback
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeCompactVolumeTransport
open MeasureTheory StickyKakeya4 NativeUnitParentNormalization NativeCompactNormalizedSource
open NativeDenseRetainedUnitParent NativePaddedSourceADLower
open scoped ENNReal

/-- Exact scale and coefficient transport. There is no epsilon loss. -/
lemma coefficient_identity {delta epsilon : ℝ} (he : 0 ≤ epsilon)
    (A : ℝ≥0∞) (hA0 : A ≠ 0) (hAT : A ≠ ⊤) :
    (625*(64:ℝ≥0∞).rpow epsilon*A)⁻¹*(ENNReal.ofReal delta).rpow epsilon =
      (A⁻¹*(ENNReal.ofReal (delta/64)).rpow epsilon)/625 := by
  have hscale : (ENNReal.ofReal (delta/64)).rpow epsilon =
      (ENNReal.ofReal delta).rpow epsilon/(64:ℝ≥0∞).rpow epsilon := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 64),ENNReal.ofReal_ofNat]
    exact ENNReal.div_rpow_of_nonneg _ _ he
  rw [hscale,ENNReal.mul_inv (Or.inr hAT) (Or.inr hA0),
    ENNReal.mul_inv (Or.inl (by norm_num : (625:ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (625:ℝ≥0∞) ≠ ⊤))]
  simp only [div_eq_mul_inv]
  ring

/-- One estimate on the literal fixed output compact class gives an estimate
on every original compact marked family. K is fixed before all source scales;
the resulting cutoff may depend on K. The coefficient is exactly625*64^epsilon*A0. -/
theorem volume_estimate_on_compact
    (h0 : HasWangZakharovFiniteVolumeEstimateOn fixedCompactClass)
    (K : Set MarkedLine) (hK : IsCompact K) : HasWangZakharovFiniteVolumeEstimateOn K := by
  intro epsilon hepsilon
  obtain ⟨eta,heta,A0,hA00,hA0T,d0,hd0,hvolume⟩ := h0 epsilon hepsilon
  obtain ⟨dn,hdn,hnormalize⟩ := compact_original_normalized_source K hK heta
  have h640 : (64:ℝ≥0∞).rpow epsilon ≠ 0 :=
    (ENNReal.rpow_pos (by norm_num : (0:ℝ≥0∞) < 64) (by norm_num)).ne'
  have h64T : (64:ℝ≥0∞).rpow epsilon ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  refine ⟨eta/64,by positivity,625*(64:ℝ≥0∞).rpow epsilon*A0,
    mul_ne_zero (mul_ne_zero (by norm_num) h640) hA00,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) h64T) hA0T,
    min dn (64*d0),lt_min hdn (by positivity),?_⟩
  intro n D hsmall hinput hDK
  obtain ⟨original,a,R,p,_horiginal,_ha,_hQ,hS,hscale,_hcells,hSK,hunion,_hcount,_hshade⟩ :=
    hnormalize n D (eta/64) hinput hDK (hsmall.trans (min_le_left _ _)) le_rfl
  let S := rootSource hinput original R a p
  have hsmallS : S.thickness ≤ d0 := by
    rw [hscale]
    exact (div_le_iff₀ (by norm_num : (0:ℝ) < 64)).mpr
      (by simpa only [mul_comm] using hsmall.trans (min_le_right dn (64*d0)))
  have hvol := (hvolume (parentSubset D R a p).card S hsmallS hS hSK).trans hunion
  rw [hscale] at hvol
  calc
    _ = (A0⁻¹*(ENNReal.ofReal (D.thickness/64)).rpow epsilon)/625 :=
      coefficient_identity hepsilon.le A0 hA00 hA0T
    _ ≤ (625*volume (sourceUnion D))/625 := ENNReal.div_le_div_right hvol 625
    _ = _ := by
      rw [mul_comm (625:ℝ≥0∞),ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]

/-- Consume the transported finite law in the unchanged original compact-front
readback. Only the single K0 estimate remains as a finite-theorem premise. -/
theorem dimH_eq_four_from_fixed_compact_volume
    (h0 : HasWangZakharovFiniteVolumeEstimateOn fixedCompactClass)
    (ambient selector : Set MarkedLine)
    (hcompact : IsCompact ambient) (hsub : selector ⊆ ambient)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀line∈selector,IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector)=3)
    (hboundary : HasCoherentConcentrationBoundary selector hmeasurable hvalid hselector) :
    dimH (unitFront ambient)=4 :=
  dimH_eq_four_of_original_compact_volume ambient selector hcompact hsub hmeasurable hvalid hselector
    hpacking hboundary (volume_estimate_on_compact h0 ambient hcompact)
end NativeCompactVolumeTransport
