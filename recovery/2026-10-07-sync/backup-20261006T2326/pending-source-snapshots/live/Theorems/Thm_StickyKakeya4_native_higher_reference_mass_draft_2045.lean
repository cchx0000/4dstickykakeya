/- UNVERIFIED actual fixed-Reference mass reader. No compiler run.
L is the remembered source's actual total-shading lower. The literal source
cells have volume(sigma/2)^4. The new E1 is a deduplicated incidence set on
those cells, and only its actual IsCore retention factor is paid.
-/
import Theorems.Thm_StickyKakeya4_native_generic_reference_data
import Theorems.Thm_StickyKakeya4_native_two_stage_transversality_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeHigherReferenceMassDraft2045
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeGenericReferenceData NativeOriginalParentDensityCore

theorem reference_factor_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (heta : 0≤eta) :
    (factor ref.dimension (g+1) L:ℝ)≤D.thickness^(-(seed/8)) := by
  let Q := coreRadix ref.original ref.R L
  have hQ4 : 4≤Q := NativeSourceSizeBounds.radix_four_le _ _
  have hQ : (1:ℝ)≤(Q:ℝ)^2 := by
    have hh : (4:ℝ)≤Q := by exact_mod_cast hQ4
    nlinarith only [hh]
  have hBudget := NativeTwoStageTransversalityBudget.retention_radix_le_of_transfer_cost
    h.1.2.1 h.1.2.2.1 heta (factor ref.dimension (g+1) L) Q
    (factor ref.dimension (g+1) L:ℝ) le_rfl ref.cost
  exact (show (factor ref.dimension (g+1) L:ℝ)≤(factor ref.dimension (g+1) L:ℝ)*(Q:ℝ)^2 by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg _)).trans hBudget

theorem actual_shading_to_reference_mass {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (shadeLower : ℝ) (hShade0 : 0≤shadeLower)
    (hShade : ENNReal.ofReal shadeLower≤wzTotalShadingVolume D) :
    16*shadeLower≤(factor ref.dimension (g+1) L:ℝ)*(ref.E1.card:ℝ)*D.thickness^4 := by
  have hMesh : 0<mesh D := half_pos h.1.2.1
  have hRead := total_shading_eq_incidence_volume D hMesh ref.original ref.backbone.1
  have hFinite : wzTotalShadingVolume D≠⊤ := by rw [hRead]; finiteness
  have hReal := ENNReal.toReal_mono hFinite hShade
  rw [hRead] at hReal
  have hMass : shadeLower≤((incidences ref.original).card:ℝ)*(D.thickness/2)^4 := by
    simpa only [ENNReal.toReal_ofReal hShade0,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_natCast,ENNReal.toReal_ofReal hMesh.le,mesh] using hReal
  have hCore : ((incidences ref.original).card:ℝ)≤
      (factor ref.dimension (g+1) L:ℝ)*ref.E1.card := by
    exact_mod_cast ref.core.2.2.1
  have hh := hMass.trans (mul_le_mul_of_nonneg_right hCore (pow_nonneg (half_pos h.1.2.1).le 4))
  nlinarith only [hh]

/-- This is the actual mass input for packed_dense_X/packed_Y_class_lower.
The older native coarse thickness never replaces D.thickness. -/
theorem normalized_reference_mass {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (heta : 0≤eta) (shadeLower : ℝ) (hShade0 : 0≤shadeLower)
    (hShade : ENNReal.ofReal shadeLower≤wzTotalShadingVolume D) :
    16*shadeLower*D.thickness^(seed/8)≤(ref.E1.card:ℝ)*D.thickness^4 := by
  have hd := h.1.2.1
  have hMass := actual_shading_to_reference_mass ref shadeLower hShade0 hShade
  have hFactor := reference_factor_upper ref heta
  have hh : 16*shadeLower≤D.thickness^(-(seed/8))*(ref.E1.card:ℝ)*D.thickness^4 :=
    hMass.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hFactor (Nat.cast_nonneg _)) (pow_nonneg hd.le 4))
  have hm := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hd.le (seed/8))
  have hCancel : D.thickness^(-(seed/8))*D.thickness^(seed/8)=1 := by
    rw [←Real.rpow_add hd,neg_add_cancel,Real.rpow_zero]
  calc
    _ ≤ (D.thickness^(-(seed/8))*(ref.E1.card:ℝ)*D.thickness^4)*D.thickness^(seed/8) := hm
    _ = (D.thickness^(-(seed/8))*D.thickness^(seed/8))*((ref.E1.card:ℝ)*D.thickness^4) := by ring
    _ = _ := by rw [hCancel,one_mul]

end NativeHigherReferenceMassDraft2045
