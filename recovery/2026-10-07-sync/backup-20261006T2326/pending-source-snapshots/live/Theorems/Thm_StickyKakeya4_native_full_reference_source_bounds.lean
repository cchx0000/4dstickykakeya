import Theorems.Thm_StickyKakeya4_native_original_coarse_selection_with_retention
import Theorems.Thm_StickyKakeya4_native_full_reference_carrier_lower
import Theorems.Thm_StickyKakeya4_native_full_reference_coarse_CW

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeFullReferenceSourceBounds
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeUnitParentNormalization NativeOriginalPrunedMass
open NativeDyadicParentCells
open NativeOriginalCoarseSelectionWithRetention NativeFullCoarseShadow
open NativeFullReferenceCarrierLower NativeFullReferenceCoarseCW
open scoped ENNReal

/-- One original native input supplies one common height chart and one retained
original family with at least half its shading. Its full occupied coarse
sources have actual all-radius carrier AD and relative CW at every available
depth, for every subsequent choice of shading. All ancestor hypotheses are
derived from the original source before these bounds are applied. -/
theorem exists_full_reference_source_bounds {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀ i, D.line i ∈ fixedCompactClass) → D.thickness ≤ delta0 → eta ≤ zeta / 16 →
        ∃ (original : Fin n → Finset Index) (a : ℝ) (level : ℕ) (R : Finset (Fin n)),
          (∀ i, D.shading i = wzCellShading (mesh D) original i) ∧
          D.thickness = (2 : ℝ)⁻¹ ^ level ∧
          (∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) ∧
          R.Nonempty ∧ wzTotalShadingVolume D ≤ 2 * shadingMass D R ∧
          ∀ b : ℕ, b ≤ level →
            ((2 ^ b : ℕ) : ℝ) * D.thickness ≤ 1 ∧
            ∀ E : Finset (Fin n × Index),
              (∀ i : Fin (R.image (parentLabel D a (2 ^ b))).card, ∀ r : ℝ,
                (fullSource h R a level b E).thickness ≤ r → r ≤ 1 →
                  D.thickness ^ (2 * zeta) * (r / (fullSource h R a level b E).thickness) ^ 3 ≤
                    (wzCarrierBallCount (fullSource h R a level b E) i r : ℝ) ∧
                  (wzCarrierBallCount (fullSource h R a level b E) i r : ℝ) ≤
                    (5832 * 770 ^ 3) * D.thickness ^ (-zeta) *
                      (r / (fullSource h R a level b E).thickness) ^ 3) ∧
              (∀ U : Set E4, Convex ℝ U →
                (wzContainedTubeCount (fullSource h R a level b E) U : ℝ≥0∞) ≤
                  (373248 * 512 ^ 4 : ℝ≥0∞) *
                    (ENNReal.ofReal D.thickness).rpow (-eta - 3 * zeta) * volume U *
                      (R.image (parentLabel D a (2 ^ b))).card) := by
  obtain ⟨delta0, hdelta0, hselect⟩ := original_coarse_selection_with_retention hzeta
  refine ⟨delta0, hdelta0, ?_⟩
  intro n D eta h hK hsmall heta
  obtain ⟨original, a, level, R, horiginal, hdy, ha, hR, hshade, H, _hcores⟩ :=
    hselect n D eta h hK hsmall heta
  refine ⟨original, a, level, R, horiginal, hdy, ha, hR, hshade, ?_⟩
  intro b hb
  have hscale : ((2 ^ b : ℕ) : ℝ) * D.thickness ≤ 1 := by
    have hh : ((2 ^ b : ℕ) : ℝ) ≤ ((2 ^ level : ℕ) : ℝ) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      exact pow_le_pow_right₀ (by norm_num) hb
    exact (mul_le_mul_of_nonneg_right hh h.1.2.1.le).trans_eq (dyadic_fine_scale hdy)
  refine ⟨hscale, ?_⟩
  intro E
  exact ⟨full_carrier_bounds h hK ha R level b hb E hscale H,
    fun U hU => full_CW h ha R hR level b hb hscale H E U hU⟩

end NativeFullReferenceSourceBounds
