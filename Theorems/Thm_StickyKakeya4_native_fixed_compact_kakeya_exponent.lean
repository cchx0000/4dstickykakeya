import Theorems.Thm_StickyKakeya4_native_finite_kakeya_exponent
import Theorems.Thm_StickyKakeya4_native_unit_parent_normalization
import Theorems.Thm_StickyKakeya4_wz_carrier_pruning
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeFixedCompactKakeyaExponent
open Classical MeasureTheory StickyKakeya4 NativeFiniteKakeyaCounts
open scoped ENNReal

/-- The kappa assertion on the EXISTING actual native finite tube/shading class.
This keeps the manuscript's epsilon/eta/cutoff order and uses volume normalization.
The literal class NativeUnitParentNormalization.fixedCompactClass is fixed
before epsilon, eta, and the cutoff; all witnesses remain actual native sources. -/
def KakeyaBound (kappa : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ eta : ℝ, 0 < eta ∧
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n),
      D.thickness ≤ delta0 → IsWangZakharovNativeFiniteInput D eta →
      (∀ i, D.line i ∈ NativeUnitParentNormalization.fixedCompactClass) →
      (ENNReal.ofReal D.thickness).rpow (kappa + epsilon) ≤ volume (sourceUnion D)

lemma bound_mono {kappa kappa' : ℝ} (h : KakeyaBound kappa) (hkk : kappa ≤ kappa') :
    KakeyaBound kappa' := by
  intro epsilon hepsilon
  obtain ⟨eta, heta, delta0, hdelta0, hbound⟩ := h epsilon hepsilon
  refine ⟨eta, heta, delta0, hdelta0, ?_⟩
  intro n D hd hinput hcompact
  have he : ENNReal.ofReal D.thickness ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal hinput.1.2.2.1
  exact (ENNReal.rpow_le_rpow_of_exponent_ge he (by linarith :
    kappa + epsilon ≤ kappa' + epsilon)).trans (hbound n D hd hinput hcompact)

/-- Restrict an actual universal native bound to the one fixed compact
class. This is only the valid one-way implication. -/
theorem bound_of_unrestricted {kappa : ℝ}
    (h : NativeFiniteKakeyaExponent.KakeyaBound kappa) : KakeyaBound kappa := by
  intro epsilon hepsilon
  obtain ⟨eta, heta, delta0, hdelta0, hbound⟩ := h epsilon hepsilon
  refine ⟨eta, heta, delta0, hdelta0, ?_⟩
  intro n D hd hinput _hcompact
  exact hbound n D hd hinput

/-- Actual tube volume and shading density already prove the nonempty
upper exponent; restricting to K0 needs no additional source certificate. -/
theorem bound_three : KakeyaBound 3 :=
  bound_of_unrestricted NativeFiniteKakeyaExponent.bound_three

/-- The extremal optimization is over nonnegative exponents, the range relevant
to proving the zero-exponent finite-volume theorem. -/
def exponents : Set ℝ := {kappa | 0 ≤ kappa ∧ KakeyaBound kappa}
def extremalExponent : ℝ := sInf exponents

lemma exponents_nonempty : exponents.Nonempty := ⟨3, by norm_num, bound_three⟩
lemma exponents_bddBelow : BddBelow exponents := ⟨0, fun _ hk => hk.1⟩
lemma extremalExponent_nonneg : 0 ≤ extremalExponent :=
  le_csInf exponents_nonempty (fun _ hk => hk.1)
lemma extremalExponent_le_three : extremalExponent ≤ 3 :=
  csInf_le exponents_bddBelow ⟨by norm_num, bound_three⟩

/-- Epsilon slack proves endpoint attainment on the actual native family class. -/
theorem bound_extremal : KakeyaBound extremalExponent := by
  intro epsilon hepsilon
  obtain ⟨k, hk, hsmall⟩ := exists_lt_of_csInf_lt exponents_nonempty
    (show sInf exponents < extremalExponent + epsilon / 2 by
      change extremalExponent < extremalExponent + epsilon / 2
      linarith)
  obtain ⟨eta, heta, delta0, hdelta0, hbound⟩ := hk.2 (epsilon / 2) (half_pos hepsilon)
  refine ⟨eta, heta, delta0, hdelta0, ?_⟩
  intro n D hd hinput hcompact
  have he : ENNReal.ofReal D.thickness ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal hinput.1.2.2.1
  exact (ENNReal.rpow_le_rpow_of_exponent_ge he
    (show k + epsilon / 2 ≤ extremalExponent + epsilon by linarith)).trans
    (hbound n D hd hinput hcompact)

lemma not_bound_below_extremal {kappa : ℝ} (hk0 : 0 ≤ kappa)
    (hk : kappa < extremalExponent) : ¬ KakeyaBound kappa := by
  intro h
  exact (not_le_of_gt hk) (csInf_le exponents_bddBelow ⟨hk0, h⟩)

/-- Negation yields an ACTUAL admissible source below every cutoff. It does
not assert a counterexample at every predetermined mesh. -/
lemma counterexample_of_not_bound {kappa : ℝ} (h : ¬ KakeyaBound kappa) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ eta : ℝ, 0 < eta →
      ∀ delta0 : ℝ, 0 < delta0 → ∃ (n : ℕ) (D : FiniteScaleSource n),
        D.thickness ≤ delta0 ∧ IsWangZakharovNativeFiniteInput D eta ∧
        (∀ i, D.line i ∈ NativeUnitParentNormalization.fixedCompactClass) ∧
        volume (sourceUnion D) < (ENNReal.ofReal D.thickness).rpow (kappa + epsilon) := by
  unfold KakeyaBound at h
  push Not at h
  exact h

/-- Concrete native analogues of (104)--(105), now on an actual original
admissible family whose every marked line belongs to the same fixed K0.
The lower multiplicity is proved from its radius-one carrier counts and shading
mass, not included as an admissibility field. -/
theorem exists_near_extremizer (hk : 0 < extremalExponent)
    {theta0 delta0 : ℝ} (htheta0 : 0 < theta0) (hdelta0 : 0 < delta0) :
    ∃ theta : ℝ, 0 < theta ∧ theta < theta0 ∧
      ∃ (n : ℕ) (D : FiniteScaleSource n),
        0 < D.thickness ∧ D.thickness < delta0 ∧
        IsWangZakharovNativeFiniteInput D theta ∧
        (∀ i, D.line i ∈ NativeUnitParentNormalization.fixedCompactClass) ∧
        volume (sourceUnion D) ≤ (ENNReal.ofReal D.thickness).rpow (extremalExponent - theta) ∧
        (ENNReal.ofReal D.thickness).rpow (-extremalExponent + theta) ≤
          NativeFiniteKakeyaCounts.multiplicity D := by
  let nu := min (extremalExponent / 2) (theta0 / 8)
  have hnu : 0 < nu := lt_min (half_pos hk) (by positivity)
  have hnuk : nu ≤ extremalExponent / 2 := min_le_left _ _
  have hnut : nu ≤ theta0 / 8 := min_le_right _ _
  have hnot : ¬ KakeyaBound (extremalExponent - nu) :=
    not_bound_below_extremal (by linarith) (by linarith)
  obtain ⟨epsilon, hepsilon, hfail⟩ := counterexample_of_not_bound hnot
  obtain ⟨dtube, hdtube, htube⟩ := exists_markedUnitTube_admissible_scale hnu
  obtain ⟨n, D, hsmall, hinput, hcompact, hvol⟩ :=
    hfail nu hnu (min (delta0 / 2) dtube) (lt_min (half_pos hdelta0) hdtube)
  have hd := hinput.1.2.1
  have hd1 := hinput.1.2.2.1
  have hvalid := hinput.1.2.2.2.2.1
  let e := ENNReal.ofReal D.thickness
  have he0 : e ≠ 0 := by dsimp [e]; positivity
  have heT : e ≠ ⊤ := ENNReal.ofReal_ne_top
  have he1 : e ≤ 1 := by simpa [e] using ENNReal.ofReal_le_ofReal hd1
  have hvol' : volume (sourceUnion D) ≤ e.rpow (extremalExponent - nu) :=
    hvol.le.trans (ENNReal.rpow_le_rpow_of_exponent_ge he1 (by linarith))
  have hshade : e.rpow (3 * nu) ≤ wzTotalShadingVolume D := by
    have hh := total_shading_lower hinput (fun i => htube (D.line i) (hvalid i)
      D.thickness hd (hsmall.trans (min_le_right _ _)))
    convert hh using 1
    congr 1
    ring
  have hS0 : wzTotalShadingVolume D ≠ 0 :=
    ne_of_gt ((ENNReal.rpow_pos (by dsimp [e]; positivity) heT).trans_le hshade)
  have hUT : volume (sourceUnion D) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_ne_zero he0 heT) hvol'
  refine ⟨4 * nu, by positivity, by linarith, n, D, hd,
    lt_of_le_of_lt (hsmall.trans (min_le_left _ _)) (by linarith),
    input_mono hinput (by linarith), hcompact, ?_, ?_⟩
  · exact hvol'.trans (ENNReal.rpow_le_rpow_of_exponent_ge he1 (by linarith))
  · unfold NativeFiniteKakeyaCounts.multiplicity
    apply (ENNReal.le_div_iff_mul_le (Or.inr hS0) (Or.inl hUT)).mpr
    calc
      _ ≤ e.rpow (-extremalExponent + 4 * nu) * e.rpow (extremalExponent - nu) :=
        mul_le_mul' le_rfl hvol'
      _ = e.rpow (3 * nu) := by
        simp only [ENNReal.rpow_eq_pow]
        rw [← ENNReal.rpow_add _ _ he0 heT]
        congr 1
        ring
      _ ≤ _ := hshade

/-- The native volume target restricted to the literal fixed compact
class K0. Its coefficient and eta/cutoff order match the original interface. -/
def HasFixedCompactFiniteVolumeEstimate : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta : ℝ, 0 < eta ∧
    ∃ A : ENNReal, A ≠ 0 ∧ A ≠ ⊤ ∧
    ∃ deltaZero : ℝ, 0 < deltaZero ∧
    ∀ (n : ℕ) (D : FiniteScaleSource n),
      D.thickness ≤ deltaZero →
      IsWangZakharovNativeFiniteInput D eta →
      (∀ i, D.line i ∈ NativeUnitParentNormalization.fixedCompactClass) →
      A⁻¹ * (ENNReal.ofReal D.thickness).rpow epsilon ≤ volume (sourceUnion D)

/-- Zero restricted exponent supplies the restricted finite-volume target,
with coefficient one and the same actual input class. -/
theorem finite_volume_of_bound_zero (h : KakeyaBound 0) : HasFixedCompactFiniteVolumeEstimate := by
  intro epsilon hepsilon
  obtain ⟨eta, heta, delta0, hdelta0, hbound⟩ := h epsilon hepsilon
  refine ⟨eta, heta, 1, by norm_num, by norm_num, delta0, hdelta0, ?_⟩
  intro n D hd hinput hcompact
  simpa using hbound n D hd hinput hcompact


/-- Fixed positive finite coefficients in the existing native interface are
absorbed by epsilon slack; the original admissible source class stays identical. -/
theorem bound_zero_of_finite_volume (h : HasFixedCompactFiniteVolumeEstimate) : KakeyaBound 0 := by
  intro epsilon hepsilon
  obtain ⟨eta, heta, A, hA0, hAT, d0, hd0, hbound⟩ := h (epsilon / 2) (half_pos hepsilon)
  obtain ⟨da, hda, _hda1, habs⟩ := exists_positive_rpow_absorption_threshold
    (half_pos hepsilon) (ENNReal.toReal_nonneg (a := A)) (by norm_num : (0 : ℝ) < 1)
  refine ⟨eta, heta, min d0 da, lt_min hd0 hda, ?_⟩
  intro n D hsmall hinput hcompact
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
    _ ≤ _ := hbound n D (hsmall.trans (min_le_left _ _)) hinput hcompact

theorem bound_zero_iff_finite_volume : KakeyaBound 0 ↔ HasFixedCompactFiniteVolumeEstimate :=
  ⟨finite_volume_of_bound_zero, bound_zero_of_finite_volume⟩

/-- Exact axiom-free reduction of the existing finite-volume target to the
nonnegative extremal exponent of the SAME original native families in the fixed class K0. -/
theorem extremal_zero_iff_finite_volume :
    extremalExponent = 0 ↔ HasFixedCompactFiniteVolumeEstimate := by
  constructor
  · intro hzero
    apply finite_volume_of_bound_zero
    simpa only [hzero] using bound_extremal
  · intro hvol
    apply le_antisymm
    · exact csInf_le exponents_bddBelow ⟨le_rfl, bound_zero_of_finite_volume hvol⟩
    · exact extremalExponent_nonneg

/-- Either the fixed-compact finite-volume target holds, or the actual positive
extremal exponent lies in (0,3] and satisfies its native universal bound. -/
theorem finite_volume_or_positive_extremal :
    HasFixedCompactFiniteVolumeEstimate ∨
      (0 < extremalExponent ∧ extremalExponent ≤ 3 ∧ KakeyaBound extremalExponent) := by
  by_cases hz : extremalExponent = 0
  · exact Or.inl (extremal_zero_iff_finite_volume.mp hz)
  · exact Or.inr ⟨lt_of_le_of_ne extremalExponent_nonneg (Ne.symm hz),
      extremalExponent_le_three, bound_extremal⟩

/-- Restriction can only decrease the infimum. No converse comparison or
identification with the unrestricted global exponent is asserted. -/
theorem extremalExponent_le_unrestricted :
    extremalExponent ≤ NativeFiniteKakeyaExponent.extremalExponent := by
  exact csInf_le exponents_bddBelow
    ⟨NativeFiniteKakeyaExponent.extremalExponent_nonneg,
      bound_of_unrestricted NativeFiniteKakeyaExponent.bound_extremal⟩

end NativeFixedCompactKakeyaExponent
