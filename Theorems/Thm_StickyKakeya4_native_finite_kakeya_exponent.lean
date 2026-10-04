import Theorems.Thm_StickyKakeya4_native_finite_kakeya_counts
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeFiniteKakeyaExponent
open Classical MeasureTheory StickyKakeya4 NativeFiniteKakeyaCounts
open scoped ENNReal

/-- The kappa assertion on the EXISTING actual native finite tube/shading class.
This keeps the manuscript's epsilon/eta/cutoff order and uses volume normalization.
No family, shading, profile, or lower-bound certificate is postulated. -/
def KakeyaBound (kappa : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ eta : ℝ, 0 < eta ∧
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n),
      D.thickness ≤ delta0 → IsWangZakharovNativeFiniteInput D eta →
      (ENNReal.ofReal D.thickness).rpow (kappa + epsilon) ≤ volume (sourceUnion D)

lemma bound_mono {kappa kappa' : ℝ} (h : KakeyaBound kappa) (hkk : kappa ≤ kappa') :
    KakeyaBound kappa' := by
  intro epsilon hepsilon
  obtain ⟨eta, heta, delta0, hdelta0, hbound⟩ := h epsilon hepsilon
  refine ⟨eta, heta, delta0, hdelta0, ?_⟩
  intro n D hd hinput
  have he : ENNReal.ofReal D.thickness ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal hinput.1.2.2.1
  exact (ENNReal.rpow_le_rpow_of_exponent_ge he (by linarith :
    kappa + epsilon ≤ kappa' + epsilon)).trans (hbound n D hd hinput)

/-- The nonempty upper exponent is derived from actual tube volume and shading
density, independently of any Wang--Zakharov conclusion. -/
theorem bound_three : KakeyaBound 3 := by
  intro epsilon hepsilon
  obtain ⟨delta0, hdelta0, htube⟩ :=
    exists_markedUnitTube_admissible_scale (half_pos hepsilon)
  refine ⟨epsilon / 2, half_pos hepsilon, delta0, hdelta0, ?_⟩
  intro n D hsmall hinput
  have hvalid := hinput.1.2.2.2.2.1
  have h := union_volume_lower hinput (fun i => htube (D.line i) (hvalid i)
    D.thickness hinput.1.2.1 hsmall)
  convert h using 1
  congr 1
  ring

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
  intro n D hd hinput
  have he : ENNReal.ofReal D.thickness ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal hinput.1.2.2.1
  exact (ENNReal.rpow_le_rpow_of_exponent_ge he
    (show k + epsilon / 2 ≤ extremalExponent + epsilon by linarith)).trans
    (hbound n D hd hinput)

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
        volume (sourceUnion D) < (ENNReal.ofReal D.thickness).rpow (kappa + epsilon) := by
  unfold KakeyaBound at h
  push Not at h
  exact h

/-- Concrete native analogues of (104)--(105): both inequalities hold on the
same original admissible tube/shading family at an arbitrarily small scale.
The lower multiplicity is proved from its radius-one carrier counts and shading
mass, not included as an admissibility field. -/
theorem exists_near_extremizer (hk : 0 < extremalExponent)
    {theta0 delta0 : ℝ} (htheta0 : 0 < theta0) (hdelta0 : 0 < delta0) :
    ∃ theta : ℝ, 0 < theta ∧ theta < theta0 ∧
      ∃ (n : ℕ) (D : FiniteScaleSource n),
        0 < D.thickness ∧ D.thickness < delta0 ∧
        IsWangZakharovNativeFiniteInput D theta ∧
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
  obtain ⟨n, D, hsmall, hinput, hvol⟩ :=
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
    input_mono hinput (by linarith), ?_, ?_⟩
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

/-- Zero native exponent directly supplies the existing finite-volume target,
with coefficient one and the same actual input class. -/
theorem finite_volume_of_bound_zero (h : KakeyaBound 0) : HasWangZakharovFiniteVolumeEstimate := by
  intro epsilon hepsilon
  obtain ⟨eta, heta, delta0, hdelta0, hbound⟩ := h epsilon hepsilon
  refine ⟨eta, heta, 1, by norm_num, by norm_num, delta0, hdelta0, ?_⟩
  intro n D hd hinput
  simpa using hbound n D hd hinput
end NativeFiniteKakeyaExponent
