import Theorems.Thm_StickyKakeya4_wang_zakharov_finite_interface
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeFiniteKakeyaCounts
open Classical Finset MeasureTheory StickyKakeya4
open scoped ENNReal BigOperators

/-- Average multiplicity of the actual original cubical shadings. -/
def multiplicity {n : ℕ} (D : FiniteScaleSource n) : ℝ≥0∞ :=
  wzTotalShadingVolume D / volume (sourceUnion D)

lemma input_mono {n : ℕ} {D : FiniteScaleSource n} {eta theta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (het : eta ≤ theta) :
    IsWangZakharovNativeFiniteInput D theta := by
  obtain ⟨hi, hg, hnrm⟩ := h
  obtain ⟨hn, hd, hd1, hdy, hv, hw, hm, hcub, hsub, hsep, hAD, hCW, hden⟩ := hi
  have he : ENNReal.ofReal D.thickness ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hd1
  have hl := ENNReal.rpow_le_rpow_of_exponent_ge he het
  have hu := ENNReal.rpow_le_rpow_of_exponent_ge he (neg_le_neg het)
  refine ⟨⟨hn, hd, hd1, hdy, hv, hw, hm, hcub, hsub, hsep, ?_, ?_, ?_⟩, hg, hnrm⟩
  · intro i r hdr hr1
    exact ⟨(mul_le_mul' hl le_rfl).trans (hAD i r hdr hr1).1,
      (hAD i r hdr hr1).2.trans (mul_le_mul' hu le_rfl)⟩
  · intro U hU
    exact (hCW U hU).trans (mul_le_mul' (mul_le_mul' hu le_rfl) le_rfl)
  · exact (mul_le_mul' hl le_rfl).trans hden

lemma total_shading_le_card_mul_union {n : ℕ} (D : FiniteScaleSource n)
    (hw : ∀ i, D.weight i = 1) :
    wzTotalShadingVolume D ≤ (n : ℝ≥0∞) * volume (sourceUnion D) := by
  unfold wzTotalShadingVolume
  calc
    _ ≤ ∑ _i : Fin n, volume (sourceUnion D) := by
      apply sum_le_sum
      intro i _hi
      apply measure_mono
      rw [sourceUnion_eq_iUnion_shading_of_weights_one D hw]
      exact Set.subset_iUnion (fun j => D.shading j) i
    _ = _ := by simp

/-- Radius-one carrier AD gives a lower bound on the ACTUAL original tube count. -/
lemma carrier_count_lower {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) :
    (ENNReal.ofReal D.thickness).rpow (eta - 3) ≤ (n : ℝ≥0∞) := by
  obtain ⟨hi, _hg, _hnrm⟩ := h
  obtain ⟨hn, hd, hd1, _hdy, _hv, _hw, _hm, _hcub, _hsub, _hsep, hAD, _hCW, _hden⟩ := hi
  let e := ENNReal.ofReal D.thickness
  have he0 : e ≠ 0 := by dsimp [e]; positivity
  have heT : e ≠ ⊤ := ENNReal.ofReal_ne_top
  have hball := (hAD ⟨0, hn⟩ 1 hd1 le_rfl).1
  have hc : wzCarrierBallCount D ⟨0, hn⟩ 1 ≤ n := by
    simpa [wzCarrierBallCount] using
      (card_filter_le (s := (univ : Finset (Fin n)))
        (p := fun j => dist (wzCarrierPoint D j) (wzCarrierPoint D ⟨0, hn⟩) ≤ 1))
  have hinv : ENNReal.ofReal (1 / D.thickness) = e⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos hd]
    simp [e]
  rw [hinv] at hball
  have heq : e.rpow eta * (e⁻¹) ^ 3 = e.rpow (eta - 3) := by
    simp only [ENNReal.rpow_eq_pow]
    rw [← ENNReal.rpow_natCast (e⁻¹) 3, ENNReal.inv_rpow,
      ← ENNReal.rpow_neg, ← ENNReal.rpow_add _ _ he0 heT]
    congr 1
  change e.rpow eta * (e⁻¹) ^ 3 ≤ _ at hball
  rw [heq] at hball
  exact hball.trans (by exact_mod_cast hc)

lemma total_tube_lower {n : ℕ} {D : FiniteScaleSource n} {beta : ℝ}
    (htube : ∀ i, (ENNReal.ofReal D.thickness).rpow (3 + beta) ≤
      volume (markedUnitTube (D.line i) D.thickness)) :
    (n : ℝ≥0∞) * (ENNReal.ofReal D.thickness).rpow (3 + beta) ≤ wzTotalTubeVolume D := by
  simpa [wzTotalTubeVolume] using sum_le_sum (s := univ) (fun i _hi => htube i)

/-- Actual density plus actual radius-one carrier counts produces the total
original shading mass used in the near-extremizer multiplicity calculation. -/
lemma total_shading_lower {n : ℕ} {D : FiniteScaleSource n} {eta beta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (htube : ∀ i, (ENNReal.ofReal D.thickness).rpow (3 + beta) ≤
      volume (markedUnitTube (D.line i) D.thickness)) :
    (ENNReal.ofReal D.thickness).rpow (2 * eta + beta) ≤ wzTotalShadingVolume D := by
  let e := ENNReal.ofReal D.thickness
  have hd : 0 < D.thickness := h.1.2.1
  have he0 : e ≠ 0 := by dsimp [e]; positivity
  have heT : e ≠ ⊤ := ENNReal.ofReal_ne_top
  have hden := h.1.2.2.2.2.2.2.2.2.2.2.2.2
  calc
    e.rpow (2 * eta + beta) = e.rpow eta * (e.rpow (eta - 3) * e.rpow (3 + beta)) := by
      simp only [ENNReal.rpow_eq_pow]
      rw [← ENNReal.rpow_add _ _ he0 heT, ← ENNReal.rpow_add _ _ he0 heT]
      congr 1
      ring
    _ ≤ e.rpow eta * ((n : ℝ≥0∞) * e.rpow (3 + beta)) :=
      mul_le_mul' le_rfl (mul_le_mul' (carrier_count_lower h) le_rfl)
    _ ≤ e.rpow eta * wzTotalTubeVolume D := mul_le_mul' le_rfl (total_tube_lower htube)
    _ ≤ wzTotalShadingVolume D := hden

/-- A nonempty finite family and shading density already give a trivial
volume lower bound of order delta^(3+eta+beta), with no Kakeya axiom. -/
lemma union_volume_lower {n : ℕ} {D : FiniteScaleSource n} {eta beta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (htube : ∀ i, (ENNReal.ofReal D.thickness).rpow (3 + beta) ≤
      volume (markedUnitTube (D.line i) D.thickness)) :
    (ENNReal.ofReal D.thickness).rpow (3 + eta + beta) ≤ volume (sourceUnion D) := by
  obtain ⟨hi, _hg, _hnrm⟩ := h
  obtain ⟨hn, hd, _hd1, _hdy, _hv, hw, _hm, _hcub, _hsub, _hsep, _hAD, _hCW, hden⟩ := hi
  let e := ENNReal.ofReal D.thickness
  have he0 : e ≠ 0 := by dsimp [e]; positivity
  have heT : e ≠ ⊤ := ENNReal.ofReal_ne_top
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hnT : (n : ℝ≥0∞) ≠ ⊤ := by simp
  have hmul : (n : ℝ≥0∞) * e.rpow (3 + eta + beta) ≤
      (n : ℝ≥0∞) * volume (sourceUnion D) := by
    calc
      _ = e.rpow eta * ((n : ℝ≥0∞) * e.rpow (3 + beta)) := by
        simp only [ENNReal.rpow_eq_pow]
        rw [← mul_assoc, mul_comm (e ^ eta) (n : ℝ≥0∞), mul_assoc,
          ← ENNReal.rpow_add _ _ he0 heT]
        congr 2
        ring
      _ ≤ e.rpow eta * wzTotalTubeVolume D := mul_le_mul' le_rfl (total_tube_lower htube)
      _ ≤ wzTotalShadingVolume D := hden
      _ ≤ _ := total_shading_le_card_mul_union D hw
  exact (ENNReal.mul_le_mul_iff_left hn0 hnT).mp (by simpa [mul_comm] using hmul)
end NativeFiniteKakeyaCounts
