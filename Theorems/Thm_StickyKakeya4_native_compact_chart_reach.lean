import Theorems.Thm_StickyKakeya4_native_original_parent_count
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeCompactChartReach
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeOriginalParentCount

lemma height_offset_le_of_mark (line : MarkedLine) (hv : IsValidLine line)
    (hc : (1/2:ℝ) ≤ direction line (3:Fin 4)) {a B : ℝ}
    (ha : wzGraphTime line a-mark line ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (hm : |mark line| ≤ B) : |a-offset line (3:Fin 4)| ≤ B+1/2 := by
  let t := wzGraphTime line a-mark line
  have hp : 0 < direction line (3:Fin 4) := by linarith
  have ht : |t|≤1/2 := abs_le.mpr ha
  have hdir : |direction line (3:Fin 4)| ≤ 1 := by
    simpa [hv.1] using coordinate_abs_le_norm (direction line) (3:Fin 4)
  have he : a-offset line (3:Fin 4)=(mark line+t)*direction line (3:Fin 4) := by
    dsimp [t,wzGraphTime]
    field_simp
    ring
  rw [he,abs_mul]
  calc
    _ ≤ (|mark line|+|t|)*1 := mul_le_mul (abs_add_le _ _) hdir (abs_nonneg _) (by positivity)
    _ ≤ B+1/2 := by nlinarith

/-- The original affine marks give the missing chart constant, uniformly over
all original cells and all choices of a common height. -/
theorem chartReach_le_of_marks {n : ℕ} {D : FiniteScaleSource n} {eta a B : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (hB : 0 ≤ B) (hm : ∀ i, |mark (D.line i)|≤B) :
    (chartReach D a:ℝ) ≤ B+1 := by
  have hd : 0 < mesh D := half_pos h.1.2.1
  have hd1 : mesh D≤1/2 := by dsimp [mesh]; linarith [h.1.2.2.1]
  have hreach (i : Fin n) :
      |((shift D a:ℤ):ℝ)*mesh D-offset (D.line i) (3:Fin 4)|≤B+1 := by
    have hlo : ((shift D a:ℤ):ℝ)*mesh D≤a :=
      (le_div_iff₀ hd).mp (Int.floor_le (a/mesh D))
    have hhi : a<(((shift D a:ℤ):ℝ)+1)*mesh D :=
      (div_lt_iff₀ hd).mp (Int.lt_floor_add_one (a/mesh D))
    have hround : |((shift D a:ℤ):ℝ)*mesh D-a| ≤ mesh D :=
      abs_le.mpr ⟨by nlinarith,by linarith⟩
    have hheight := height_offset_le_of_mark (D.line i) (h.1.2.2.2.2.1 i)
      (h.2.1.1 i) (ha i) (hm i)
    exact (abs_sub_le _ a _).trans (by linarith)
  have hh : chartReach D a ≤ (⟨B+1,by linarith⟩ : NNReal) := by
    apply Finset.sup_le
    intro i _hi
    exact hreach i
  exact hh

/-- Compactness of the original marked source supplies one finite mark bound
before the dyadic scale or a retained finite family is chosen. -/
theorem compact_uniform_chartReach (K : Set MarkedLine) (hK : IsCompact K) :
    ∃ M : ℝ, 0 < M ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta a : ℝ),
      IsWangZakharovNativeFiniteInput D eta → (∀ i, D.line i∈K) →
      (∀ i, wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) →
      (chartReach D a:ℝ)≤M := by
  have hc : Continuous (fun line : MarkedLine=>mark line) := by unfold mark; fun_prop
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 0+1,by positivity,?_⟩
  intro n D eta a h hDK ha
  apply chartReach_le_of_marks h ha (le_max_right B 0)
  intro i
  have hh : |mark (D.line i)| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB (D.line i) (hDK i)
  exact hh.trans (le_max_left B 0)

end NativeCompactChartReach
