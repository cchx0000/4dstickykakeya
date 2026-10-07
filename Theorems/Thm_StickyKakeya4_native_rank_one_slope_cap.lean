import Theorems.Thm_StickyKakeya4_native_direction_rank_dichotomy
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section

namespace NativeRankOneSlopeCap
open Classical Finset StickyKakeya4 NativeDirectionRankDichotomy
open NativeOriginalCellChartGeometry NativeCommonCubicalMesh

/-- A rank-one linear subspace meets the bounded affine chart `x₃ = 1`
in a quantitative cap. The subspace is the actual concentration witness. -/
theorem rank_one_cap (P : Submodule ℝ E4) (hP : Module.finrank ℝ P ≤ 1)
    (u v : E4) (B r : ℝ) (hu : u (3 : Fin 4) = 1) (hv : v (3 : Fin 4) = 1)
    (huB : ‖u‖ ≤ B) (hvB : ‖v‖ ≤ B) (hr : 0 < r) (hrsmall : r ≤ 1 / 4)
    (huP : Metric.infDist u (P : Set E4) ≤ r)
    (hvP : Metric.infDist v (P : Set E4) ≤ r) :
    ‖u - v‖ ≤ 16 * (B + 1) * r := by
  have hne : (P : Set E4).Nonempty := ⟨0, P.zero_mem⟩
  obtain ⟨x, hxP, hux⟩ := (Metric.infDist_lt_iff hne).mp
    (lt_of_le_of_lt huP (by linarith : r < 2 * r))
  obtain ⟨y, hyP, hvy⟩ := (Metric.infDist_lt_iff hne).mp
    (lt_of_le_of_lt hvP (by linarith : r < 2 * r))
  have huxn : ‖u - x‖ ≤ 2 * r := by simpa only [dist_eq_norm] using hux.le
  have hvyn : ‖v - y‖ ≤ 2 * r := by simpa only [dist_eq_norm] using hvy.le
  have hx3 : |1 - x (3 : Fin 4)| ≤ 2 * r := by
    simpa only [PiLp.sub_apply, hu] using
      (coordinate_abs_le_norm (u - x) (3 : Fin 4)).trans huxn
  have hy3 : |1 - y (3 : Fin 4)| ≤ 2 * r := by
    simpa only [PiLp.sub_apply, hv] using
      (coordinate_abs_le_norm (v - y) (3 : Fin 4)).trans hvyn
  have hxpos : 1 / 2 ≤ x (3 : Fin 4) := by
    have hh := (abs_le.mp hx3).2
    linarith
  have hx0 : x ≠ 0 := by
    intro hh
    have he : x (3 : Fin 4) = 0 := by simp only [hh, PiLp.zero_apply]
    linarith
  have hPne : P ≠ ⊥ := by
    intro hh
    apply hx0
    have hxP' : x ∈ P := hxP
    rw [hh] at hxP'
    exact (Submodule.mem_bot ℝ).mp hxP'
  have hPone : Module.finrank ℝ P = 1 :=
    Nat.le_antisymm hP (Submodule.one_le_finrank_iff.mpr hPne)
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hPone hxP hx0
  rw [hspan] at hyP
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hyP
  have hty : t * x (3 : Fin 4) = y (3 : Fin 4) := by
    simpa only [PiLp.smul_apply, smul_eq_mul] using congrArg (fun z : E4 => z (3 : Fin 4)) ht
  have hxy3 : |y (3 : Fin 4) - x (3 : Fin 4)| ≤ 4 * r := by
    calc
      _ ≤ |y (3 : Fin 4) - 1| + |1 - x (3 : Fin 4)| := abs_sub_le _ _ _
      _ ≤ 2 * r + 2 * r := add_le_add (by simpa only [abs_sub_comm] using hy3) hx3
      _ = _ := by ring
  have htprod : |t - 1| * x (3 : Fin 4) ≤ 4 * r := by
    calc
      _ = |(t - 1) * x (3 : Fin 4)| := by
        rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ x (3 : Fin 4))]
      _ = |y (3 : Fin 4) - x (3 : Fin 4)| := by congr 1; nlinarith only [hty]
      _ ≤ _ := hxy3
  have ht1 : |t - 1| ≤ 8 * r := by
    have hh := mul_le_mul_of_nonneg_left hxpos (abs_nonneg (t - 1))
    nlinarith
  have hB : 0 ≤ B := (norm_nonneg v).trans hvB
  have hxB : ‖x‖ ≤ B + 1 := by
    have hh := norm_le_insert u x
    linarith
  have hxy : ‖x - y‖ ≤ 8 * r * (B + 1) := by
    have he : x - y = (1 - t) • x := by rw [sub_smul, one_smul, ht]
    rw [he, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (by simpa only [abs_sub_comm] using ht1) hxB
      (norm_nonneg _) (by positivity)
  calc
    ‖u - v‖ ≤ ‖u - x‖ + ‖x - y‖ + ‖y - v‖ := by
      have htri : dist u v ≤ dist u x + dist x y + dist y v := by
        calc
          _ ≤ dist u x + dist x v := dist_triangle _ _ _
          _ ≤ dist u x + (dist x y + dist y v) := add_le_add le_rfl (dist_triangle _ _ _)
          _ = _ := by ring
      simpa only [dist_eq_norm] using htri
    _ ≤ 2 * r + 8 * r * (B + 1) + 2 * r := by
      exact add_le_add (add_le_add huxn hxy) (by simpa only [norm_sub_rev] using hvyn)
    _ ≤ 16 * (B + 1) * r := by nlinarith [mul_nonneg hB hr.le]

/-- The center is a genuine retained label in the concentrated set. -/
theorem near_labels_cap {α : Type*} [DecidableEq α] (A : Finset α) (v : α → E4)
    (P : Submodule ℝ E4) (hP : Module.finrank ℝ P ≤ 1) (B r : ℝ)
    (hr : 0 < r) (hrsmall : r ≤ 1 / 4)
    (hlast : ∀ i ∈ A, v i (3 : Fin 4) = 1) (hB : ∀ i ∈ A, ‖v i‖ ≤ B)
    (hne : (nearLabels A v r P).Nonempty) :
    ∃ i ∈ nearLabels A v r P, ∀ j ∈ nearLabels A v r P,
      ‖v j - v i‖ ≤ 16 * (B + 1) * r := by
  obtain ⟨i, hi⟩ := hne
  refine ⟨i, hi, ?_⟩
  intro j hj
  have hi' := mem_filter.mp hi
  have hj' := mem_filter.mp hj
  exact rank_one_cap P hP (v j) (v i) B r (hlast j hj'.1) (hlast i hi'.1)
    (hB j hj'.1) (hB i hi'.1) hr hrsmall hj'.2 hi'.2

lemma slopeVector_eq_normalized_direction {n : ℕ} (D : FiniteScaleSource n) (i : Fin n)
    (hc : direction (D.line i) (3 : Fin 4) ≠ 0) :
    slopeVector D i = (direction (D.line i) (3 : Fin 4))⁻¹ • direction (D.line i) := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · change 1 = (direction (D.line i) (3 : Fin 4))⁻¹ * direction (D.line i) (3 : Fin 4)
    exact (inv_mul_cancel₀ hc).symm
  · simp only [slopeVector, ActualSlopeSource.heightPoint_castSucc]
    change slope (D.line i) k =
      (direction (D.line i) (3 : Fin 4))⁻¹ * direction (D.line i) k.castSucc
    simp only [NativeOriginalCellChartGeometry.slope, div_eq_mul_inv, mul_comm]

lemma slopeVector_norm_le_two {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (i : Fin n) : ‖slopeVector D i‖ ≤ 2 := by
  have hc := h.2.1.1 i
  have hp : 0 < direction (D.line i) (3 : Fin 4) := by linarith
  rw [slopeVector_eq_normalized_direction D i hp.ne', norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hp), (h.1.2.2.2.2.1 i).1, mul_one]
  simpa only [one_div] using
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hc).trans_eq
      (by norm_num : (1 : ℝ) / (1 / 2) = 2)

/-- All actual slope vectors in the rank-one concentration lie in a radius
`48r` cap centered at an actual original retained label. -/
theorem actual_slope_cap {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (A : Finset (Fin n))
    (P : Submodule ℝ E4) (hP : Module.finrank ℝ P ≤ 1) (r : ℝ)
    (hr : 0 < r) (hrsmall : r ≤ 1 / 4)
    (hne : (nearLabels A (slopeVector D) r P).Nonempty) :
    ∃ i ∈ nearLabels A (slopeVector D) r P,
      ∀ j ∈ nearLabels A (slopeVector D) r P,
        ‖slopeVector D j - slopeVector D i‖ ≤ 48 * r ∧
        ∀ k : Fin 3, |slope (D.line j) k - slope (D.line i) k| ≤ 48 * r := by
  obtain ⟨i, hi, hcap⟩ := near_labels_cap A (slopeVector D) P hP 2 r hr hrsmall
    (fun i _hi => slopeVector_last D i) (fun i _hi => slopeVector_norm_le_two h i) hne
  refine ⟨i, hi, ?_⟩
  intro j hj
  have hjcap : ‖slopeVector D j - slopeVector D i‖ ≤ 48 * r := by
    convert hcap j hj using 1
    norm_num
  refine ⟨hjcap, ?_⟩
  intro k
  simpa only [PiLp.sub_apply, slopeVector, ActualSlopeSource.heightPoint_castSucc] using
    (coordinate_abs_le_norm (slopeVector D j - slopeVector D i) k.castSucc).trans hjcap

end NativeRankOneSlopeCap
