import Mathlib
set_option autoImplicit false
set_option warningAsError true
open Set MeasureTheory
open scoped BigOperators
namespace GridPaddingTranslation

noncomputable def candidates (b h : ℝ) : Finset ℤ :=
  Finset.Icc (⌊b / h⌋ - 1) (⌊(b + 1) / h⌋ + 1)

def bad (b h H : ℝ) : Set ℝ :=
  {z | z ∈ Icc 0 1 ∧ ∃ k : ℤ, |b + z - k * h| < h / H}

theorem candidates_card (b h : ℝ) (hh : 0 < h) :
    ((candidates b h).card : ℝ) ≤ 1 / h + 4 := by
  have hm : ⌊b / h⌋ ≤ ⌊(b + 1) / h⌋ := Int.floor_mono (by gcongr; linarith)
  have hc := Int.card_Icc_of_le (a := ⌊b / h⌋ - 1)
    (b := ⌊(b + 1) / h⌋ + 1) (by omega)
  have hc' : ((candidates b h).card : ℝ) =
      (⌊(b + 1) / h⌋ : ℝ) - (⌊b / h⌋ : ℝ) + 3 := by
    have hc'' : ((candidates b h).card : ℝ) =
        (⌊(b + 1) / h⌋ : ℝ) + 1 + 1 - ((⌊b / h⌋ : ℝ) - 1) := by
      exact_mod_cast hc
    linarith
  rw [hc']
  have h₁ := Int.floor_le ((b + 1) / h)
  have h₂ := Int.lt_floor_add_one (b / h)
  have he : (b + 1) / h = b / h + 1 / h := add_div b 1 h
  linarith

theorem bad_subset_cover (b h H : ℝ) (hh : 0 < h) (hH : 1 ≤ H) :
    bad b h H ⊆ ⋃ k ∈ candidates b h,
      Icc ((k : ℝ) * h - b - h / H) ((k : ℝ) * h - b + h / H) := by
  intro z hz
  obtain ⟨hz, k, hk⟩ := hz
  have hHpos : 0 < H := by linarith
  have heps : h / H ≤ h := (div_le_iff₀ hHpos).2 (by nlinarith)
  have habs := abs_lt.mp hk
  have hf₁ := Int.floor_le (b / h)
  have hf₂ := Int.lt_floor_add_one ((b + 1) / h)
  have hf₁' : (⌊b / h⌋ : ℝ) * h ≤ b := (le_div_iff₀ hh).1 hf₁
  have hf₂' : b + 1 < ((⌊(b + 1) / h⌋ : ℝ) + 1) * h :=
    (div_lt_iff₀ hh).1 hf₂
  have hlo : ⌊b / h⌋ - 1 ≤ k := by
    have : (⌊b / h⌋ : ℝ) - 1 ≤ (k : ℝ) := by nlinarith [hz.1]
    exact_mod_cast this
  have hhi : k ≤ ⌊(b + 1) / h⌋ + 1 := by
    have : (k : ℝ) < (⌊(b + 1) / h⌋ : ℝ) + 2 := by nlinarith [hz.2]
    have : k < ⌊(b + 1) / h⌋ + 2 := by exact_mod_cast this
    omega
  refine mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨?_, ?_⟩⟩
  · exact Finset.mem_Icc.2 ⟨hlo, hhi⟩
  · constructor <;> linarith

theorem measure_bad_le (b h H : ℝ) (hh : 0 < h) (hh₁ : h ≤ 1) (hH : 1 ≤ H) :
    volume (bad b h H) ≤ ENNReal.ofReal (10 / H) := by
  have hHpos : 0 < H := by linarith
  calc
    volume (bad b h H) ≤ volume (⋃ k ∈ candidates b h,
        Icc ((k : ℝ) * h - b - h / H) ((k : ℝ) * h - b + h / H)) :=
      measure_mono (bad_subset_cover b h H hh hH)
    _ ≤ ∑ k ∈ candidates b h,
        volume (Icc ((k : ℝ) * h - b - h / H) ((k : ℝ) * h - b + h / H)) :=
      measure_biUnion_finset_le _ _
    _ = ENNReal.ofReal (((candidates b h).card : ℝ) * (2 * h / H)) := by
      simp only [Real.volume_Icc]
      simp_rw [show ∀ k : ℤ, (k : ℝ) * h - b + h / H -
          ((k : ℝ) * h - b - h / H) = 2 * h / H by intro k; ring]
      simp [ENNReal.ofReal_mul, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (10 / H) := by
      apply ENNReal.ofReal_le_ofReal
      have hc := candidates_card b h hh
      rw [← mul_div_assoc]
      apply (div_le_div_iff_of_pos_right hHpos).2
      have he : (1 / h + 4) * (2 * h) = 2 + 8 * h := by field_simp; ring
      calc
        ((candidates b h).card : ℝ) * (2 * h) ≤ (1 / h + 4) * (2 * h) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        _ = 2 + 8 * h := he
        _ ≤ 10 := by linarith


theorem measurableSet_bad (b h H : ℝ) : MeasurableSet (bad b h H) := by
  have he : bad b h H = Icc 0 1 ∩ ⋃ k : ℤ, {z : ℝ | |b + z - k * h| < h / H} := by
    ext z
    simp [bad]
  rw [he]
  refine measurableSet_Icc.inter (MeasurableSet.iUnion fun k => ?_)
  exact measurableSet_lt (by fun_prop) measurable_const

/-- Finite weighted first-moment selection retains the original labels and weights. -/
theorem weighted_avoid {α : Type*} (A : Finset α) (w : α → ℕ)
    (E : α → Set ℝ) (hE : ∀ a ∈ A, MeasurableSet (E a))
    (p : ℝ) (hp₀ : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hμ : ∀ a ∈ A, volume (E a) ≤ ENNReal.ofReal p) :
    ∃ z ∈ Icc (0 : ℝ) 1, ∃ B : Finset α, B ⊆ A ∧
      (∑ a ∈ A, w a) ≤ 2 * (∑ a ∈ B, w a) ∧ ∀ a ∈ B, z ∉ E a := by
  classical
  let μ : Measure ℝ := volume.restrict (Icc 0 1)
  have : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
  let f : ℝ → ℝ := fun z => ∑ a ∈ A, (E a).indicator (fun _ => (w a : ℝ)) z
  have hi (a : α) (ha : a ∈ A) :
      Integrable ((E a).indicator (fun _ : ℝ => (w a : ℝ))) μ :=
    (integrable_const _).indicator (hE a ha)
  have hf : Integrable f μ := integrable_finsetSum A hi
  have hint : (∫ z, f z ∂μ) ≤ p * ∑ a ∈ A, (w a : ℝ) := by
    rw [show (∫ z, f z ∂μ) = ∑ a ∈ A,
        ∫ z, (E a).indicator (fun _ => (w a : ℝ)) z ∂μ from integral_finsetSum A hi]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [integral_indicator_const _ (hE a ha), smul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact ENNReal.toReal_le_of_le_ofReal hp₀
      ((Measure.restrict_apply_le (μ := volume) (s := Icc 0 1) (t := E a)).trans (hμ a ha))
  obtain ⟨z, hz, hfz⟩ := exists_notMem_null_le_integral hf
    (show μ ((Icc (0 : ℝ) 1)ᶜ) = 0 by simp [μ])
  have hbound : f z ≤ (∑ a ∈ A, (w a : ℝ)) / 2 := by
    have hw : 0 ≤ ∑ a ∈ A, (w a : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
    calc
      f z ≤ p * ∑ a ∈ A, (w a : ℝ) := hfz.trans hint
      _ ≤ (1 / 2) * ∑ a ∈ A, (w a : ℝ) := mul_le_mul_of_nonneg_right hp hw
      _ = _ := by ring
  let B : Finset α := A.filter (fun a => z ∉ E a)
  have hpart : f z + ∑ a ∈ B, (w a : ℝ) = ∑ a ∈ A, (w a : ℝ) := by
    have h := Finset.sum_filter_add_sum_filter_not A (fun a => z ∈ E a)
      (fun a => (w a : ℝ))
    simpa [f, B, Finset.sum_filter, Set.indicator_apply] using h
  refine ⟨z, by simpa using hz, B, Finset.filter_subset _ _, ?_, ?_⟩
  · have : (∑ a ∈ A, (w a : ℝ)) ≤ 2 * ∑ a ∈ B, (w a : ℝ) := by linarith
    exact_mod_cast this
  · intro a ha
    exact (Finset.mem_filter.1 ha).2


theorem measure_bad_iUnion_le {τ : Type*} [Fintype τ] (b h : τ → ℝ) (H : ℝ)
    (hh : ∀ t, 0 < h t) (hh₁ : ∀ t, h t ≤ 1) (hH : 1 ≤ H) :
    volume (⋃ t, bad (b t) (h t) H) ≤
      ENNReal.ofReal (10 * (Fintype.card τ : ℝ) / H) := by
  calc
    volume (⋃ t, bad (b t) (h t) H) ≤ ∑ t, volume (bad (b t) (h t) H) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _t : τ, ENNReal.ofReal (10 / H) :=
      Finset.sum_le_sum fun t _ => measure_bad_le (b t) (h t) H (hh t) (hh₁ t) hH
    _ = ENNReal.ofReal (10 * (Fintype.card τ : ℝ) / H) := by
      rw [show 10 * (Fintype.card τ : ℝ) / H = (Fintype.card τ : ℝ) * (10 / H) by ring]
      simp [ENNReal.ofReal_mul, nsmul_eq_mul]

/-- One common scalar translation pads every retained original label at every scale. -/
theorem weighted_translation {α τ : Type*} [Fintype τ]
    (A : Finset α) (w : α → ℕ) (b : α → τ → ℝ) (h : τ → ℝ) (H : ℝ)
    (hh : ∀ t, 0 < h t) (hh₁ : ∀ t, h t ≤ 1) (hH : 1 ≤ H)
    (hsize : 20 * (Fintype.card τ : ℝ) ≤ H) :
    ∃ z ∈ Icc (0 : ℝ) 1, ∃ B : Finset α, B ⊆ A ∧
      (∑ a ∈ A, w a) ≤ 2 * (∑ a ∈ B, w a) ∧
      ∀ a ∈ B, ∀ t : τ, ∀ k : ℤ, h t / H ≤ |b a t + z - k * h t| := by
  have hHpos : 0 < H := by linarith
  let E : α → Set ℝ := fun a => ⋃ t, bad (b a t) (h t) H
  have hE : ∀ a ∈ A, MeasurableSet (E a) :=
    fun a _ => MeasurableSet.iUnion fun t => measurableSet_bad (b a t) (h t) H
  have hp : 10 * (Fintype.card τ : ℝ) / H ≤ 1 / 2 := by
    apply (div_le_iff₀ hHpos).2
    linarith
  obtain ⟨z, hz, B, hBA, hw, havoid⟩ := weighted_avoid A w E hE
    (10 * (Fintype.card τ : ℝ) / H) (by positivity) hp
    (fun a _ => measure_bad_iUnion_le (b a) h H hh hh₁ hH)
  refine ⟨z, hz, B, hBA, hw, ?_⟩
  intro a ha t k
  apply le_of_not_gt
  intro hbad
  exact havoid a ha (mem_iUnion.2 ⟨t, hz, k, hbad⟩)

/-- A vector shift in the unit cube retaining at least half of any integer weight.
A single diagonal shift suffices; the coordinates need not be sampled independently. -/
theorem weighted_vector_translation {α : Type*} (r m : ℕ)
    (A : Finset α) (w : α → ℕ) (b : α → Fin r → ℝ) (h : Fin m → ℝ) (H : ℝ)
    (hh : ∀ j, 0 < h j) (hh₁ : ∀ j, h j ≤ 1) (hH : 1 ≤ H)
    (hsize : 20 * (r : ℝ) * (m : ℝ) ≤ H) :
    ∃ z : Fin r → ℝ, (∀ i, z i ∈ Icc 0 1) ∧
      ∃ B : Finset α, B ⊆ A ∧ (∑ a ∈ A, w a) ≤ 2 * (∑ a ∈ B, w a) ∧
        ∀ a ∈ B, ∀ i : Fin r, ∀ j : Fin m, ∀ k : ℤ,
          h j / H ≤ |b a i + z i - k * h j| := by
  obtain ⟨z, hz, B, hBA, hw, hpad⟩ := weighted_translation
    (τ := Fin r × Fin m) A w (fun a t => b a t.1) (fun t => h t.2) H
    (fun t => hh t.2) (fun t => hh₁ t.2) hH (by simpa [mul_assoc] using hsize)
  exact ⟨fun _ => z, fun _ => hz, B, hBA, hw, fun a ha i j k => hpad a ha (i, j) k⟩

end GridPaddingTranslation
