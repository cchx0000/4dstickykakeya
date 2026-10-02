import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# Compact-front finite-scale Frostman limits

This is the compactness step needed by the original manuscript's family
Frostman escape (Theorem 8.11).  Probability measures carried by one fixed
compact front, with one uniform finite coefficient and ball estimates above
scales tending to zero, have a genuine weak subsequential limit carried by
that same front.  Portmanteau transfers every positive-radius ball bound.
The small-radius coefficient is unchanged; `max C 1` works at all radii.

The finite-scale geometric estimates are explicit hypotheses.  This module
does not prove the manuscript's moving-center family estimate.  Compactness
of the actual ambient front is essential here; support is not replaced by
support in the closure of an arbitrary Borel selector front.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section

namespace StickyKakeya4.CompactFrontLimit

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Prokhorov compactness for probability measures carried by exactly one
fixed compact set.  No externally supplied weak-limit certificate is used. -/
theorem isCompact_probabilities_carried_by {K : Set E} (hK : IsCompact K) :
    IsCompact {μ : ProbabilityMeasure E | (μ : Measure E) Kᶜ = 0} := by
  have hc := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
    (E := E) (u := fun _ : ℕ => (0 : ℝ≥0)) (K := fun _ : ℕ => K)
    tendsto_const_nhds (fun _ => hK) (Or.inr monotone_const)
  have he : {μ : ProbabilityMeasure E | ∀ _n : ℕ, μ Kᶜ ≤ (0 : ℝ≥0)} =
      {μ : ProbabilityMeasure E | (μ : Measure E) Kᶜ = 0} := by
    ext μ
    simp only [mem_ofPred_eq, le_zero_iff, forall_const,
      ProbabilityMeasure.null_iff_toMeasure_null]
  rwa [he] at hc

/-- Portmanteau passes a scale-truncated uniform ball estimate to a supplied
weak limit.  Weak-limit existence is proved separately below by compactness. -/
theorem ball_bound_of_tendsto_finite_scale
    (μs : ℕ → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop (𝓝 0))
    (hμ : Tendsto μs atTop (𝓝 μ)) (C : ℝ≥0∞) (d : ℝ)
    (hball : ∀ n x r, 0 < r → ρ n ≤ r → r ≤ 1 →
      (μs n : Measure E) (Metric.ball x r) ≤ C * (ENNReal.ofReal r) ^ d) :
    ∀ x r, 0 < r → r ≤ 1 →
      (μ : Measure E) (Metric.ball x r) ≤ C * (ENNReal.ofReal r) ^ d := by
  intro x r hr hr1
  have hev : ∀ᶠ n in atTop,
      (μs n : Measure E) (Metric.ball x r) ≤ C * (ENNReal.ofReal r) ^ d := by
    filter_upwards [hρ.eventually_le_const hr] with n hn
    exact hball n x r hr hn hr1
  exact (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ Metric.isOpen_ball).trans
    (Filter.liminf_le_of_frequently_le' hev.frequently)

/-- A genuine convergent subsequence of probability measures supported on a
fixed compact front, retaining both that support and all small-radius bounds. -/
theorem exists_frostman_probability_subseq [TopologicalSpace.SeparableSpace E]
    {K : Set E} (hK : IsCompact K) (μs : ℕ → ProbabilityMeasure E)
    (hsupport : ∀ n, (μs n : Measure E) Kᶜ = 0)
    (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop (𝓝 0)) (C : ℝ≥0∞) (d : ℝ)
    (hball : ∀ n x r, 0 < r → ρ n ≤ r → r ≤ 1 →
      (μs n : Measure E) (Metric.ball x r) ≤ C * (ENNReal.ofReal r) ^ d) :
    ∃ μ : ProbabilityMeasure E, (μ : Measure E) Kᶜ = 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) ∧
        ∀ x r, 0 < r → r ≤ 1 →
          (μ : Measure E) (Metric.ball x r) ≤ C * (ENNReal.ofReal r) ^ d := by
  obtain ⟨μ, hμK, φ, hφ, hconv⟩ :=
    (isCompact_probabilities_carried_by hK).tendsto_subseq hsupport
  refine ⟨μ, hμK, φ, hφ, hconv, ?_⟩
  exact ball_bound_of_tendsto_finite_scale (μs ∘ φ) μ (ρ ∘ φ)
    (hρ.comp hφ.tendsto_atTop) hconv C d
      (fun n x r hr hρr hr1 => hball (φ n) x r hr hρr hr1)

/-- A probability measure's small-radius bound extends to every positive
radius with coefficient `max C 1`. -/
theorem ball_bound_all_radii (μ : ProbabilityMeasure E) (C : ℝ≥0∞)
    (d : ℝ) (hd : 0 < d)
    (hball : ∀ x r, 0 < r → r ≤ 1 →
      (μ : Measure E) (Metric.ball x r) ≤ C * (ENNReal.ofReal r) ^ d) :
    ∀ x r, 0 < r →
      (μ : Measure E) (Metric.ball x r) ≤ max C 1 * (ENNReal.ofReal r) ^ d := by
  intro x r hr
  by_cases hr1 : r ≤ 1
  · exact (hball x r hr hr1).trans (by gcongr; exact le_max_left C 1)
  · have hrpow : (1 : ℝ≥0∞) ≤ (ENNReal.ofReal r) ^ d :=
      ENNReal.one_le_rpow
        (by simpa using ENNReal.ofReal_le_ofReal (le_of_not_ge hr1)) hd
    calc
      (μ : Measure E) (Metric.ball x r) ≤ (μ : Measure E) univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
      _ ≤ max C 1 * (ENNReal.ofReal r) ^ d :=
        one_le_mul_of_one_le_of_one_le (le_max_right C 1) hrpow

/-- Compact-front Frostman compactness in the unbundled measure interface.
The limit is a probability carried by the exact original compact set, and its
ball estimate holds at every positive radius with one finite coefficient. -/
theorem exists_supported_frostman_probability [TopologicalSpace.SeparableSpace E]
    {K : Set E} (hK : IsCompact K) (μs : ℕ → Measure E)
    (hprob : ∀ n, IsProbabilityMeasure (μs n)) (hsupport : ∀ n, μs n Kᶜ = 0)
    (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop (𝓝 0))
    (C : ℝ≥0∞) (hC : C ≠ ∞) (d : ℝ) (hd : 0 < d)
    (hball : ∀ n x r, 0 < r → ρ n ≤ r → r ≤ 1 →
      μs n (Metric.ball x r) ≤ C * (ENNReal.ofReal r) ^ d) :
    ∃ μ : Measure E, IsProbabilityMeasure μ ∧ μ Kᶜ = 0 ∧
      max C 1 ≠ ∞ ∧ ∀ x r, 0 < r →
        μ (Metric.ball x r) ≤ max C 1 * (ENNReal.ofReal r) ^ d := by
  let ps : ℕ → ProbabilityMeasure E := fun n => ⟨μs n, hprob n⟩
  obtain ⟨μ, hμK, _φ, _hφ, _hconv, hμball⟩ :=
    exists_frostman_probability_subseq hK ps hsupport ρ hρ C d hball
  refine ⟨(μ : Measure E), inferInstance, hμK, ?_, ball_bound_all_radii μ C d hd hμball⟩
  finiteness

end StickyKakeya4.CompactFrontLimit
