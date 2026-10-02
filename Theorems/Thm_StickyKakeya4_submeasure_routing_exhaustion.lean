import Theorems.Thm_StickyKakeya4_markov_endpoint_preservation
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Tactic.Linarith

/-!
# Qualitative exhaustion by genuine submeasures

A finite occurrence measure can be exhausted by countably many eligible
submeasures if every nonzero submeasure contains a nonzero eligible
submeasure. Eligibility need not be inherited by arbitrary restrictions.
The pieces are the actual, unnormalized successful outputs: neither a
uniform retained fraction nor conditioning by an inverse success probability
is used. This supplies no quantitative decay rate, generation bound, or
paid/cross-cap estimate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.SubmeasureRoutingExhaustion

variable {Ω L Y : Type*} [MeasurableSpace Ω] [MeasurableSpace L] [MeasurableSpace Y]

/-- Among eligible submeasures of a finite measure, choose one with at least
half the mass of every eligible candidate. This is an absolute comparison
with the eligible supremum, not a fixed retained fraction of the remainder. -/
theorem exists_half_maximal_submeasure (ν : Measure Ω) [IsFiniteMeasure ν]
    (P : Measure Ω → Prop) (hzero : P 0) :
    ∃ θ : Measure Ω, θ ≤ ν ∧ P θ ∧
      ∀ η : Measure Ω, η ≤ ν → P η →
        (η univ).toReal ≤ 2 * (θ univ).toReal := by
  let S : Set ℝ := {r | ∃ η : Measure Ω, η ≤ ν ∧ P η ∧ r = (η univ).toReal}
  have hSzero : (0 : ℝ) ∈ S := ⟨0, bot_le, hzero, by simp⟩
  have hSbdd : BddAbove S := by
    refine ⟨(ν univ).toReal, ?_⟩
    rintro r ⟨η, hην, _, rfl⟩
    exact ENNReal.toReal_mono (measure_ne_top ν univ) (hην univ)
  have hSnonneg : 0 ≤ sSup S := le_csSup hSbdd hSzero
  by_cases hS : sSup S = 0
  · refine ⟨0, bot_le, hzero, ?_⟩
    intro η hην hηP
    have hle := le_csSup hSbdd (show (η univ).toReal ∈ S from ⟨η, hην, hηP, rfl⟩)
    simpa [hS] using hle
  · have hhalf : sSup S / 2 < sSup S := by
      have hpos : 0 < sSup S := lt_of_le_of_ne hSnonneg (Ne.symm hS)
      linarith
    obtain ⟨r, ⟨θ, hθν, hθP, hr⟩, hnear⟩ := exists_lt_of_lt_csSup ⟨0, hSzero⟩ hhalf
    refine ⟨θ, hθν, hθP, ?_⟩
    intro η hην hηP
    have hle := le_csSup hSbdd (show (η univ).toReal ∈ S from ⟨η, hην, hηP, rfl⟩)
    rw [hr] at hnear
    linarith

/-- Positive hereditary availability exhausts the original finite occurrence
as an equality of measures. Only availability, not hereditary eligibility,
is assumed. The zero measure is an allowed padding output. -/
theorem exists_submeasure_routing_exhaustion
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : Measure Ω → Prop) (hzero : P 0)
    (hlocal : ∀ ν : Measure Ω, ν ≤ μ → ν ≠ 0 →
      ∃ θ : Measure Ω, θ ≤ ν ∧ P θ ∧ θ ≠ 0) :
    ∃ θ : ℕ → Measure Ω, (∀ n, P (θ n)) ∧ Measure.sum θ = μ := by
  classical
  let M := {ν : Measure Ω // ν ≤ μ}
  have hchoice (ν : M) : ∃ θ : Measure Ω, θ ≤ ν.val ∧ P θ ∧
      ∀ η : Measure Ω, η ≤ ν.val → P η →
        (η univ).toReal ≤ 2 * (θ univ).toReal := by
    let : IsFiniteMeasure ν.val := isFiniteMeasure_of_le μ ν.property
    exact exists_half_maximal_submeasure ν.val P hzero
  let pick (ν : M) : Measure Ω := Classical.choose (hchoice ν)
  have hpick (ν : M) : pick ν ≤ ν.val ∧ P (pick ν) ∧
      ∀ η : Measure Ω, η ≤ ν.val → P η →
        (η univ).toReal ≤ 2 * (pick ν univ).toReal := Classical.choose_spec (hchoice ν)
  let step (ν : M) : M := ⟨ν.val - pick ν, Measure.sub_le.trans ν.property⟩
  let R : ℕ → M := fun n => (step^[n]) ⟨μ, le_rfl⟩
  let θ : ℕ → Measure Ω := fun n => pick (R n)
  have hRzero : (R 0).val = μ := rfl
  have hRsucc (n : ℕ) : (R (n + 1)).val = (R n).val - θ n := by
    simp only [R, Function.iterate_succ_apply', step, θ]
  have hθle (n : ℕ) : θ n ≤ (R n).val := (hpick (R n)).1
  have hθP (n : ℕ) : P (θ n) := (hpick (R n)).2.1
  have hθfinite (n : ℕ) : IsFiniteMeasure (θ n) :=
    isFiniteMeasure_of_le μ ((hθle n).trans (R n).property)
  have hconserve (n : ℕ) : (R n).val + ∑ i ∈ Finset.range n, θ i = μ := by
    induction n with
    | zero => simpa only [Finset.range_zero, Finset.sum_empty, add_zero] using hRzero
    | succ n ih =>
      calc
        (R (n + 1)).val + ∑ i ∈ Finset.range (n + 1), θ i =
            ((R n).val - θ n + θ n) + ∑ i ∈ Finset.range n, θ i := by
          rw [hRsucc, Finset.sum_range_succ]
          ac_rfl
        _ = μ := by rw [Measure.sub_add_cancel_of_le (hθle n)]; exact ih
  have hpartial_le (n : ℕ) : (∑ i ∈ Finset.range n, θ i) ≤ μ := by
    rw [← hconserve n]
    exact Measure.le_add_left le_rfl
  have hsum_le : Measure.sum θ ≤ μ := by
    apply Measure.le_iff.mpr
    intro s hs
    rw [Measure.sum_apply θ hs]
    apply ENNReal.tsum_le_of_sum_range_le
    intro n
    simpa only [Measure.finsetSum_apply] using hpartial_le n s
  have hpartial_sum (n : ℕ) : (∑ i ∈ Finset.range n, θ i) ≤ Measure.sum θ := by
    apply Measure.le_iff.mpr
    intro s hs
    rw [Measure.finsetSum_apply, Measure.sum_apply θ hs]
    exact ENNReal.sum_le_tsum (Finset.range n)
  have hremain_le (n : ℕ) : μ - Measure.sum θ ≤ (R n).val := by
    apply Measure.sub_le_of_le_add
    calc
      μ = (R n).val + ∑ i ∈ Finset.range n, θ i := (hconserve n).symm
      _ ≤ (R n).val + Measure.sum θ := add_le_add le_rfl (hpartial_sum n)
  have hremain_zero : μ - Measure.sum θ = 0 := by
    by_contra hnonzero
    obtain ⟨ψ, hψremain, hψP, hψnonzero⟩ :=
      hlocal (μ - Measure.sum θ) Measure.sub_le hnonzero
    have hψμ : ψ ≤ μ := hψremain.trans Measure.sub_le
    have : IsFiniteMeasure ψ := isFiniteMeasure_of_le μ hψμ
    have hψmass : ψ univ ≠ 0 := by
      exact Measure.measure_univ_ne_zero.mpr hψnonzero
    have hpositive : 0 < (ψ univ).toReal :=
      ENNReal.toReal_pos hψmass (measure_ne_top ψ univ)
    let c : ℝ≥0∞ := ENNReal.ofReal ((ψ univ).toReal / 2)
    have hc : c ≠ 0 := by
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
    have hcn (n : ℕ) : c ≤ θ n univ := by
      have hmass := (hpick (R n)).2.2 ψ (hψremain.trans (hremain_le n)) hψP
      apply ENNReal.ofReal_le_of_le_toReal
      dsimp [θ] at hmass ⊢
      linarith
    have htop : (∞ : ℝ≥0∞) ≤ μ univ := by
      calc
        ∞ = ∑' _ : ℕ, c := (ENNReal.tsum_const_eq_top_of_ne_zero hc).symm
        _ ≤ ∑' n, θ n univ := ENNReal.tsum_le_tsum hcn
        _ = Measure.sum θ univ := (Measure.sum_apply θ MeasurableSet.univ).symm
        _ ≤ μ univ := hsum_le univ
    exact (measure_ne_top μ univ) (top_le_iff.mp htop)
  have : IsFiniteMeasure (Measure.sum θ) := isFiniteMeasure_of_le μ hsum_le
  refine ⟨θ, hθP, ?_⟩
  have h := Measure.sub_add_cancel_of_le hsum_le
  rwa [hremain_zero, zero_add] at h

/-- Independently chosen probability labels on the actual exhausted outputs
preserve the whole original occurrence, without conditioning any piece. -/
theorem exhaustive_markov_extensions_preserve_occurrence
    (μ : Measure Ω) (θ : ℕ → Measure Ω) [∀ n, SFinite (θ n)]
    (hidentity : Measure.sum θ = μ)
    (κ : ℕ → Kernel Ω L) [∀ n, IsMarkovKernel (κ n)] :
    Measure.sum (fun n => ((θ n).compProd (κ n)).map Prod.fst) = μ := by
  simpa only [MarkovEndpointPreservation.extension_fst] using hidentity

/-- Every fixed inherited endpoint observable retains its exact original law.
The new label spaces and Markov kernels may vary from one output to another. -/
theorem exhaustive_markov_extensions_preserve_endpoints
    (Labels : ℕ → Type*) [∀ n, MeasurableSpace (Labels n)]
    (μ : Measure Ω) (θ : ℕ → Measure Ω) [∀ n, SFinite (θ n)]
    (hidentity : Measure.sum θ = μ)
    (κ : ∀ n, Kernel Ω (Labels n)) [∀ n, IsMarkovKernel (κ n)]
    (endpoint : Ω → Y) (hendpoint : Measurable endpoint) :
    Measure.sum (fun n => ((θ n).compProd (κ n)).map
      (fun p => endpoint p.1)) = μ.map endpoint := by
  simp_rw [MarkovEndpointPreservation.extension_endpoint _ _ endpoint hendpoint]
  rw [← Measure.map_sum hendpoint.aemeasurable, hidentity]

end StickyKakeya4.SubmeasureRoutingExhaustion
