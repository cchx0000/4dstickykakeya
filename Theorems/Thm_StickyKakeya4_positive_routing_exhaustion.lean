import Theorems.Thm_StickyKakeya4_markov_endpoint_preservation
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Positive hereditary routing exhausts without a uniform retained fraction

For source-hereditary measurable routes, an eligible positive piece in every
positive remainder suffices for a countable exhaustive partition. No fixed
fraction `c` is assumed. The proof uses the measurable essential union of all
eligible pieces, followed by disjointification; it does not assert a uniform
number of extraction rounds or a geometric remainder rate.

This repairs a qualitative measure-construction obligation in original Lemma
8.56, when the actual fine-scale route only provides positive mass. It does
not pay any cross-cap or paid ledger, bound the number of tree generations,
or make constants on different source-density layers uniform.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.PositiveRoutingExhaustion

variable {Ω X L : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace L]

/-- Every positive remainder contains an eligible positive piece, so countably
many eligible measurable sets cover the occurrence up to a null set. -/
theorem exists_countable_routing_cover (μ : Measure Ω) [SFinite μ]
    (P : Set Ω → Prop)
    (hlocal : ∀ s : Set Ω, MeasurableSet s → μ s ≠ 0 →
      ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧ P t ∧ μ t ≠ 0) :
    ∃ D : Set (Set Ω), (∀ t ∈ D, MeasurableSet t ∧ P t) ∧
      D.Countable ∧ μ (⋃₀ D)ᶜ = 0 := by
  let C : Set (Set Ω) := {t | MeasurableSet t ∧ P t}
  obtain ⟨D, hDC, hDcount, hmax⟩ :=
    Measure.exists_ae_subset_biUnion_countable μ (C := C) (fun _ ht => ht.1)
  refine ⟨D, fun t ht => hDC ht, hDcount, ?_⟩
  have hU : MeasurableSet (⋃₀ D) :=
    MeasurableSet.sUnion hDcount (fun t ht => (hDC ht).1)
  by_contra hnonzero
  obtain ⟨t, htU, htm, htP, htpos⟩ := hlocal (⋃₀ D)ᶜ hU.compl hnonzero
  have ht_ae : ∀ᵐ x ∂μ, x ∉ t := (hmax t ⟨htm, htP⟩).mono (fun x hx hxt =>
    (htU hxt) (hx hxt))
  have htz : μ t = 0 := by simpa only [ae_iff, not_not, ofPred_mem_eq] using ht_ae
  exact htpos htz

/-- If route eligibility survives measurable restrictions, the cover can be
made pairwise disjoint without losing eligibility or occurrence mass. The
empty set is allowed as a harmless zero-output piece. -/
theorem exists_disjoint_routing_partition (μ : Measure Ω) [SFinite μ]
    (P : Set Ω → Prop) (hempty : P ∅)
    (hhereditary : ∀ s t : Set Ω, P s → MeasurableSet t → t ⊆ s → P t)
    (hlocal : ∀ s : Set Ω, MeasurableSet s → μ s ≠ 0 →
      ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧ P t ∧ μ t ≠ 0) :
    ∃ pieces : ℕ → Set Ω,
      (∀ n, MeasurableSet (pieces n)) ∧ (∀ n, P (pieces n)) ∧
      Pairwise (fun i j => Disjoint (pieces i) (pieces j)) ∧
      μ (⋃ n, pieces n)ᶜ = 0 := by
  classical
  obtain ⟨D, hD, hDcount, hcover⟩ := exists_countable_routing_cover μ P hlocal
  obtain ⟨f, hf⟩ := (hDcount.insert ∅).exists_eq_range (by simp : (insert ∅ D).Nonempty)
  have hfmem (n : ℕ) : f n ∈ insert ∅ D := by
    rw [hf]
    exact mem_range_self n
  have hfmeas (n : ℕ) : MeasurableSet (f n) := by
    rcases mem_insert_iff.mp (hfmem n) with h | h
    · simpa only [h] using MeasurableSet.empty
    · exact (hD _ h).1
  have hfP (n : ℕ) : P (f n) := by
    rcases mem_insert_iff.mp (hfmem n) with h | h
    · simpa only [h] using hempty
    · exact (hD _ h).2
  have hunion : (⋃ n, f n) = ⋃₀ D := by
    rw [← sUnion_range, ← hf]
    simp
  refine ⟨disjointed f, MeasurableSet.disjointed hfmeas, ?_, disjoint_disjointed f, ?_⟩
  · intro n
    exact hhereditary (f n) (disjointed f n) (hfP n)
      (MeasurableSet.disjointed hfmeas n) (disjointed_subset f n)
  · rw [iUnion_disjointed, hunion]
    exact hcover

/-- The exhausted pieces add as measures, not merely as total masses. -/
theorem exists_routing_measure_identity (μ : Measure Ω) [SFinite μ]
    (P : Set Ω → Prop) (hempty : P ∅)
    (hhereditary : ∀ s t : Set Ω, P s → MeasurableSet t → t ⊆ s → P t)
    (hlocal : ∀ s : Set Ω, MeasurableSet s → μ s ≠ 0 →
      ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧ P t ∧ μ t ≠ 0) :
    ∃ pieces : ℕ → Set Ω,
      (∀ n, MeasurableSet (pieces n)) ∧ (∀ n, P (pieces n)) ∧
      Pairwise (fun i j => Disjoint (pieces i) (pieces j)) ∧
      Measure.sum (fun n => μ.restrict (pieces n)) = μ := by
  obtain ⟨pieces, hm, hP, hdisj, hcover⟩ :=
    exists_disjoint_routing_partition μ P hempty hhereditary hlocal
  refine ⟨pieces, hm, hP, hdisj, ?_⟩
  rw [← Measure.restrict_iUnion hdisj hm]
  apply Measure.restrict_eq_self_of_ae_mem
  exact (ae_iff).2 hcover

/-- Appending separately chosen Markov labels on each exhaustive piece retains
one exact original-occurrence measure, including its old endpoints and marks. -/
theorem exhaustive_markov_extensions_preserve_occurrence
    (μ : Measure Ω) [SFinite μ] (pieces : ℕ → Set Ω)
    (hidentity : Measure.sum (fun n => μ.restrict (pieces n)) = μ)
    (κ : ℕ → Kernel Ω L) [∀ n, IsMarkovKernel (κ n)] :
    Measure.sum (fun n => ((μ.restrict (pieces n)).compProd (κ n)).map Prod.fst) = μ := by
  simpa only [MarkovEndpointPreservation.extension_fst] using hidentity

/-- Positive selector mass on a genuine lower source-density layer is positive
original occurrence mass. This is the point needed to pass a fine physical
bush back to a nonzero restriction of the original old-neighbor occurrence. -/
theorem source_piece_positive_of_lower_density
    (Γ : Measure Ω) (σ : Measure X) (source : Ω → X) (hsource : Measurable source)
    (S H : Set X) (hH : MeasurableSet H) (hHS : H ⊆ S)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hpos : σ H ≠ 0)
    (hlower : c • σ.restrict S ≤ Γ.map source) :
    Γ (source ⁻¹' H) ≠ 0 := by
  have hbound := hlower H
  rw [Measure.map_apply hsource hH, Measure.smul_apply, Measure.restrict_apply hH,
    inter_eq_left.mpr hHS, smul_eq_mul] at hbound
  exact ne_zero_of_lt ((bot_lt_iff_ne_bot.mpr (mul_ne_zero hc hpos)).trans_le hbound)

/-- Positive hereditary routability for the selector measure transfers to any
measurable source density. Restrict first to where that density is nonzero;
there is no uniform lower-density constant to lose. -/
theorem positive_route_withDensity (σ : Measure X) (f : X → ℝ≥0∞)
    (hf : Measurable f) (P : Set X → Prop)
    (hlocal : ∀ s : Set X, MeasurableSet s → σ s ≠ 0 →
      ∃ t : Set X, t ⊆ s ∧ MeasurableSet t ∧ P t ∧ σ t ≠ 0) :
    ∀ s : Set X, MeasurableSet s → (σ.withDensity f) s ≠ 0 →
      ∃ t : Set X, t ⊆ s ∧ MeasurableSet t ∧ P t ∧ (σ.withDensity f) t ≠ 0 := by
  intro s hs hpos
  have hpositive : σ ({x | f x ≠ 0} ∩ s) ≠ 0 :=
    mt (withDensity_apply_eq_zero hf).mpr hpos
  obtain ⟨t, hts, htm, htP, htpos⟩ := hlocal ({x | f x ≠ 0} ∩ s)
    ((measurableSet_support hf).inter hs) hpositive
  refine ⟨t, hts.trans inter_subset_right, htm, htP, ?_⟩
  apply mt (withDensity_apply_eq_zero hf).mp
  have htsupport : t ⊆ {x | f x ≠ 0} := hts.trans inter_subset_left
  rwa [inter_eq_right.mpr htsupport]

/-- A positive geometric route on every positive selector restriction yields
an exact countable partition of the original occurrence by source cuts. The
old target and every inherited mark are coordinates of `Ω` and are untouched.
The measurable density identity is supplied by the actual source marginal,
as in the old-neighbor disintegration module. -/
theorem source_density_routing_exhaustion
    (Γ : Measure Ω) [IsFiniteMeasure Γ] (σ : Measure X)
    (source : Ω → X) (hsource : Measurable source)
    (f : X → ℝ≥0∞) (hf : Measurable f)
    (hdensity : Γ.map source = σ.withDensity f)
    (P : Set X → Prop) (hempty : P ∅)
    (hhereditary : ∀ s t : Set X, P s → MeasurableSet t → t ⊆ s → P t)
    (hlocal : ∀ s : Set X, MeasurableSet s → σ s ≠ 0 →
      ∃ t : Set X, t ⊆ s ∧ MeasurableSet t ∧ P t ∧ σ t ≠ 0) :
    ∃ pieces : ℕ → Set X,
      (∀ n, MeasurableSet (pieces n)) ∧ (∀ n, P (pieces n)) ∧
      Pairwise (fun i j => Disjoint (pieces i) (pieces j)) ∧
      Measure.sum (fun n => Γ.restrict (source ⁻¹' pieces n)) = Γ := by
  have hweighted : ∀ s : Set X, MeasurableSet s → (Γ.map source) s ≠ 0 →
      ∃ t : Set X, t ⊆ s ∧ MeasurableSet t ∧ P t ∧ (Γ.map source) t ≠ 0 := by
    rw [hdensity]
    exact positive_route_withDensity σ f hf P hlocal
  obtain ⟨pieces, hm, hP, hdisj, hcover⟩ :=
    exists_disjoint_routing_partition (Γ.map source) P hempty hhereditary hweighted
  refine ⟨pieces, hm, hP, hdisj, ?_⟩
  have hrootdisj : Pairwise (fun i j =>
      Disjoint (source ⁻¹' pieces i) (source ⁻¹' pieces j)) :=
    fun i j hij => (hdisj hij).preimage source
  rw [← Measure.restrict_iUnion hrootdisj (fun n => hsource (hm n))]
  apply Measure.restrict_eq_self_of_ae_mem
  apply ae_iff.mpr
  change Γ (⋃ n, source ⁻¹' pieces n)ᶜ = 0
  rw [Measure.map_apply hsource (MeasurableSet.iUnion hm).compl] at hcover
  simpa only [preimage_compl, preimage_iUnion] using hcover

/-- A finite truncation can have any prescribed positive absolute tail. No
bound on its number of pieces is claimed. This is sufficient for a nodewise
`r^A` relative error after choosing the tolerance to be `r^A` times node mass. -/
theorem finite_truncation_arbitrarily_small_tail
    (μ : Measure Ω) [IsFiniteMeasure μ] (pieces : ℕ → Set Ω)
    (hm : ∀ n, MeasurableSet (pieces n))
    (hdisj : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (hcover : μ (⋃ n, pieces n)ᶜ = 0)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ N : ℕ, μ (⋃ i ∈ Set.Iio N, pieces i)ᶜ < ε := by
  classical
  have hlim := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
    (μ := μ) (fun n => (hm n).nullMeasurableSet) hdisj
  simp only [tendsto_atTop_nhds, Function.comp_apply] at hlim
  obtain ⟨N, hN⟩ := hlim (Set.Iio ε) hε isOpen_Iio
  refine ⟨N, ?_⟩
  have htail : μ (⋃ i ∈ Set.Ici N, pieces i) < ε := hN N le_rfl
  have hsubset : (⋃ i ∈ Set.Iio N, pieces i)ᶜ ⊆
      (⋃ n, pieces n)ᶜ ∪ (⋃ i ∈ Set.Ici N, pieces i) := by
    intro x hx
    by_cases hu : x ∈ ⋃ n, pieces n
    · right
      obtain ⟨i, hi⟩ := mem_iUnion.mp hu
      refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨?_, hi⟩⟩
      by_contra hni
      have hiN : i < N := lt_of_not_ge hni
      exact hx (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hiN, hi⟩⟩)
    · exact Or.inl hu
  calc
    μ (⋃ i ∈ Set.Iio N, pieces i)ᶜ ≤
        μ ((⋃ n, pieces n)ᶜ ∪ (⋃ i ∈ Set.Ici N, pieces i)) := measure_mono hsubset
    _ ≤ μ (⋃ n, pieces n)ᶜ + μ (⋃ i ∈ Set.Ici N, pieces i) := measure_union_le _ _
    _ = μ (⋃ i ∈ Set.Ici N, pieces i) := by rw [hcover, zero_add]
    _ < ε := htail

end StickyKakeya4.PositiveRoutingExhaustion
