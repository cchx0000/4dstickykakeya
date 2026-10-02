import Theorems.Thm_StickyKakeya4_independent_flag_separation

/-!
# Lossless conditioning on positive fresh-label events

The original occurrence `ω` contains every inherited endpoint and mark. Given
an appended Markov label and a measurable successful event `E`, let
`q ω = κ ω (E ω)`. The successful joint law has first marginal `q • Γ`
(pointwise density). Its actual standard-Borel conditional kernel is Markov.

On `{q > 0}`, this successful marginal and the full restricted original law
have exactly the same null sets. Consequently the conditional kernel can be
used with **all** of `Γ.restrict {q > 0}`: it succeeds almost everywhere while
preserving this entire original law. No positive uniform lower bound on `q`
is needed, and there is no loss proportional to the possibly tiny success
probabilities. The completed kernel is only constrained almost everywhere at
null sources, as is usual for disintegration.

This is a probability adapter for source-hereditary positive routing. It does
not establish positivity of geometric success events, geometric routing, or an
all-inherited-normals cap hypothesis. Genuine-incidence properties of the
original appended labels do survive conditioning by absolute continuity. When
`E` depends on an inherited target or mark, the base remains the entire old
occurrence; projecting its success to the physical source alone would not
justify successful conditioning for all inherited old neighbors there.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StickyKakeya4.PositiveFlagConditioning

variable {Ω L Y : Type*}
  [MeasurableSpace Ω] [MeasurableSpace L] [MeasurableSpace Y]

/-- The actual fiber success probability, before conditioning. -/
noncomputable def successProbability (κ : Kernel Ω L) (E : Set (Ω × L)) (ω : Ω) :
    ℝ≥0∞ := κ ω (Prod.mk ω ⁻¹' E)

/-- All original occurrences whose fresh-label success probability is positive. -/
def positiveSource (κ : Kernel Ω L) (E : Set (Ω × L)) : Set Ω :=
  {ω | 0 < successProbability κ E ω}

/-- The measurability follows from the kernel integral theorem for sections. -/
theorem measurable_successProbability (κ : Kernel Ω L) [IsSFiniteKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E) :
    Measurable (successProbability κ E) :=
  Kernel.measurable_kernel_prodMk_left hE

/-- No selection or arbitrary source cutoff is used to define the positive set. -/
theorem measurableSet_positiveSource (κ : Kernel Ω L) [IsSFiniteKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E) :
    MeasurableSet (positiveSource κ E) :=
  measurableSet_lt measurable_const (measurable_successProbability κ E hE)

/-- The unnormalized law of successful original occurrences and fresh labels. -/
noncomputable def successfulMeasure (Γ : Measure Ω) (κ : Kernel Ω L)
    (E : Set (Ω × L)) : Measure (Ω × L) :=
  (Γ.compProd κ).restrict E

instance successfulMeasure_isFinite (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ] (E : Set (Ω × L)) :
    IsFiniteMeasure (successfulMeasure Γ κ E) := by
  unfold successfulMeasure
  infer_instance

/-- The successful source is weighted by its actual success probability. -/
theorem successful_source_density (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsSFiniteKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E) :
    (successfulMeasure Γ κ E).fst = Γ.withDensity (successProbability κ E) := by
  ext s hs
  change ((Γ.compProd κ).restrict E).map Prod.fst s = _
  rw [IndependentFlagSeparation.restricted_original_apply Γ κ E hE s hs,
    withDensity_apply _ hs]
  rfl

/-- Weighting by a strictly positive, possibly arbitrarily small probability
changes no null sets on the positive source. This is the lossless step. -/
theorem successful_source_null_iff (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsSFiniteKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E)
    (s : Set Ω) (hs : MeasurableSet s) :
    (successfulMeasure Γ κ E).fst s = 0 ↔
      Γ.restrict (positiveSource κ E) s = 0 := by
  rw [successful_source_density Γ κ E hE,
    withDensity_apply_eq_zero (measurable_successProbability κ E hE),
    Measure.restrict_apply hs]
  simp only [positiveSource, pos_iff_ne_zero, Set.inter_comm]

/-- Both source measures have exactly the same almost-everywhere predicates. -/
theorem successful_source_ae_iff (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsSFiniteKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E) (p : Ω → Prop) :
    (∀ᵐ ω ∂(successfulMeasure Γ κ E).fst, p ω) ↔
      ∀ᵐ ω ∂Γ.restrict (positiveSource κ E), p ω := by
  rw [successful_source_density Γ κ E hE]
  simpa only [positiveSource, pos_iff_ne_zero] using
    ae_withDensity_iff_ae_restrict (μ := Γ)
      (p := p) (measurable_successProbability κ E hE)

/-- Absolute continuity holds both ways, with no bounded inverse-density claim. -/
theorem successful_source_equivalent (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsSFiniteKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E) :
    Γ.restrict (positiveSource κ E) ≪ (successfulMeasure Γ κ E).fst ∧
      (successfulMeasure Γ κ E).fst ≪ Γ.restrict (positiveSource κ E) := by
  constructor
  · exact Measure.AbsolutelyContinuous.mk fun s hs hzero =>
      (successful_source_null_iff Γ κ E hE s hs).mp hzero
  · exact Measure.AbsolutelyContinuous.mk fun s hs hzero =>
      (successful_source_null_iff Γ κ E hE s hs).mpr hzero

section Conditioned

variable [StandardBorelSpace L] [Nonempty L]

/-- A genuine Markov kernel constructed by disintegrating the successful law;
its arbitrary completion at source-null points is not used for support claims. -/
noncomputable def conditionedKernel (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ] (E : Set (Ω × L)) : Kernel Ω L :=
  (successfulMeasure Γ κ E).condKernel

instance conditionedKernel_isMarkov (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ] (E : Set (Ω × L)) :
    IsMarkovKernel (conditionedKernel Γ κ E) := by
  unfold conditionedKernel
  infer_instance

/-- Exact disintegration of the successful joint law, retaining the full old
occurrence in the first coordinate. -/
theorem successful_disintegration (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ] (E : Set (Ω × L)) :
    (successfulMeasure Γ κ E).fst.compProd (conditionedKernel Γ κ E) =
      successfulMeasure Γ κ E :=
  (successfulMeasure Γ κ E).disintegrate (successfulMeasure Γ κ E).condKernel

/-- Append the conditioned fresh label to the *full* positive original source. -/
noncomputable def conditionedExtension (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ] (E : Set (Ω × L)) : Measure (Ω × L) :=
  (Γ.restrict (positiveSource κ E)).compProd (conditionedKernel Γ κ E)

instance conditionedExtension_isFinite (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ] (E : Set (Ω × L)) :
    IsFiniteMeasure (conditionedExtension Γ κ E) := by
  unfold conditionedExtension
  infer_instance

/-- Conditional relabeling is equivalent to the successful joint law, even
though no fixed multiple of the successful mass need dominate it. -/
theorem conditioned_extension_equivalent (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E) :
    conditionedExtension Γ κ E ≪ successfulMeasure Γ κ E ∧
      successfulMeasure Γ κ E ≪ conditionedExtension Γ κ E := by
  obtain ⟨hforward, hreverse⟩ := successful_source_equivalent Γ κ E hE
  constructor
  · have h := hforward.compProd_left (conditionedKernel Γ κ E)
    rwa [successful_disintegration] at h
  · have h := hreverse.compProd_left (conditionedKernel Γ κ E)
    rwa [successful_disintegration] at h

/-- The conditioned extension succeeds almost everywhere for the full positive
source, without a lower bound on the fiber success probabilities. -/
theorem conditioned_extension_success (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E) :
    ∀ᵐ p ∂conditionedExtension Γ κ E, p ∈ E :=
  (conditioned_extension_equivalent Γ κ E hE).1.ae_le (ae_restrict_mem hE)

/-- The kernel gives successful labels almost surely at almost every positive
original occurrence. Null-source completions need not satisfy this property. -/
theorem conditioned_kernel_success (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E) :
    ∀ᵐ ω ∂Γ.restrict (positiveSource κ E),
      ∀ᵐ l ∂conditionedKernel Γ κ E ω, (ω, l) ∈ E :=
  Measure.ae_ae_of_ae_compProd (conditioned_extension_success Γ κ E hE)

/-- The successful fiber has conditional probability one at almost every
original occurrence in the positive source. -/
theorem conditioned_kernel_success_mass (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E) :
    ∀ᵐ ω ∂Γ.restrict (positiveSource κ E),
      conditionedKernel Γ κ E ω (Prod.mk ω ⁻¹' E) = 1 := by
  filter_upwards [conditioned_kernel_success Γ κ E hE] with ω hω
  exact (mem_ae_iff_prob_eq_one (measurable_prodMk_left hE)).mp hω

/-- Restricting the conditioned law to success costs no measure at all. -/
theorem conditioned_restrict_success (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E) :
    (conditionedExtension Γ κ E).restrict E = conditionedExtension Γ κ E :=
  Measure.restrict_eq_self_of_ae_mem (conditioned_extension_success Γ κ E hE)

/-- The original occurrence marginal is exactly the full positive source. -/
theorem conditioned_extension_original (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ] (E : Set (Ω × L)) :
    (conditionedExtension Γ κ E).map Prod.fst = Γ.restrict (positiveSource κ E) :=
  MarkovEndpointPreservation.extension_fst _ _

/-- Every inherited endpoint observable or mark keeps its full restricted law. -/
theorem conditioned_extension_observable (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ] (E : Set (Ω × L))
    (endpoint : Ω → Y) (hendpoint : Measurable endpoint) :
    (conditionedExtension Γ κ E).map (fun p => endpoint p.1) =
      (Γ.restrict (positiveSource κ E)).map endpoint :=
  MarkovEndpointPreservation.extension_endpoint _ _ endpoint hendpoint

/-- The total mass is the positive-source mass, not the smaller successful
mass obtained by multiplication by the success probabilities. -/
theorem conditioned_extension_mass (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ] (E : Set (Ω × L)) :
    conditionedExtension Γ κ E univ = Γ (positiveSource κ E) := by
  change (Γ.restrict (positiveSource κ E)).compProd _ univ = _
  rw [Measure.compProd_apply_univ, Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter]

/-- Conditioning retains all almost-sure original fresh-label properties,
including genuine old-flag incidence at the unchanged physical endpoint. -/
theorem conditioned_extension_genuine (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E)
    (P : Ω × L → Prop) (hP : ∀ᵐ p ∂Γ.compProd κ, P p) :
    ∀ᵐ p ∂conditionedExtension Γ κ E, P p :=
  (conditioned_extension_equivalent Γ κ E hE).1.ae_le (ae_restrict_of_ae hP)

/-- The same conditioned kernel works on every hereditary source restriction,
and more generally every absolutely continuous reweighting of the positive
original source. Every such source keeps its own exact occurrence marginal. -/
theorem conditioned_subsource_law (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E)
    (ν : Measure Ω) [SFinite ν]
    (hν : ν ≪ Γ.restrict (positiveSource κ E)) :
    (∀ᵐ p ∂ν.compProd (conditionedKernel Γ κ E), p ∈ E) ∧
      (ν.compProd (conditionedKernel Γ κ E)).map Prod.fst = ν := by
  constructor
  · exact (hν.compProd_left (conditionedKernel Γ κ E)).ae_le
      (conditioned_extension_success Γ κ E hE)
  · exact MarkovEndpointPreservation.extension_fst ν _

/-- Existence form of the lossless positive-event conditioning adapter. The
witness is an actual constructed Markov kernel, and conservation is an equality
of occurrence measures rather than only of their total masses. -/
theorem exists_lossless_positive_conditioning (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E) :
    ∃ η : Kernel Ω L, IsMarkovKernel η ∧
      (∀ᵐ p ∂(Γ.restrict (positiveSource κ E)).compProd η, p ∈ E) ∧
      ((Γ.restrict (positiveSource κ E)).compProd η).map Prod.fst =
        Γ.restrict (positiveSource κ E) :=
  ⟨conditionedKernel Γ κ E, inferInstance,
    conditioned_extension_success Γ κ E hE, conditioned_extension_original Γ κ E⟩

/-- When success is merely positive almost everywhere on the original source,
conditioning retains *all* of that source with exact occurrence-law equality.
There is still no uniform numerical lower bound on success probabilities. -/
theorem exists_lossless_conditioning_of_ae_positive
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (E : Set (Ω × L)) (hE : MeasurableSet E)
    (hpositive : ∀ᵐ ω ∂Γ, 0 < successProbability κ E ω) :
    ∃ η : Kernel Ω L, IsMarkovKernel η ∧
      (∀ᵐ p ∂Γ.compProd η, p ∈ E) ∧ (Γ.compProd η).map Prod.fst = Γ := by
  have hfull : Γ.restrict (positiveSource κ E) = Γ :=
    Measure.restrict_eq_self_of_ae_mem hpositive
  simpa only [hfull] using exists_lossless_positive_conditioning Γ κ E hE

end Conditioned

end StickyKakeya4.PositiveFlagConditioning
