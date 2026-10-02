import Theorems.Thm_StickyKakeya4_rooted_four_cycle_measure
import Theorems.Thm_StickyKakeya4_positive_flag_conditioning
import Theorems.Thm_StickyKakeya4_four_distinct_sources
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Lossless fresh witnesses for a cycle rooted at the inherited old edge

The root is a whole occurrence `ω : Ω`, including its original ordered
endpoints, time, and flags. Only two opposite vertices `(z,w)` are appended.
The three new graph edges must have strictly positive original density.

The measurable success event has probability at least the weighted rooted-C4
success density. The latter is positive at almost every original old edge,
so actual positive-event conditioning produces a Markov witness kernel on
*all* of the inherited occurrence law. Every original observable, including
time and flags, keeps exactly its old law; the old pair is never resampled.

The conditioned extension is absolutely continuous with respect to the fresh
product extension, but no uniform density or product-domination bound after
conditioning is claimed. This construction establishes positive graph-cycle
witnesses only. A mesoscopic determinant bound, quantitative time alignment,
residual scale control, and a paid estimate remain geometric obligations.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.RootedCycleWitnessKernel

namespace Diffuse

variable {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]

lemma fresh_pair_ae_ne (μ : Measure X) (ν : Measure Y)
    [NullSingletonClass μ] [NullSingletonClass ν] (x : X) (y : Y) :
    ∀ᵐ q ∂μ.prod ν, q.1 ≠ x ∧ q.2 ≠ y := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (μ.ae_ne x),
    Measure.quasiMeasurePreserving_snd.ae (ν.ae_ne y)] with q hx hy
  exact ⟨hx, hy⟩

lemma fresh_pair_measure_one (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] [NullSingletonClass ν] (x : X) (y : Y) :
    (μ.prod ν) {q | q.1 ≠ x ∧ q.2 ≠ y} = 1 := by
  calc
    (μ.prod ν) {q | q.1 ≠ x ∧ q.2 ≠ y} = (μ.prod ν) Set.univ := by
      apply measure_congr
      filter_upwards [fresh_pair_ae_ne μ ν x y] with q hq
      exact propext ⟨fun _ => True.intro, fun _ => hq⟩
    _ = 1 := measure_univ

lemma extension_ae_ne [MeasurableEq X] [MeasurableEq Y]
    (μ : Measure X) (ν : Measure Y)
    [NullSingletonClass μ] [NullSingletonClass ν]
    (Γ : Measure Ω) (endpoint : Ω → X × Y) (hm : Measurable endpoint) :
    ∀ᵐ p ∂Γ.compProd (Kernel.const Ω (μ.prod ν)),
      p.2.1 ≠ (endpoint p.1).1 ∧ p.2.2 ≠ (endpoint p.1).2 := by
  apply Measure.ae_compProd_of_ae_ae
  · exact (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
      (hm.fst.comp measurable_fst)).compl.inter
      (measurableSet_eq_fun (measurable_snd.comp measurable_snd)
        (hm.snd.comp measurable_fst)).compl
  · exact ae_of_all _ fun r => fresh_pair_ae_ne μ ν (endpoint r).1 (endpoint r).2

omit [MeasurableSpace X] in
lemma positive_cycle_fourDistinct
    (h : X × X → ℝ≥0∞) (hdiag : ∀ x, h (x, x) = 0)
    {x y z w : X} (hxy : 0 < h (x, y)) (hzy : 0 < h (z, y))
    (hzw : 0 < h (z, w)) (hxw : 0 < h (x, w))
    (hzx : z ≠ x) (hwy : w ≠ y) :
    StickyKakeya4.FourDistinctSources.FourDistinct x y z w := by
  have pos_ne {a b : X} (hab : 0 < h (a, b)) : a ≠ b := by
    intro heq
    subst b
    rw [hdiag] at hab
    exact (lt_irrefl 0) hab
  exact ⟨pos_ne hxy, hzx.symm, pos_ne hxw, (pos_ne hzy).symm, hwy.symm, pos_ne hzw⟩

lemma extension_ae_cycle_distinct [MeasurableEq X]
    (μ ν : Measure X) [NullSingletonClass μ] [NullSingletonClass ν]
    (Γ : Measure Ω) (endpoint : Ω → X × X) (hm : Measurable endpoint)
    (h : X × X → ℝ≥0∞) (hdiag : ∀ x, h (x, x) = 0) :
    ∀ᵐ p ∂Γ.compProd (Kernel.const Ω (μ.prod ν)),
      (0 < h (endpoint p.1) ∧
        0 < h (p.2.1, (endpoint p.1).2) ∧
        0 < h (p.2.1, p.2.2) ∧
        0 < h ((endpoint p.1).1, p.2.2)) →
      StickyKakeya4.FourDistinctSources.FourDistinct
        (endpoint p.1).1 (endpoint p.1).2 p.2.1 p.2.2 := by
  filter_upwards [extension_ae_ne μ ν Γ endpoint hm] with p hp
  rintro ⟨hxy, hzy, hzw, hxw⟩
  exact positive_cycle_fourDistinct h hdiag hxy hzy hzw hxw hp.1 hp.2

lemma ac_extension_ae_cycle_distinct [MeasurableEq X]
    (μ ν : Measure X) [NullSingletonClass μ] [NullSingletonClass ν]
    (Γ : Measure Ω) (endpoint : Ω → X × X) (hm : Measurable endpoint)
    (h : X × X → ℝ≥0∞) (hdiag : ∀ x, h (x, x) = 0)
    (ξ : Measure (Ω × (X × X)))
    (hac : ξ ≪ Γ.compProd (Kernel.const Ω (μ.prod ν)))
    (hpositive : ∀ᵐ p ∂ξ,
      0 < h (endpoint p.1) ∧
        0 < h (p.2.1, (endpoint p.1).2) ∧
        0 < h (p.2.1, p.2.2) ∧
        0 < h ((endpoint p.1).1, p.2.2)) :
    ∀ᵐ p ∂ξ,
      StickyKakeya4.FourDistinctSources.FourDistinct
        (endpoint p.1).1 (endpoint p.1).2 p.2.1 p.2.2 := by
  filter_upwards [hac.ae_le (extension_ae_cycle_distinct μ ν Γ endpoint hm h hdiag),
    hpositive] with p hp hpos
  exact hp hpos

end Diffuse


variable {Ω X Y T : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace T]

/-- Success of the three newly required edges; the inherited root is fixed. -/
def witnessEvent (endpoint : Ω → X × Y) (h : X × Y → ℝ≥0∞) :
    Set (Ω × (X × Y)) :=
  {p | 0 < h (p.2.1, (endpoint p.1).2) ∧
    0 < h p.2 ∧ 0 < h ((endpoint p.1).1, p.2.2)}

theorem measurableSet_witnessEvent (endpoint : Ω → X × Y)
    (hendpoint : Measurable endpoint) (h : X × Y → ℝ≥0∞) (hh : Measurable h) :
    MeasurableSet (witnessEvent endpoint h) := by
  exact (measurableSet_lt measurable_const (hh.comp (by fun_prop))).inter
    ((measurableSet_lt measurable_const (hh.comp measurable_snd)).inter
      (measurableSet_lt measurable_const (hh.comp (by fun_prop))))

/-- Start with genuine independent selector draws, then condition their event. -/
def freshVertexKernel (μ : Measure X) (ν : Measure Y) : Kernel Ω (X × Y) :=
  Kernel.const Ω (μ.prod ν)

instance freshVertexKernel_isMarkov (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsMarkovKernel (freshVertexKernel (Ω := Ω) μ ν) := by
  unfold freshVertexKernel
  infer_instance

/-- The three-edge indicator dominates the weighted rooted-cycle integrand,
so its probability is at least the actual weighted success density. -/
theorem rootSuccess_le_event_probability
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (endpoint : Ω → X × Y) (hendpoint : Measurable endpoint)
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1) (ω : Ω) :
    RootedFourCycle.rootSuccess μ ν h (endpoint ω) ≤
      PositiveFlagConditioning.successProbability (freshVertexKernel μ ν)
        (witnessEvent endpoint h) ω := by
  change (∫⁻ q : X × Y,
    h (q.1, (endpoint ω).2) * h q * h ((endpoint ω).1, q.2) ∂μ.prod ν) ≤
      (μ.prod ν) (Prod.mk ω ⁻¹' witnessEvent endpoint h)
  rw [← lintegral_indicator_one
    (measurable_prodMk_left (measurableSet_witnessEvent endpoint hendpoint h hh))]
  apply lintegral_mono
  intro q
  by_cases h₁ : h (q.1, (endpoint ω).2) = 0
  · simp only [h₁, zero_mul]
    exact zero_le
  by_cases h₂ : h q = 0
  · simp only [h₂, mul_zero, zero_mul]
    exact zero_le
  by_cases h₃ : h ((endpoint ω).1, q.2) = 0
  · simp only [h₃, mul_zero]
    exact zero_le
  have hmem : q ∈ Prod.mk ω ⁻¹' witnessEvent endpoint h :=
    ⟨pos_iff_ne_zero.mpr h₁, pos_iff_ne_zero.mpr h₂, pos_iff_ne_zero.mpr h₃⟩
  rw [Set.indicator_of_mem hmem, Pi.one_apply]
  calc
    _ ≤ (1 : ℝ≥0∞) * 1 * 1 :=
      mul_le_mul' (mul_le_mul' (hbound _) (hbound _)) (hbound _)
    _ = 1 := by simp

/-- Endpoint-law domination suffices: almost every whole old occurrence admits
positive-probability fresh rooted witnesses. No quantitative lower bound occurs. -/
theorem ae_witness_probability_pos
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) (endpoint : Ω → X × Y) (hendpoint : Measurable endpoint)
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1)
    (hΓ : Γ.map endpoint ≤ (μ.prod ν).withDensity h) :
    ∀ᵐ ω ∂Γ, 0 < PositiveFlagConditioning.successProbability
      (freshVertexKernel μ ν) (witnessEvent endpoint h) ω := by
  have hr := hΓ.absolutelyContinuous.ae_le (RootedFourCycle.ae_rootSuccess_pos μ ν h hh hbound)
  have ho := ae_of_ae_map hendpoint.aemeasurable hr
  exact ho.mono (fun ω hω => hω.trans_le
    (rootSuccess_le_event_probability μ ν endpoint hendpoint h hh hbound ω))

/-- The inherited edge itself is genuine under its original dominated law. -/
theorem ae_root_edge_pos
    (μ : Measure X) (ν : Measure Y) (Γ : Measure Ω)
    (endpoint : Ω → X × Y) (hendpoint : Measurable endpoint)
    (h : X × Y → ℝ≥0∞) (hh : Measurable h)
    (hΓ : Γ.map endpoint ≤ (μ.prod ν).withDensity h) :
    ∀ᵐ ω ∂Γ, 0 < h (endpoint ω) := by
  have hp : ∀ᵐ p ∂(μ.prod ν).withDensity h, 0 < h p := by
    rw [ae_withDensity_iff hh]
    exact Filter.Eventually.of_forall (fun _ hp => pos_iff_ne_zero.mpr hp)
  exact ae_of_ae_map hendpoint.aemeasurable (hΓ.absolutelyContinuous.ae_le hp)

section Conditioned

variable [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]

/-- The actual Markov conditioned kernel. Only fresh vertices are added. -/
def rootedWitnessKernel
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (h : X × Y → ℝ≥0∞) : Kernel Ω (X × Y) :=
  PositiveFlagConditioning.conditionedKernel Γ (freshVertexKernel μ ν) (witnessEvent endpoint h)

instance rootedWitnessKernel_isMarkov
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (h : X × Y → ℝ≥0∞) :
    IsMarkovKernel (rootedWitnessKernel μ ν Γ endpoint h) := by
  unfold rootedWitnessKernel
  infer_instance

/-- The full original occurrence measure, with two conditioned fresh vertices. -/
def rootedWitnessExtension
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (h : X × Y → ℝ≥0∞) : Measure (Ω × (X × Y)) :=
  Γ.compProd (rootedWitnessKernel μ ν Γ endpoint h)

instance rootedWitnessExtension_isFinite
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (h : X × Y → ℝ≥0∞) :
    IsFiniteMeasure (rootedWitnessExtension μ ν Γ endpoint h) := by
  unfold rootedWitnessExtension
  infer_instance

/-- No inherited mass, root endpoint, time, or flag is replaced or discarded. -/
theorem rooted_extension_original
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (h : X × Y → ℝ≥0∞) :
    (rootedWitnessExtension μ ν Γ endpoint h).map Prod.fst = Γ :=
  MarkovEndpointPreservation.extension_fst Γ _

/-- Any measurable inherited observable has exactly its previous law. -/
theorem rooted_extension_observable
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (h : X × Y → ℝ≥0∞)
    (f : Ω → T) (hf : Measurable f) :
    (rootedWitnessExtension μ ν Γ endpoint h).map (fun p => f p.1) = Γ.map f :=
  MarkovEndpointPreservation.extension_endpoint Γ _ f hf

/-- Even nonmeasurably presented inherited almost-sure properties persist. -/
theorem rooted_extension_inherited
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (h : X × Y → ℝ≥0∞)
    (P : Ω → Prop) (hP : ∀ᵐ ω ∂Γ, P ω) :
    ∀ᵐ p ∂rootedWitnessExtension μ ν Γ endpoint h, P p.1 := by
  apply ae_of_ae_map measurable_fst.aemeasurable
  rw [rooted_extension_original]
  exact hP

/-- Positivity removes the auxiliary positive-source restriction entirely. -/
theorem conditioned_extension_eq_rooted
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (hendpoint : Measurable endpoint)
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1)
    (hΓ : Γ.map endpoint ≤ (μ.prod ν).withDensity h) :
    PositiveFlagConditioning.conditionedExtension Γ (freshVertexKernel μ ν)
      (witnessEvent endpoint h) = rootedWitnessExtension μ ν Γ endpoint h := by
  have hfull : Γ.restrict (PositiveFlagConditioning.positiveSource
      (freshVertexKernel μ ν) (witnessEvent endpoint h)) = Γ :=
    Measure.restrict_eq_self_of_ae_mem (ae_witness_probability_pos μ ν Γ endpoint hendpoint h hh hbound hΓ)
  unfold PositiveFlagConditioning.conditionedExtension rootedWitnessExtension rootedWitnessKernel
  rw [hfull]

/-- The actual conditioned extension succeeds almost everywhere on all Γ. -/
theorem rooted_extension_success
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (hendpoint : Measurable endpoint)
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1)
    (hΓ : Γ.map endpoint ≤ (μ.prod ν).withDensity h) :
    ∀ᵐ p ∂rootedWitnessExtension μ ν Γ endpoint h, p ∈ witnessEvent endpoint h := by
  rw [← conditioned_extension_eq_rooted μ ν Γ endpoint hendpoint h hh hbound hΓ]
  exact PositiveFlagConditioning.conditioned_extension_success Γ _ _
    (measurableSet_witnessEvent endpoint hendpoint h hh)

/-- The actual Markov kernel assigns probability one to successful fresh
vertices for almost every full inherited occurrence. -/
theorem rooted_kernel_success_mass
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (hendpoint : Measurable endpoint)
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1)
    (hΓ : Γ.map endpoint ≤ (μ.prod ν).withDensity h) :
    ∀ᵐ ω ∂Γ, rootedWitnessKernel μ ν Γ endpoint h ω
      (Prod.mk ω ⁻¹' witnessEvent endpoint h) = 1 := by
  have hf := Measure.ae_ae_of_ae_compProd
    (rooted_extension_success μ ν Γ endpoint hendpoint h hh hbound hΓ)
  filter_upwards [hf] with ω hω
  exact (mem_ae_iff_prob_eq_one (measurable_prodMk_left
    (measurableSet_witnessEvent endpoint hendpoint h hh))).mp hω

/-- The same witness kernel is valid on every absolutely continuous hereditary
old source, preserving that source's whole occurrence measure exactly. -/
theorem rooted_subsource_witness
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (hendpoint : Measurable endpoint)
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1)
    (hΓ : Γ.map endpoint ≤ (μ.prod ν).withDensity h)
    (Λ : Measure Ω) [SFinite Λ] (hΛ : Λ ≪ Γ) :
    (∀ᵐ p ∂Λ.compProd (rootedWitnessKernel μ ν Γ endpoint h),
      p ∈ witnessEvent endpoint h) ∧
      (Λ.compProd (rootedWitnessKernel μ ν Γ endpoint h)).map Prod.fst = Λ :=
  ⟨(hΛ.compProd_left (rootedWitnessKernel μ ν Γ endpoint h)).ae_le
      (rooted_extension_success μ ν Γ endpoint hendpoint h hh hbound hΓ),
    MarkovEndpointPreservation.extension_fst Λ _⟩

/-- Absolute continuity retains all genuine-support properties of the raw
fresh product law. This is not a bounded-density assertion after conditioning. -/
theorem rooted_extension_absolutelyContinuous
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (hendpoint : Measurable endpoint)
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1)
    (hΓ : Γ.map endpoint ≤ (μ.prod ν).withDensity h) :
    rootedWitnessExtension μ ν Γ endpoint h ≪ Γ.compProd (freshVertexKernel μ ν) := by
  rw [← conditioned_extension_eq_rooted μ ν Γ endpoint hendpoint h hh hbound hΓ]
  exact (PositiveFlagConditioning.conditioned_extension_equivalent Γ _ _
    (measurableSet_witnessEvent endpoint hendpoint h hh)).1.trans
      Measure.restrict_le_self.absolutelyContinuous

/-- All four graph edges of the cycle are genuine original positive-density edges. -/
theorem rooted_extension_all_edges_pos
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (hendpoint : Measurable endpoint)
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1)
    (hΓ : Γ.map endpoint ≤ (μ.prod ν).withDensity h) :
    ∀ᵐ p ∂rootedWitnessExtension μ ν Γ endpoint h,
      0 < h (endpoint p.1) ∧ 0 < h (p.2.1, (endpoint p.1).2) ∧
        0 < h p.2 ∧ 0 < h ((endpoint p.1).1, p.2.2) := by
  filter_upwards [rooted_extension_success μ ν Γ endpoint hendpoint h hh hbound hΓ,
    rooted_extension_inherited μ ν Γ endpoint h (fun ω => 0 < h (endpoint ω))
      (ae_root_edge_pos μ ν Γ endpoint hendpoint h hh hΓ)] with p hp hroot
  exact ⟨hroot, hp⟩

/-- Any genuine old-edge support containing positive-density edges contains all
four witness edges. Original time and flag observables remain in Ω throughout. -/
theorem rooted_extension_old_edge_support
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (hendpoint : Measurable endpoint)
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1)
    (hΓ : Γ.map endpoint ≤ (μ.prod ν).withDensity h)
    (G : Set (X × Y)) (hG : ∀ p, 0 < h p → p ∈ G) :
    ∀ᵐ p ∂rootedWitnessExtension μ ν Γ endpoint h,
      endpoint p.1 ∈ G ∧ (p.2.1, (endpoint p.1).2) ∈ G ∧
        p.2 ∈ G ∧ ((endpoint p.1).1, p.2.2) ∈ G := by
  filter_upwards [rooted_extension_all_edges_pos μ ν Γ endpoint hendpoint h hh hbound hΓ]
    with p hp
  exact ⟨hG _ hp.1, hG _ hp.2.1, hG _ hp.2.2.1, hG _ hp.2.2.2⟩

/-- Existence form with an actual Markov witness kernel and exact full old-law
conservation, rather than a scalar success-mass certificate. -/
theorem exists_rooted_witness_kernel
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (hendpoint : Measurable endpoint)
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1)
    (hΓ : Γ.map endpoint ≤ (μ.prod ν).withDensity h) :
    ∃ κ : Kernel Ω (X × Y), IsMarkovKernel κ ∧
      (∀ᵐ p ∂Γ.compProd κ, p ∈ witnessEvent endpoint h) ∧
      (Γ.compProd κ).map Prod.fst = Γ :=
  ⟨rootedWitnessKernel μ ν Γ endpoint h, inferInstance,
    rooted_extension_success μ ν Γ endpoint hendpoint h hh hbound hΓ,
    rooted_extension_original μ ν Γ endpoint h⟩

/-- Nonatomic selectors exclude coincidences with the fixed opposite root
vertices already in the raw product extension, and conditioning preserves this. -/
theorem rooted_extension_opposite_distinct
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] [NullSingletonClass ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (hendpoint : Measurable endpoint)
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1)
    (hΓ : Γ.map endpoint ≤ (μ.prod ν).withDensity h) :
    ∀ᵐ p ∂rootedWitnessExtension μ ν Γ endpoint h,
      p.2.1 ≠ (endpoint p.1).1 ∧ p.2.2 ≠ (endpoint p.1).2 :=
  (rooted_extension_absolutelyContinuous μ ν Γ endpoint hendpoint h hh hbound hΓ).ae_le
    (Diffuse.extension_ae_ne μ ν Γ endpoint hendpoint)

/-- Requiring the two opposite-vertex inequalities costs exactly zero mass. -/
theorem rooted_extension_restrict_opposite_distinct
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] [NullSingletonClass ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × Y) (hendpoint : Measurable endpoint)
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1)
    (hΓ : Γ.map endpoint ≤ (μ.prod ν).withDensity h) :
    (rootedWitnessExtension μ ν Γ endpoint h).restrict
      {p | p.2.1 ≠ (endpoint p.1).1 ∧ p.2.2 ≠ (endpoint p.1).2} =
      rootedWitnessExtension μ ν Γ endpoint h :=
  Measure.restrict_eq_self_of_ae_mem
    (rooted_extension_opposite_distinct μ ν Γ endpoint hendpoint h hh hbound hΓ)

/-- For a loop-free graph on a common physical vertex space, these are four
distinct physical vertices. No quantitative separation or determinant follows. -/
theorem rooted_extension_four_distinct
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] [NullSingletonClass ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × X) (hendpoint : Measurable endpoint)
    (h : X × X → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1)
    (hdiag : ∀ x, h (x, x) = 0)
    (hΓ : Γ.map endpoint ≤ (μ.prod ν).withDensity h) :
    ∀ᵐ p ∂rootedWitnessExtension μ ν Γ endpoint h,
      FourDistinctSources.FourDistinct (endpoint p.1).1 (endpoint p.1).2 p.2.1 p.2.2 :=
  Diffuse.ac_extension_ae_cycle_distinct μ ν Γ endpoint hendpoint h hdiag _
    (rooted_extension_absolutelyContinuous μ ν Γ endpoint hendpoint h hh hbound hΓ)
    (rooted_extension_all_edges_pos μ ν Γ endpoint hendpoint h hh hbound hΓ)

/-- Four-distinctness can be imposed as an actual restriction without losing
any old occurrence or changing its inherited endpoint/time/flag law. -/
theorem rooted_extension_restrict_four_distinct
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] [NullSingletonClass ν]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (endpoint : Ω → X × X) (hendpoint : Measurable endpoint)
    (h : X × X → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1)
    (hdiag : ∀ x, h (x, x) = 0)
    (hΓ : Γ.map endpoint ≤ (μ.prod ν).withDensity h) :
    (rootedWitnessExtension μ ν Γ endpoint h).restrict
      {p | FourDistinctSources.FourDistinct (endpoint p.1).1 (endpoint p.1).2 p.2.1 p.2.2} =
      rootedWitnessExtension μ ν Γ endpoint h :=
  Measure.restrict_eq_self_of_ae_mem
    (rooted_extension_four_distinct μ ν Γ endpoint hendpoint h hh hbound hdiag hΓ)

end Conditioned

end StickyKakeya4.RootedCycleWitnessKernel
