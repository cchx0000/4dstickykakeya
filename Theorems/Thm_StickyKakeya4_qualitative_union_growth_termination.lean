import Theorems.Thm_StickyKakeya4_positive_routing_exhaustion
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Whole-selector-support growth cannot occur twice under exact old-pair reversal

The support containment below is derived from actual measure domination and
measurable density identities. It is not a certificate postulated of a route.
A submeasure of a probability-labeled reversal has old target law dominated
by the original source law. Its positive-density support is therefore contained,
up to selector null sets, in the original source set.

An exhaustive source-cut partition covers the whole positive-density support
in selector measure, even if the original occurrence density has no uniform
positive lower bound. A finite prefix covers more than half that selector
measure. Starting with source mass `Q > 0`, two growth factors at least two,
with this half-support finite truncation between them, contradict the original
source support bound. This is a qualitative, same-old-pair statement only.

No uniform original-occurrence retained fraction, quantitative paid estimate,
uniform depth bound, or common-target/smaller-cap continuation is proved here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.QualitativeUnionGrowthTermination

variable {Ω X L : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace L]

/-- Positive-density support relative to the selector measure, rather than
an unweighted incidence projection or the support of one selected bush. -/
def densitySupport (f : X → ℝ≥0∞) : Set X := {x | f x ≠ 0}

/-- A zero weighted complement forces a selector-null complement of the
positive-density support. No positive lower bound for the density is used. -/
theorem density_support_sdiff_null (σ : Measure X) (f : X → ℝ≥0∞)
    (hf : Measurable f) (A : Set X) (hzero : (σ.withDensity f) Aᶜ = 0) :
    σ (densitySupport f \ A) = 0 := by
  simpa only [densitySupport, sdiff_eq] using (withDensity_apply_eq_zero hf).mp hzero

/-- The support containment is almost everywhere for the selector itself. -/
theorem density_support_ae_subset (σ : Measure X) (f : X → ℝ≥0∞)
    (hf : Measurable f) (A : Set X) (hzero : (σ.withDensity f) Aᶜ = 0) :
    densitySupport f ≤ᵐ[σ] A := by
  have hmem : ∀ᵐ x ∂σ.withDensity f, x ∈ A := ae_iff.mpr hzero
  exact (ae_withDensity_iff hf).mp hmem

/-- Hence the whole positive-density support has at most the original
selector mass of `A`; no edge-mass-to-selector-mass estimate is involved. -/
theorem density_support_measure_le (σ : Measure X) (f : X → ℝ≥0∞)
    (hf : Measurable f) (A : Set X) (hzero : (σ.withDensity f) Aᶜ = 0) :
    σ (densitySupport f) ≤ σ A :=
  measure_mono_ae (density_support_ae_subset σ f hf A hzero)

theorem density_support_real_le (σ : Measure X) [IsFiniteMeasure σ]
    (f : X → ℝ≥0∞) (hf : Measurable f) (A : Set X)
    (hzero : (σ.withDensity f) Aᶜ = 0) :
    σ.real (densitySupport f) ≤ σ.real A :=
  ENNReal.toReal_mono (measure_ne_top σ A) (density_support_measure_le σ f hf A hzero)

/-- Genuine measure domination carries source support to any actual endpoint
law with a measurable selector density. -/
theorem submeasure_density_support_sdiff_null
    (σ μ ν : Measure X) (hν : ν ≤ μ) (A : Set X) (hA : μ Aᶜ = 0)
    (f : X → ℝ≥0∞) (hf : Measurable f) (hdensity : ν = σ.withDensity f) :
    σ (densitySupport f \ A) = 0 := by
  apply density_support_sdiff_null σ f hf A
  rw [← hdensity]
  exact le_antisymm ((hν Aᶜ).trans_eq hA) bot_le

/-- A measurable density is supported on its own positive-density set. -/
theorem withDensity_compl_densitySupport (σ : Measure X) (f : X → ℝ≥0∞)
    (hf : Measurable f) : (σ.withDensity f) (densitySupport f)ᶜ = 0 := by
  rw [withDensity_apply_eq_zero hf]
  simp only [densitySupport, inter_compl_self, measure_empty]

/-- Actual endpoint densities of a submeasure have a.e. smaller supports.
Taking `endpoint = Prod.fst` or `Prod.snd` gives the source and target versions. -/
theorem submeasure_endpoint_density_support_sdiff_null
    (Γ Γ₁ : Measure Ω) (hΓ₁ : Γ₁ ≤ Γ) (σ : Measure X)
    (endpoint : Ω → X) (hendpoint : Measurable endpoint)
    (f g : X → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hroot : Γ.map endpoint = σ.withDensity f)
    (hselected : Γ₁.map endpoint = σ.withDensity g) :
    σ (densitySupport g \ densitySupport f) = 0 := by
  apply submeasure_density_support_sdiff_null σ _ _
    (Measure.map_mono hΓ₁ hendpoint) (densitySupport f) _ g hg hselected
  rw [hroot]
  exact withDensity_compl_densitySupport σ f hf

/-- Exact old-pair reversal exchanges the source and target marginal laws. -/
theorem reversal_source_eq (Γ : Measure (X × X)) :
    (Γ.map Prod.swap).map Prod.fst = Γ.map Prod.snd := by
  rw [Measure.map_map measurable_fst measurable_swap]
  rfl

theorem reversal_target_eq (Γ : Measure (X × X)) :
    (Γ.map Prod.swap).map Prod.snd = Γ.map Prod.fst := by
  rw [Measure.map_map measurable_snd measurable_swap]
  rfl

/-- Arbitrary Markov labels on the same reversed old pair leave its new
source law exactly equal to the previous target law. -/
theorem reversed_labeled_source_eq (Γ : Measure (X × X)) [SFinite Γ]
    (κ : Kernel (X × X) L) [IsMarkovKernel κ] :
    ((Γ.map Prod.swap).compProd κ).map (fun p => p.1.1) = Γ.map Prod.snd := by
  rw [MarkovEndpointPreservation.extension_endpoint _ κ Prod.fst measurable_fst]
  exact reversal_source_eq Γ

/-- Every genuine submeasure after reversal and probability labeling retains
old-target domination by the source law before reversal. -/
theorem reversed_labeled_submeasure_target_le
    (Γ Γ₁ : Measure (X × X)) [SFinite Γ₁] (hΓ₁ : Γ₁ ≤ Γ)
    (κ : Kernel (X × X) L) [IsMarkovKernel κ]
    (ν : Measure ((X × X) × L)) (hν : ν ≤ (Γ₁.map Prod.swap).compProd κ) :
    ν.map (fun p => p.1.2) ≤ Γ.map Prod.fst := by
  have h := MarkovEndpointPreservation.submeasure_endpoint_le
    (Γ₁.map Prod.swap) κ ν hν Prod.snd measurable_snd
  rw [reversal_target_eq] at h
  exact h.trans (Measure.map_mono hΓ₁ measurable_fst)

/-- The second target support is actually contained a.e. in the first source
set, regardless of label-dependent thinning or the intervening source cuts. -/
theorem reversed_labeled_target_support_sdiff_null
    (σ : Measure X) (Γ Γ₁ : Measure (X × X)) [SFinite Γ₁]
    (hΓ₁ : Γ₁ ≤ Γ) (A : Set X) (hA : (Γ.map Prod.fst) Aᶜ = 0)
    (κ : Kernel (X × X) L) [IsMarkovKernel κ]
    (ν : Measure ((X × X) × L)) (hν : ν ≤ (Γ₁.map Prod.swap).compProd κ)
    (c : X → ℝ≥0∞) (hc : Measurable c)
    (hdensity : ν.map (fun p => p.1.2) = σ.withDensity c) :
    σ (densitySupport c \ A) = 0 :=
  submeasure_density_support_sdiff_null σ _ _
    (reversed_labeled_submeasure_target_le Γ Γ₁ hΓ₁ κ ν hν) A hA c hc hdensity

theorem reversed_labeled_target_support_real_le
    (σ : Measure X) [IsFiniteMeasure σ]
    (Γ Γ₁ : Measure (X × X)) [SFinite Γ₁]
    (hΓ₁ : Γ₁ ≤ Γ) (A : Set X) (hA : (Γ.map Prod.fst) Aᶜ = 0)
    (κ : Kernel (X × X) L) [IsMarkovKernel κ]
    (ν : Measure ((X × X) × L)) (hν : ν ≤ (Γ₁.map Prod.swap).compProd κ)
    (c : X → ℝ≥0∞) (hc : Measurable c)
    (hdensity : ν.map (fun p => p.1.2) = σ.withDensity c) :
    σ.real (densitySupport c) ≤ σ.real A := by
  apply density_support_real_le σ c hc A
  rw [← hdensity]
  exact le_antisymm
    (((reversed_labeled_submeasure_target_le Γ Γ₁ hΓ₁ κ ν hν) Aᶜ).trans_eq hA)
    bot_le

/-- Trimming the source to its actual positive-density support leaves the
whole original occurrence measure unchanged. -/
theorem source_density_support_restrict_eq
    (Γ : Measure Ω) (σ : Measure X) (source : Ω → X) (hsource : Measurable source)
    (f : X → ℝ≥0∞) (hf : Measurable f)
    (hdensity : Γ.map source = σ.withDensity f) :
    Γ.restrict (source ⁻¹' densitySupport f) = Γ := by
  apply Measure.restrict_eq_self_of_ae_mem
  apply ae_iff.mpr
  have h := withDensity_compl_densitySupport σ f hf
  have hB : MeasurableSet (densitySupport f) := measurableSet_support hf
  rw [← hdensity, Measure.map_apply hsource hB.compl] at h
  exact h

/-- Each physical source piece can be intersected with the full density
support without losing any original occurrence. Hereditary eligibility can
therefore be preserved while removing selector-positive zero-density padding. -/
theorem source_cut_trim_to_density_support
    (Γ : Measure Ω) (σ : Measure X) (source : Ω → X) (hsource : Measurable source)
    (f : X → ℝ≥0∞) (hf : Measurable f)
    (hdensity : Γ.map source = σ.withDensity f)
    (S : Set X) (hS : MeasurableSet S) :
    Γ.restrict (source ⁻¹' (densitySupport f ∩ S)) = Γ.restrict (source ⁻¹' S) := by
  rw [preimage_inter, inter_comm, ← Measure.restrict_restrict (hsource hS),
    source_density_support_restrict_eq Γ σ source hsource f hf hdensity]

/-- Exhausting the original occurrence by source cuts exhausts its entire
positive-density source support in selector measure, not only edge measure. -/
theorem exhaustive_source_partition_selector_cover
    (Γ : Measure Ω) (σ : Measure X) (source : Ω → X) (hsource : Measurable source)
    (f : X → ℝ≥0∞) (hf : Measurable f)
    (hdensity : Γ.map source = σ.withDensity f)
    (pieces : ℕ → Set X) (hm : ∀ n, MeasurableSet (pieces n))
    (hidentity : Measure.sum (fun n => Γ.restrict (source ⁻¹' pieces n)) = Γ) :
    (σ.restrict (densitySupport f)) (⋃ n, pieces n)ᶜ = 0 := by
  have hU := MeasurableSet.iUnion hm
  have hzero : Γ (source ⁻¹' (⋃ n, pieces n)ᶜ) = 0 := by
    rw [← hidentity, Measure.sum_apply _ (hsource hU.compl)]
    apply ENNReal.tsum_eq_zero.mpr
    intro n
    rw [Measure.restrict_apply (hsource hU.compl)]
    have hempty : (source ⁻¹' (⋃ n, pieces n)ᶜ) ∩ (source ⁻¹' pieces n) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.1 (mem_iUnion.mpr ⟨n, hx.2⟩)
    rw [hempty, measure_empty]
  have hzero' : (σ.withDensity f) (⋃ n, pieces n)ᶜ = 0 := by
    rw [← hdensity, Measure.map_apply hsource hU.compl]
    exact hzero
  rw [Measure.restrict_apply hU.compl, inter_comm]
  exact (withDensity_apply_eq_zero hf).mp hzero'

/-- A countable exhaustive partition has a finite prefix covering more than
half of any positive finite selector support. Its length is not bounded. -/
theorem finite_selector_cover_gt_half
    (σ : Measure X) [IsFiniteMeasure σ] (B : Set X)
    (hBpos : 0 < σ.real B) (pieces : ℕ → Set X)
    (hm : ∀ n, MeasurableSet (pieces n))
    (hdisj : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (hcover : (σ.restrict B) (⋃ n, pieces n)ᶜ = 0) :
    ∃ N : ℕ, σ.real B / 2 < σ.real (B ∩ ⋃ i ∈ Set.Iio N, pieces i) := by
  obtain ⟨N, hN⟩ := PositiveRoutingExhaustion.finite_truncation_arbitrarily_small_tail
    (σ.restrict B) pieces hm hdisj hcover (ENNReal.ofReal (σ.real B / 2))
    (ENNReal.ofReal_pos.mpr (by positivity))
  let D : Set X := ⋃ i ∈ Set.Iio N, pieces i
  have hD : MeasurableSet D := MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => hm i))
  have htail : (σ.restrict B).real Dᶜ < σ.real B / 2 := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hN
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ σ.real B / 2)] at h
    exact h
  have htotal := measureReal_add_measureReal_compl (μ := σ.restrict B) hD
  rw [measureReal_restrict_apply_univ, measureReal_restrict_apply hD] at htotal
  refine ⟨N, ?_⟩
  change σ.real B / 2 < σ.real (B ∩ D)
  rw [inter_comm]
  linarith

/-- The elementary contradiction uses selector masses of the whole supports.
It permits a half-selector-mass finite truncation between the growth steps. -/
theorem two_growths_impossible_of_support_bound
    (Q R S T a : ℝ) (hQ : 0 < Q) (hS : 0 ≤ S) (ha : 2 ≤ a)
    (hfirst : a * Q ≤ R) (hhalf : R / 2 ≤ S)
    (hsecond : a * S ≤ T) (hbound : T ≤ Q) : False := by
  have hfirst' : 2 * Q ≤ R := (mul_le_mul_of_nonneg_right ha hQ.le).trans hfirst
  have hsecond' : 2 * S ≤ T := (mul_le_mul_of_nonneg_right ha hS).trans hsecond
  linarith

/-- Two low-growth outputs on the same old pair are impossible after exact
reversal, probability labels and a half-selector-support source selection.
The final support bound is proved from the actual submeasure/density data. -/
theorem no_two_whole_support_growths
    (σ : Measure X) [IsFiniteMeasure σ]
    (Γ Γ₁ : Measure (X × X)) [SFinite Γ₁]
    (hΓ₁ : Γ₁ ≤ Γ) (A : Set X) (hA : (Γ.map Prod.fst) Aᶜ = 0)
    (hQ : 0 < σ.real A) (b : X → ℝ≥0∞)
    (a : ℝ) (ha : 2 ≤ a) (hfirst : a * σ.real A ≤ σ.real (densitySupport b))
    (D : Set X) (hhalf : σ.real (densitySupport b) / 2 ≤ σ.real D)
    (κ : Kernel (X × X) L) [IsMarkovKernel κ]
    (ν : Measure ((X × X) × L)) (hν : ν ≤ (Γ₁.map Prod.swap).compProd κ)
    (c : X → ℝ≥0∞) (hc : Measurable c)
    (hdensity : ν.map (fun p => p.1.2) = σ.withDensity c)
    (hsecond : a * σ.real D ≤ σ.real (densitySupport c)) : False := by
  exact two_growths_impossible_of_support_bound _ _ _ _ a hQ measureReal_nonneg ha
    hfirst hhalf hsecond
    (reversed_labeled_target_support_real_le σ Γ Γ₁ hΓ₁ A hA κ ν hν c hc hdensity)

/-- The effective finite source support retains every positive-density source
in the chosen finite family. It does not select one favorable source bush. -/
def finiteSelectorSupport (b : X → ℝ≥0∞) (pieces : ℕ → Set X) (N : ℕ) : Set X :=
  densitySupport b ∩ ⋃ i ∈ Set.Iio N, pieces i

/-- Assembled same-old-pair termination: the first target marginal is the
actual density `b`; reverse and probability-label that very submeasure;
exhaust it by source cuts; retain a finite family in selector mass. Every
second submeasure of that family has strictly insufficient target support
for another growth factor `a ≥ 2`. -/
theorem finite_exhaustive_reversal_blocks_second_growth
    (σ : Measure X) [IsFiniteMeasure σ]
    (Γ Γ₁ : Measure (X × X)) [SFinite Γ₁]
    (hΓ₁ : Γ₁ ≤ Γ) (A : Set X) (hA : (Γ.map Prod.fst) Aᶜ = 0)
    (hQ : 0 < σ.real A) (b : X → ℝ≥0∞) (hb : Measurable b)
    (hbdensity : Γ₁.map Prod.snd = σ.withDensity b)
    (a : ℝ) (ha : 2 ≤ a) (hfirst : a * σ.real A ≤ σ.real (densitySupport b))
    (κ : Kernel (X × X) L) [IsMarkovKernel κ]
    (pieces : ℕ → Set X) (hm : ∀ n, MeasurableSet (pieces n))
    (hdisj : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (hidentity : Measure.sum (fun n => ((Γ₁.map Prod.swap).compProd κ).restrict
      ((fun p => p.1.1) ⁻¹' pieces n)) = (Γ₁.map Prod.swap).compProd κ) :
    ∃ N : ℕ, σ.real (densitySupport b) / 2 < σ.real (finiteSelectorSupport b pieces N) ∧
      ∀ (ν : Measure ((X × X) × L)),
        ν ≤ ((Γ₁.map Prod.swap).compProd κ).restrict
          ((fun p => p.1.1) ⁻¹' finiteSelectorSupport b pieces N) →
        ∀ (c : X → ℝ≥0∞), Measurable c →
          ν.map (fun p => p.1.2) = σ.withDensity c →
          σ.real (densitySupport c) < a * σ.real (finiteSelectorSupport b pieces N) := by
  have hsource : ((Γ₁.map Prod.swap).compProd κ).map (fun p => p.1.1) =
      σ.withDensity b := (reversed_labeled_source_eq Γ₁ κ).trans hbdensity
  have hcover := exhaustive_source_partition_selector_cover
    ((Γ₁.map Prod.swap).compProd κ) σ (fun p => p.1.1)
    (measurable_fst.comp measurable_fst) b hb hsource pieces hm hidentity
  have hBpos : 0 < σ.real (densitySupport b) :=
    (mul_pos (by linarith : 0 < a) hQ).trans_le hfirst
  obtain ⟨N, hN⟩ := finite_selector_cover_gt_half σ (densitySupport b) hBpos
    pieces hm hdisj hcover
  refine ⟨N, hN, ?_⟩
  intro ν hν c hc hdensity
  apply lt_of_not_ge
  intro hsecond
  exact no_two_whole_support_growths σ Γ Γ₁ hΓ₁ A hA hQ b a ha hfirst
    (finiteSelectorSupport b pieces N) hN.le κ ν
    (hν.trans Measure.restrict_le_self) c hc hdensity hsecond

/-- Positive hereditary source routability suffices for the entire qualitative
construction. This invokes actual source-density occurrence exhaustion and
then selector-mass finite truncation; no quantitative extraction fraction or
bound for the number of selected pieces is assumed. -/
theorem positive_routing_forces_qualitative_termination
    (σ : Measure X) [IsFiniteMeasure σ]
    (Γ Γ₁ : Measure (X × X)) [IsFiniteMeasure Γ₁]
    (hΓ₁ : Γ₁ ≤ Γ) (A : Set X) (hA : (Γ.map Prod.fst) Aᶜ = 0)
    (hQ : 0 < σ.real A) (b : X → ℝ≥0∞) (hb : Measurable b)
    (hbdensity : Γ₁.map Prod.snd = σ.withDensity b)
    (a : ℝ) (ha : 2 ≤ a) (hfirst : a * σ.real A ≤ σ.real (densitySupport b))
    (κ : Kernel (X × X) L) [IsMarkovKernel κ]
    (P : Set X → Prop) (hempty : P ∅)
    (hhereditary : ∀ s t : Set X, P s → MeasurableSet t → t ⊆ s → P t)
    (hlocal : ∀ s : Set X, MeasurableSet s → σ s ≠ 0 →
      ∃ t : Set X, t ⊆ s ∧ MeasurableSet t ∧ P t ∧ σ t ≠ 0) :
    ∃ (pieces : ℕ → Set X) (N : ℕ),
      (∀ n, MeasurableSet (pieces n)) ∧ (∀ n, P (pieces n)) ∧
      (∀ n, pieces n ⊆ densitySupport b) ∧
      Pairwise (fun i j => Disjoint (pieces i) (pieces j)) ∧
      Measure.sum (fun n => ((Γ₁.map Prod.swap).compProd κ).restrict
        ((fun p => p.1.1) ⁻¹' pieces n)) = (Γ₁.map Prod.swap).compProd κ ∧
      σ.real (densitySupport b) / 2 < σ.real (finiteSelectorSupport b pieces N) ∧
      ∀ (ν : Measure ((X × X) × L)),
        ν ≤ ((Γ₁.map Prod.swap).compProd κ).restrict
          ((fun p => p.1.1) ⁻¹' finiteSelectorSupport b pieces N) →
        ∀ (c : X → ℝ≥0∞), Measurable c →
          ν.map (fun p => p.1.2) = σ.withDensity c →
          σ.real (densitySupport c) < a * σ.real (finiteSelectorSupport b pieces N) := by
  have hsource : ((Γ₁.map Prod.swap).compProd κ).map (fun p => p.1.1) =
      σ.withDensity b := (reversed_labeled_source_eq Γ₁ κ).trans hbdensity
  obtain ⟨pieces, hm, hP, hdisj, hidentity⟩ :=
    PositiveRoutingExhaustion.source_density_routing_exhaustion
      ((Γ₁.map Prod.swap).compProd κ) σ (fun p => p.1.1)
      (measurable_fst.comp measurable_fst) b hb hsource P hempty hhereditary hlocal
  let trimmed : ℕ → Set X := fun n => densitySupport b ∩ pieces n
  have htm (n : ℕ) : MeasurableSet (trimmed n) := (measurableSet_support hb).inter (hm n)
  have htP (n : ℕ) : P (trimmed n) :=
    hhereditary (pieces n) (trimmed n) (hP n) (htm n) inter_subset_right
  have htdisj : Pairwise (fun i j => Disjoint (trimmed i) (trimmed j)) :=
    fun _ _ hij => (hdisj hij).mono inter_subset_right inter_subset_right
  have htidentity : Measure.sum (fun n => ((Γ₁.map Prod.swap).compProd κ).restrict
      ((fun p => p.1.1) ⁻¹' trimmed n)) = (Γ₁.map Prod.swap).compProd κ := by
    have heq (n : ℕ) := source_cut_trim_to_density_support
      ((Γ₁.map Prod.swap).compProd κ) σ (fun p => p.1.1)
      (measurable_fst.comp measurable_fst) b hb hsource (pieces n) (hm n)
    simpa only [trimmed, heq] using hidentity
  obtain ⟨N, hN, hstop⟩ := finite_exhaustive_reversal_blocks_second_growth
    σ Γ Γ₁ hΓ₁ A hA hQ b hb hbdensity a ha hfirst κ trimmed htm htdisj htidentity
  exact ⟨trimmed, N, htm, htP, fun _ => inter_subset_left, htdisj, htidentity, hN, hstop⟩

end StickyKakeya4.QualitativeUnionGrowthTermination
