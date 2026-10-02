import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Probability labels preserve original endpoint measures

This is the restriction--kernel calculus used in Appendix A, pp. 135--136,
and Lemma 8.56 of the original manuscript. The occurrence measure in (419)
already contains its ordered old endpoints. Appending a probability label
does not change their joint law. All preservation statements below are proved
from mathlib's actual `Measure.compProd`, not assumed in a routing structure.

The joint root density bound `h ≤ 1` implies domination by `σ.prod σ`.
It does not imply domination of the conditional old-neighbor probability
kernel by `σ`, or domination by the occurrence's source marginal times `σ`.
The geometric routing, paid/cross-cap bounds and terminal cap support remain
separate obligations.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StickyKakeya4.MarkovEndpointPreservation

variable {Ω L Y X I : Type*}
  [MeasurableSpace Ω] [MeasurableSpace L] [MeasurableSpace Y]
  [MeasurableSpace X]

/-- Appending a probability label preserves the whole original occurrence,
not just its total mass. The `SFinite` assumption is essential for mathlib's
composition-product construction. -/
theorem extension_fst (μ : Measure Ω) [SFinite μ]
    (κ : Kernel Ω L) [IsMarkovKernel κ] :
    (μ.compProd κ).map Prod.fst = μ :=
  Measure.fst_compProd μ κ

/-- Every measurable inherited observable has exactly its original law.
In particular, the observable can be the ordered old-endpoint pair. -/
theorem extension_endpoint (μ : Measure Ω) [SFinite μ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (endpoint : Ω → Y) (hendpoint : Measurable endpoint) :
    (μ.compProd κ).map (fun p => endpoint p.1) = μ.map endpoint := by
  calc
    _ = ((μ.compProd κ).map Prod.fst).map endpoint :=
      (Measure.map_map hendpoint measurable_fst).symm
    _ = _ := congrArg (Measure.map endpoint) (extension_fst μ κ)

/-- The familiar scalar mass identity follows from the same Markov extension. -/
theorem extension_mass (μ : Measure Ω) [SFinite μ]
    (κ : Kernel Ω L) [IsMarkovKernel κ] :
    μ.compProd κ univ = μ univ :=
  Measure.compProd_apply_univ

/-- A genuine submeasure, including a restriction involving the new label,
has endpoint law dominated by the original occurrence's endpoint law. -/
theorem submeasure_endpoint_le (μ : Measure Ω) [SFinite μ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (ν : Measure (Ω × L)) (hν : ν ≤ μ.compProd κ)
    (endpoint : Ω → Y) (hendpoint : Measurable endpoint) :
    ν.map (fun p => endpoint p.1) ≤ μ.map endpoint := by
  rw [← extension_endpoint μ κ endpoint hendpoint]
  exact Measure.map_mono hν (hendpoint.comp measurable_fst)

/-- Restricting on any measurable collection of original occurrences and
new labels cannot increase the inherited endpoint measure. -/
theorem restriction_endpoint_le (μ : Measure Ω) [SFinite μ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (s : Set (Ω × L))
    (endpoint : Ω → Y) (hendpoint : Measurable endpoint) :
    ((μ.compProd κ).restrict s).map (fun p => endpoint p.1) ≤ μ.map endpoint :=
  submeasure_endpoint_le μ κ _ Measure.restrict_le_self endpoint hendpoint

/-- A fractional restriction with density at most one is a submeasure.
The a.e. bound is enough; no pointwise bound on null sets is needed. -/
theorem density_le (μ : Measure Ω) {f : Ω → ℝ≥0∞}
    (hf : ∀ᵐ x ∂μ, f x ≤ 1) : μ.withDensity f ≤ μ := by
  have hle : μ.withDensity f ≤ μ.withDensity 1 := withDensity_mono hf
  simpa only [withDensity_one] using hle

/-- Fractional thinning after adjoining labels preserves endpoint domination. -/
theorem fractional_endpoint_le (μ : Measure Ω) [SFinite μ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    {f : Ω × L → ℝ≥0∞} (hf : ∀ᵐ p ∂μ.compProd κ, f p ≤ 1)
    (endpoint : Ω → Y) (hendpoint : Measurable endpoint) :
    ((μ.compProd κ).withDensity f).map (fun p => endpoint p.1) ≤ μ.map endpoint :=
  submeasure_endpoint_le μ κ _ (density_le _ hf) endpoint hendpoint

/-- Appendix A's full two-kernel step: thin a marked occurrence, then adjoin
another conditional probability label. Every original endpoint law remains
dominated. Both labels may depend on all coordinates available at their stage. -/
theorem fractional_extension_endpoint_le
    {N : Type*} [MeasurableSpace N]
    (μ : Measure Ω) [SFinite μ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    {f : Ω × L → ℝ≥0∞} (hf : ∀ᵐ p ∂μ.compProd κ, f p ≤ 1)
    (η : Kernel (Ω × L) N) [IsMarkovKernel η]
    (endpoint : Ω → Y) (hendpoint : Measurable endpoint) :
    (((μ.compProd κ).withDensity f).compProd η).map
        (fun p => endpoint p.1.1) ≤ μ.map endpoint := by
  rw [extension_endpoint _ η (fun p => endpoint p.1)
    (hendpoint.comp measurable_fst)]
  exact fractional_endpoint_le μ κ hf endpoint hendpoint

/-- Countably many disjoint restrictions of one labeled occurrence still
have one root measure as their joint budget. -/
theorem sum_subrestrictions_le [Countable I]
    (μ : Measure Ω) (pieces : I → Set Ω)
    (hpieces : ∀ i, MeasurableSet (pieces i))
    (hdisjoint : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (ν : I → Measure Ω) (hν : ∀ i, ν i ≤ μ.restrict (pieces i)) :
    Measure.sum ν ≤ μ := by
  have hsum : Measure.sum ν ≤ Measure.sum (fun i => μ.restrict (pieces i)) := by
    apply Measure.le_iff.mpr
    intro s hs
    simp only [Measure.sum_apply _ hs]
    exact ENNReal.tsum_le_tsum (fun i => hν i s)
  rw [← Measure.restrict_iUnion hdisjoint hpieces] at hsum
  exact hsum.trans Measure.restrict_le_self

/-- A common measurable endpoint map preserves a measure-valued budget.
This requires a measure inequality, not merely a total-mass inequality. -/
theorem sum_endpoint_le (μ : Measure Ω) (ν : I → Measure Ω)
    (hν : Measure.sum ν ≤ μ)
    (endpoint : Ω → Y) (hendpoint : Measurable endpoint) :
    Measure.sum (fun i => (ν i).map endpoint) ≤ μ.map endpoint := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.sum_apply _ hs, Measure.map_apply hendpoint hs]
  simp_rw [Measure.map_apply hendpoint hs]
  rw [← Measure.sum_apply _ (hendpoint hs)]
  exact hν _

/-- Destinations may use different label spaces and different conditional
probability kernels. Their original endpoint laws still satisfy the original
measure budget; no normalization or multiplicity factor is introduced. -/
theorem sum_extensions_endpoint_le
    (Labels : I → Type*) [∀ i, MeasurableSpace (Labels i)]
    (μ : Measure Ω) (ν : I → Measure Ω) [∀ i, SFinite (ν i)]
    (hν : Measure.sum ν ≤ μ)
    (κ : ∀ i, Kernel Ω (Labels i)) [∀ i, IsMarkovKernel (κ i)]
    (endpoint : Ω → Y) (hendpoint : Measurable endpoint) :
    Measure.sum (fun i => ((ν i).compProd (κ i)).map
      (fun p => endpoint p.1)) ≤ μ.map endpoint := by
  simp_rw [extension_endpoint _ _ endpoint hendpoint]
  exact sum_endpoint_le μ ν hν endpoint hendpoint

/-- The original ordered edge measure with density `h ≤ 1` is dominated by
the selector product. Nonnegativity is encoded by the `ℝ≥0∞` codomain. -/
theorem root_density_le_product (σ : Measure X) {h : X × X → ℝ≥0∞}
    (hh : ∀ᵐ p ∂σ.prod σ, h p ≤ 1) :
    (σ.prod σ).withDensity h ≤ σ.prod σ :=
  density_le _ hh

/-- The concrete root invariant for an original ordered pair plus arbitrary
conditional probability labels. The joint endpoint law equals the original
edge-density measure exactly. -/
theorem root_extension_endpoint_eq (σ : Measure X) [SFinite σ]
    (h : X × X → ℝ≥0∞)
    (κ : Kernel (X × X) L) [IsMarkovKernel κ] :
    (((σ.prod σ).withDensity h).compProd κ).map Prod.fst =
      (σ.prod σ).withDensity h :=
  extension_fst _ κ

/-- This discharges root endpoint-product domination for the actual
probability-label construction, with the original ordered endpoints retained. -/
theorem root_extension_endpoint_le_product (σ : Measure X) [SFinite σ]
    {h : X × X → ℝ≥0∞} (hh : ∀ᵐ p ∂σ.prod σ, h p ≤ 1)
    (κ : Kernel (X × X) L) [IsMarkovKernel κ] :
    (((σ.prod σ).withDensity h).compProd κ).map Prod.fst ≤ σ.prod σ := by
  rw [root_extension_endpoint_eq]
  exact root_density_le_product σ hh

/-- Every submeasure of the labeled root retains the same product domination.
In particular a measurable terminal restriction is covered. -/
theorem root_submeasure_endpoint_le_product (σ : Measure X) [SFinite σ]
    {h : X × X → ℝ≥0∞} (hh : ∀ᵐ p ∂σ.prod σ, h p ≤ 1)
    (κ : Kernel (X × X) L) [IsMarkovKernel κ]
    (ν : Measure ((X × X) × L))
    (hν : ν ≤ ((σ.prod σ).withDensity h).compProd κ) :
    ν.map Prod.fst ≤ σ.prod σ :=
  (Measure.map_mono hν measurable_fst).trans
    (root_extension_endpoint_le_product σ hh κ)

/-- The countable terminal endpoint budget follows for actual disjoint
restrictions of one probability-labeled root. This is the measure inequality
needed by the global terminal-band estimate, including label-dependent cuts. -/
theorem root_disjoint_subrestrictions_endpoint_le_product [Countable I]
    (σ : Measure X) [SFinite σ]
    {h : X × X → ℝ≥0∞} (hh : ∀ᵐ p ∂σ.prod σ, h p ≤ 1)
    (κ : Kernel (X × X) L) [IsMarkovKernel κ]
    (pieces : I → Set ((X × X) × L))
    (hpieces : ∀ i, MeasurableSet (pieces i))
    (hdisjoint : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (ν : I → Measure ((X × X) × L))
    (hν : ∀ i, ν i ≤ (((σ.prod σ).withDensity h).compProd κ).restrict (pieces i)) :
    Measure.sum (fun i => (ν i).map Prod.fst) ≤ σ.prod σ :=
  (sum_endpoint_le _ ν (sum_subrestrictions_le _ pieces hpieces hdisjoint ν hν)
    Prod.fst measurable_fst).trans (root_extension_endpoint_le_product σ hh κ)

end StickyKakeya4.MarkovEndpointPreservation
