import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Theorems.Thm_StickyKakeya4_markov_endpoint_preservation

/-!
# The old-neighbor disintegration in equation (419)

A finite measure on ordered old endpoints is disintegrated using mathlib's
constructed conditional kernel. Its source marginal and this Markov kernel
recover the original joint measure exactly. Appending probability labels then
preserves the entire ordered-endpoint measure, including all correlations.

For the root `Γ = (σ.prod σ).withDensity h`, the bound `h ≤ 1` gives finiteness
when `σ` is finite. The source marginal is the measure with density
`x ↦ ∫⁻ y, h (x,y) ∂σ`; it is at most `(σ univ) • σ`, and at most `σ` when
`σ` is a probability measure. These bounds concern the marginal, not the
conditional old-neighbor kernel. In general that kernel is not dominated by
`σ`. Geometric routing, paid/cross estimates, and terminal support are not
proved by this measure-theoretic construction.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StickyKakeya4.OldNeighborDisintegration

variable {X L : Type*} [MeasurableSpace X] [MeasurableSpace L]

section FiniteEdge

variable [StandardBorelSpace X] [Nonempty X]

/-- The actual conditional old-neighbor kernel, constructed by mathlib's
standard-Borel disintegration theorem. -/
noncomputable def oldNeighbor (Γ : Measure (X × X)) [IsFiniteMeasure Γ] :
    Kernel X X := Γ.condKernel

instance oldNeighbor_isMarkov (Γ : Measure (X × X)) [IsFiniteMeasure Γ] :
    IsMarkovKernel (oldNeighbor Γ) := by
  unfold oldNeighbor
  infer_instance

/-- Equation (419), with equality of measures rather than only total masses. -/
theorem old_neighbor_disintegration (Γ : Measure (X × X)) [IsFiniteMeasure Γ] :
    Γ.fst.compProd (oldNeighbor Γ) = Γ :=
  Γ.disintegrate Γ.condKernel

/-- The old-neighbor kernel is a probability measure at every source,
including the arbitrary standard-Borel completion on null sources. -/
theorem old_neighbor_mass (Γ : Measure (X × X)) [IsFiniteMeasure Γ] (x : X) :
    oldNeighbor Γ x univ = 1 :=
  measure_univ

/-- The rectangle form of equation (419). -/
theorem old_neighbor_rectangle (Γ : Measure (X × X)) [IsFiniteMeasure Γ]
    {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    Γ (s ×ˢ t) = ∫⁻ x in s, oldNeighbor Γ x t ∂Γ.fst := by
  conv_lhs => rw [← old_neighbor_disintegration Γ]
  exact Measure.compProd_apply_prod hs ht

/-- New conditional probability labels preserve the ordered old endpoints
after the actual source/old-neighbor construction. -/
theorem labeled_old_endpoint_eq (Γ : Measure (X × X)) [IsFiniteMeasure Γ]
    (η : Kernel (X × X) L) [IsMarkovKernel η] :
    ((Γ.fst.compProd (oldNeighbor Γ)).compProd η).map Prod.fst = Γ := by
  rw [old_neighbor_disintegration]
  exact MarkovEndpointPreservation.extension_fst Γ η

/-- Any measurable observable of the old endpoints is conserved as a law. -/
theorem labeled_old_observable_eq {Y : Type*} [MeasurableSpace Y]
    (Γ : Measure (X × X)) [IsFiniteMeasure Γ]
    (η : Kernel (X × X) L) [IsMarkovKernel η]
    (f : X × X → Y) (hf : Measurable f) :
    ((Γ.fst.compProd (oldNeighbor Γ)).compProd η).map (fun p => f p.1) =
      Γ.map f := by
  rw [old_neighbor_disintegration]
  exact MarkovEndpointPreservation.extension_endpoint Γ η f hf

end FiniteEdge

section DensityRoot

/-- The degree density is the actual first marginal of a measurable root
edge density; this does not identify the joint law with a product measure. -/
theorem root_source_density (σ : Measure X) [SFinite σ]
    {h : X × X → ℝ≥0∞} (hMeas : Measurable h) :
    ((σ.prod σ).withDensity h).fst =
      σ.withDensity (fun x => ∫⁻ y, h (x, y) ∂σ) := by
  ext s hs
  rw [Measure.fst_apply hs, withDensity_apply _ (measurable_fst hs),
    withDensity_apply _ hs]
  rw [← prod_univ, setLIntegral_prod h hMeas.aemeasurable]
  simp only [Measure.restrict_univ]

/-- Root finiteness is derived from its density bound, not postulated. -/
theorem root_isFinite (σ : Measure X) [IsFiniteMeasure σ]
    {h : X × X → ℝ≥0∞} (hh : ∀ᵐ p ∂σ.prod σ, h p ≤ 1) :
    IsFiniteMeasure ((σ.prod σ).withDensity h) :=
  isFiniteMeasure_of_le (σ.prod σ)
    (MarkovEndpointPreservation.root_density_le_product σ hh)

/-- For a finite, unnormalized selector, its total mass is a necessary factor. -/
theorem root_source_le_scaled (σ : Measure X) [IsFiniteMeasure σ]
    {h : X × X → ℝ≥0∞} (hh : ∀ᵐ p ∂σ.prod σ, h p ≤ 1) :
    ((σ.prod σ).withDensity h).fst ≤ (σ univ) • σ := by
  have hle := Measure.fst_mono
    (MarkovEndpointPreservation.root_density_le_product σ hh)
  simpa only [Measure.fst, Measure.map_fst_prod] using hle

/-- Probability normalization makes the old-edge source a submeasure of σ. -/
theorem root_source_le (σ : Measure X) [IsProbabilityMeasure σ]
    {h : X × X → ℝ≥0∞} (hh : ∀ᵐ p ∂σ.prod σ, h p ≤ 1) :
    ((σ.prod σ).withDensity h).fst ≤ σ := by
  simpa only [measure_univ, one_smul] using root_source_le_scaled σ hh

variable [StandardBorelSpace X] [Nonempty X]

/-- The root's old-neighbor kernel with finiteness supplied by `h ≤ 1`. -/
noncomputable def rootOldNeighbor (σ : Measure X) [IsFiniteMeasure σ]
    {h : X × X → ℝ≥0∞} (hh : ∀ᵐ p ∂σ.prod σ, h p ≤ 1) : Kernel X X :=
  letI := root_isFinite σ hh
  oldNeighbor ((σ.prod σ).withDensity h)

instance rootOldNeighbor_isMarkov (σ : Measure X) [IsFiniteMeasure σ]
    {h : X × X → ℝ≥0∞} (hh : ∀ᵐ p ∂σ.prod σ, h p ≤ 1) :
    IsMarkovKernel (rootOldNeighbor σ hh) := by
  unfold rootOldNeighbor
  infer_instance

/-- The density root itself, not an assumed routing invariant, satisfies (419). -/
theorem root_disintegration (σ : Measure X) [IsFiniteMeasure σ]
    {h : X × X → ℝ≥0∞} (hh : ∀ᵐ p ∂σ.prod σ, h p ≤ 1) :
    ((σ.prod σ).withDensity h).fst.compProd (rootOldNeighbor σ hh) =
      (σ.prod σ).withDensity h := by
  haveI := root_isFinite σ hh
  exact old_neighbor_disintegration ((σ.prod σ).withDensity h)

/-- Equation (419) also holds with the explicit degree-density source from
the paper in place of the abstract first marginal. -/
theorem root_degree_disintegration (σ : Measure X) [IsFiniteMeasure σ]
    {h : X × X → ℝ≥0∞} (hMeas : Measurable h)
    (hh : ∀ᵐ p ∂σ.prod σ, h p ≤ 1) :
    (σ.withDensity (fun x => ∫⁻ y, h (x, y) ∂σ)).compProd (rootOldNeighbor σ hh) =
      (σ.prod σ).withDensity h := by
  rw [← root_source_density σ hMeas]
  exact root_disintegration σ hh

/-- Exact conservation of the old-endpoint law after adjoining arbitrary
conditional probability labels to the disintegrated density root. -/
theorem root_labeled_endpoint_eq (σ : Measure X) [IsFiniteMeasure σ]
    {h : X × X → ℝ≥0∞} (hh : ∀ᵐ p ∂σ.prod σ, h p ≤ 1)
    (η : Kernel (X × X) L) [IsMarkovKernel η] :
    ((((σ.prod σ).withDensity h).fst.compProd (rootOldNeighbor σ hh)).compProd η).map
        Prod.fst = (σ.prod σ).withDensity h := by
  rw [root_disintegration]
  exact MarkovEndpointPreservation.extension_fst _ η

/-- The conserved joint law is still bounded by the selector product.
This is not a pointwise domination assertion about `rootOldNeighbor σ hh x`. -/
theorem root_labeled_endpoint_le_product (σ : Measure X) [IsFiniteMeasure σ]
    {h : X × X → ℝ≥0∞} (hh : ∀ᵐ p ∂σ.prod σ, h p ≤ 1)
    (η : Kernel (X × X) L) [IsMarkovKernel η] :
    ((((σ.prod σ).withDensity h).fst.compProd (rootOldNeighbor σ hh)).compProd η).map
        Prod.fst ≤ σ.prod σ := by
  rw [root_labeled_endpoint_eq]
  exact MarkovEndpointPreservation.root_density_le_product σ hh

end DensityRoot

end StickyKakeya4.OldNeighborDisintegration
