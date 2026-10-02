import Theorems.Thm_StickyKakeya4_residual_affine_rescaling

set_option autoImplicit false

#print axioms StickyKakeya4.ResidualAffineRescaling.physicalSlope
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedSlope
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedIntercept
#print axioms StickyKakeya4.ResidualAffineRescaling.physicalSlope_normalizedSlope
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedSlope_physicalSlope
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedSlope_root
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedIntercept_zero
#print axioms StickyKakeya4.ResidualAffineRescaling.normalized_secants
#print axioms StickyKakeya4.ResidualAffineRescaling.collisionTime_smul
#print axioms StickyKakeya4.ResidualAffineRescaling.collisionResidual_smul
#print axioms StickyKakeya4.ResidualAffineRescaling.normalized_collisionTime
#print axioms StickyKakeya4.ResidualAffineRescaling.normalized_collisionResidual
#print axioms StickyKakeya4.ResidualAffineRescaling.normalized_shell_iff
#print axioms StickyKakeya4.ResidualAffineRescaling.normalized_residual_time_iff
#print axioms StickyKakeya4.ResidualAffineRescaling.inverse_secant_weight_rescale
#print axioms StickyKakeya4.ResidualAffineRescaling.normalized_residualContentWeight
#print axioms StickyKakeya4.ResidualAffineRescaling.weightedResidualContent_rescale
#print axioms StickyKakeya4.ResidualAffineRescaling.frontAffineMap
#print axioms StickyKakeya4.ResidualAffineRescaling.frontUnscale
#print axioms StickyKakeya4.ResidualAffineRescaling.frontUnscale_leftInverse
#print axioms StickyKakeya4.ResidualAffineRescaling.frontUnscale_rightInverse
#print axioms StickyKakeya4.ResidualAffineRescaling.frontAffineEquiv
#print axioms StickyKakeya4.ResidualAffineRescaling.heightCoordinates
#print axioms StickyKakeya4.ResidualAffineRescaling.frontAffineEquiv4
#print axioms StickyKakeya4.ResidualAffineRescaling.normalized_frontPoint
#print axioms StickyKakeya4.ResidualAffineRescaling.normalized_front_spatial
#print axioms StickyKakeya4.ResidualAffineRescaling.measurable_normalizedSlope
#print axioms StickyKakeya4.ResidualAffineRescaling.measurable_normalizedIntercept
#print axioms StickyKakeya4.ResidualAffineRescaling.weightedResidualContent_map_normalized
#print axioms StickyKakeya4.ResidualAffineRescaling.map_volume_normalizedSlope
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedSource
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedSource_isProbability
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedSource_le_volume
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedSource_eq_real_mass
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedSource_le_real_density
#print axioms StickyKakeya4.ResidualAffineRescaling.normalized_frontPoint_mem_image_iff
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedDirectedGraph
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedSource_prod
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedDirectedGraph_le_product
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedDirectedGraph_mass
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedDirectedGraph_real_mass
#print axioms StickyKakeya4.ResidualAffineRescaling.normalizedDirectedGraph_mass_le_one

open MeasureTheory Set
open scoped ENNReal
open StickyKakeya4

-- Both endpoint secants retain their physical old time and the literal window.
example (b : E3 → E3) (a₀ a a' : E3) (τ ρ : ℝ) (hτ : 0 < τ) (J : Set ℝ) :
    residualContentWeight J
      (ResidualAffineRescaling.normalizedSlope a₀ τ a - ResidualAffineRescaling.normalizedSlope a₀ τ a')
      (ResidualAffineRescaling.normalizedIntercept b a₀ τ (ResidualAffineRescaling.normalizedSlope a₀ τ a) -
        ResidualAffineRescaling.normalizedIntercept b a₀ τ (ResidualAffineRescaling.normalizedSlope a₀ τ a')) (ρ / τ) =
      ENNReal.ofReal τ * residualContentWeight J (a - a') (b a - b a') ρ :=
  ResidualAffineRescaling.normalized_residualContentWeight b a₀ a a' τ ρ hτ J

-- The actual transported block is a probability with its derived cubic density.
example (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ)
    (hσ : σ ≤ volume) (a₀ : E3) (τ : ℝ) (hτ : 0 < τ) :
    IsProbabilityMeasure (ResidualAffineRescaling.normalizedSource σ a₀ τ) ∧
      ResidualAffineRescaling.normalizedSource σ a₀ τ ≤
        ENNReal.ofReal (τ ^ 3 / (σ univ).toReal) • volume :=
  ⟨ResidualAffineRescaling.normalizedSource_isProbability σ hσpos a₀ τ,
    ResidualAffineRescaling.normalizedSource_le_real_density σ hσpos hσ a₀ τ hτ⟩

-- This is a fixed invertible map on literal E4, with exact support transport.
example (b : E3 → E3) (a₀ a : E3) (τ s : ℝ) (hτ : τ ≠ 0) (S : Set E4) :
    ActualSlopeSource.heightPoint
      (ResidualAffineRescaling.normalizedIntercept b a₀ τ (ResidualAffineRescaling.normalizedSlope a₀ τ a) +
        s • ResidualAffineRescaling.normalizedSlope a₀ τ a) s ∈
      ResidualAffineRescaling.frontAffineEquiv4 a₀ (b a₀) τ hτ '' S ↔
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ S :=
  ResidualAffineRescaling.normalized_frontPoint_mem_image_iff b a₀ a τ s hτ S

-- Ordered endpoint transport preserves directed domination and exact block-mass normalization.
example (μ : Measure E3) [IsFiniteMeasure μ] (Γ : Measure (E3 × E3))
    (hΓ : Γ ≤ μ.prod μ) (a₀ : E3) (τ : ℝ) :
    ResidualAffineRescaling.normalizedDirectedGraph μ Γ a₀ τ ≤
      (ResidualAffineRescaling.normalizedSource μ a₀ τ).prod
        (ResidualAffineRescaling.normalizedSource μ a₀ τ) ∧
      (ResidualAffineRescaling.normalizedDirectedGraph μ Γ a₀ τ univ).toReal =
        (Γ univ).toReal / (μ univ).toReal ^ 2 :=
  ⟨ResidualAffineRescaling.normalizedDirectedGraph_le_product μ Γ hΓ a₀ τ,
    ResidualAffineRescaling.normalizedDirectedGraph_real_mass μ Γ a₀ τ⟩
