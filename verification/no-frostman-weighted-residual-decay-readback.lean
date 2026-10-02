import Theorems.Thm_StickyKakeya4_no_frostman_weighted_residual_decay

set_option autoImplicit false

#print axioms StickyKakeya4.NoFrostmanWeightedResidualDecay.finite_inverse_secant_integral
#print axioms StickyKakeya4.NoFrostmanWeightedResidualDecay.tendsto_residualContentWeight_zero
#print axioms StickyKakeya4.NoFrostmanWeightedResidualDecay.tendsto_weightedResidualContent_zero_of_exact_collision_null
#print axioms StickyKakeya4.NoFrostmanWeightedResidualDecay.no_front_frostman_tendsto_weightedResidualContent_zero

open MeasureTheory Set Filter
open scoped ENNReal Topology
open StickyKakeya4

example (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume) :
    (∫⁻ p : E3 × E3, (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹ ∂σ.prod σ) < ⊤ :=
  NoFrostmanWeightedResidualDecay.finite_inverse_secant_integral σ hσ

example (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v : ℝ) (huv : u < v)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hno : ¬ HasFrontFrostmanMeasures ambient) (J : Set ℝ) (hJ : MeasurableSet J) :
    Tendsto (fun r : ℝ => weightedResidualContent (σ.prod σ)
      (fun p => p.1 - p.2) (fun p => b p.1 - b p.2) J r)
      (𝓝[>] 0) (𝓝 0) :=
  NoFrostmanWeightedResidualDecay.no_front_frostman_tendsto_weightedResidualContent_zero
    ambient hcompact σ hσ b hb hslopes u v huv hsupport hno J hJ
