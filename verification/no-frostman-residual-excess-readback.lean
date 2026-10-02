import Theorems.Thm_StickyKakeya4_no_frostman_residual_excess

set_option autoImplicit false

#print axioms StickyKakeya4.NoFrostmanResidualExcess.weightedResidualContent_le_inverse_secant_integral
#print axioms StickyKakeya4.NoFrostmanResidualExcess.extend_small_radius_power_bound
#print axioms StickyKakeya4.NoFrostmanResidualExcess.front_dimH_ge_of_residual_power_bound
#print axioms StickyKakeya4.NoFrostmanResidualExcess.arbitrarily_fine_residual_excess_of_dimH_lt
#print axioms StickyKakeya4.NoFrostmanResidualExcess.exists_residual_exponent_gap_of_dimH_lt_four
#print axioms StickyKakeya4.NoFrostmanResidualExcess.full_residual_decay_and_excess_of_dimH_lt_four

open MeasureTheory Set Filter
open scoped ENNReal Topology
open StickyKakeya4

example (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ) (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v d η t : ℝ) (huv : u < v) (hd : 0 < d)
    (hη : 0 < η) (hη2 : η < 2) (ht : 0 < t) (htt : t < 4 - η)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hdim : dimH (unitFront ambient) < ENNReal.ofReal t)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < min ρ₀ 1 ∧
      C * (ENNReal.ofReal ρ) ^ (2 - η) <
        weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
          (fun p => b p.1 - b p.2) (Icc (u - d) (v + d)) ρ :=
  NoFrostmanResidualExcess.arbitrarily_fine_residual_excess_of_dimH_lt
    ambient hcompact σ hσpos hσ b hb hslopes u v d η t huv hd
      hη hη2 ht htt hsupport hdim C hC ρ₀ hρ₀

example (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ) (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v d : ℝ) (huv : u < v) (hd : 0 < d)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hdim : dimH (unitFront ambient) < (4 : ℝ≥0∞)) :
    ∃ η : ℝ, 0 < η ∧ η < 2 ∧ ∀ C : ℝ≥0∞, C ≠ ⊤ →
      ∀ ρ₀ : ℝ, 0 < ρ₀ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < min ρ₀ 1 ∧
        C * (ENNReal.ofReal ρ) ^ (2 - η) <
          weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
            (fun p => b p.1 - b p.2) (Icc (u - d) (v + d)) ρ :=
  (NoFrostmanResidualExcess.full_residual_decay_and_excess_of_dimH_lt_four
    ambient hcompact σ hσpos hσ b hb hslopes u v d huv hd hsupport hdim).2
