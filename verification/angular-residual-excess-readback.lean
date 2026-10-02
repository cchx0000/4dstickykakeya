import Theorems.Thm_StickyKakeya4_angular_residual_excess

set_option autoImplicit false

#print axioms StickyKakeya4.AngularResidualExcess.eventually_log_shell_cost_small
#print axioms StickyKakeya4.AngularResidualExcess.eventually_shell_excess_of_full_excess
#print axioms StickyKakeya4.AngularResidualExcess.scaled_radius_le_rpow
#print axioms StickyKakeya4.AngularResidualExcess.angular_loss_le_scaled_radius_loss
#print axioms StickyKakeya4.AngularResidualExcess.arbitrarily_fine_shell_excess_of_full_excess
#print axioms StickyKakeya4.AngularResidualExcess.arbitrarily_fine_shell_excess_of_dimH_lt_four

open MeasureTheory Set Filter
open scoped ENNReal Topology
open StickyKakeya4

-- The original source, literal residual/time-window integrand, and both scales survive.
example (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ) (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v d : ℝ) (huv : u < v) (hd : 0 < d)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hdim : dimH (unitFront ambient) < (4 : ℝ≥0∞)) :
    ∃ η : ℝ, 0 < η ∧ η < 2 ∧ ∀ ρ₀ ε : ℝ, 0 < ρ₀ → 0 < ε →
      ∃ ρ τ : ℝ, 0 < ρ ∧ ρ < min ρ₀ 1 ∧ 0 < τ ∧
        ρ ^ (1 - η / 4) ≤ τ ∧ τ ≤ 2 ∧
        0 < ρ / τ ∧ ρ / τ ≤ ρ ^ (η / 4) ∧ ρ / τ < ε ∧
        (ENNReal.ofReal ρ) ^ (2 - η / 2) <
          AngularResidualShell.angularShellContent (σ.prod σ) (fun p => p.1 - p.2)
            (fun p => b p.1 - b p.2) (Icc (u - d) (v + d)) ρ τ (2 * τ) ∧
        ∀ ζ : ℝ, 0 ≤ ζ → τ ^ (-ζ) ≤ (ρ / τ) ^ (-4 * ζ / η) :=
  AngularResidualExcess.arbitrarily_fine_shell_excess_of_dimH_lt_four
    ambient hcompact σ hσpos hσ b hb hslopes u v d huv hd hsupport hdim

example (ρ τ η ζ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hη : 0 < η) (hζ : 0 ≤ ζ)
    (hcut : ρ ^ (1 - η / 4) ≤ τ) :
    τ ^ (-ζ) ≤ (ρ / τ) ^ (-4 * ζ / η) :=
  AngularResidualExcess.angular_loss_le_scaled_radius_loss ρ τ η ζ hρ hρ1 hη hζ hcut
