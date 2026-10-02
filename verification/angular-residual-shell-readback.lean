import Theorems.Thm_StickyKakeya4_angular_residual_shell

set_option autoImplicit false

#print axioms StickyKakeya4.AngularResidualShell.short_inverse_tail_le_of_cubic
#print axioms StickyKakeya4.AngularResidualShell.slope_pair_short_inverse_tail_le
#print axioms StickyKakeya4.AngularResidualShell.slope_pair_secant_pos_ae
#print axioms StickyKakeya4.AngularResidualShell.slope_pair_short_inverse_tail_including_diagonal_le
#print axioms StickyKakeya4.AngularResidualShell.angularShellContent
#print axioms StickyKakeya4.AngularResidualShell.exists_dyadic_shell_of_le
#print axioms StickyKakeya4.AngularResidualShell.weightedResidualContent_le_short_tail_add_shells
#print axioms StickyKakeya4.AngularResidualShell.exists_shell_carrying_residual_content
#print axioms StickyKakeya4.AngularResidualShell.exists_slope_shell_carrying_residual_content
#print axioms StickyKakeya4.AngularResidualShell.exists_bounded_dyadic_slope_shell

open MeasureTheory Set Filter
open scoped ENNReal Topology
open StickyKakeya4

-- The cutoff and dyadic shell are extracted from the full literal content.
example (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (J : Set ℝ) (hJ : MeasurableSet J) (ρ u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
    ∃ N k : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.log (2 / u) / Real.log 2 + 1 ∧
      k < N ∧ u ≤ u * 2 ^ k ∧ u * 2 ^ k ≤ 2 ∧
      weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
        (fun p => b p.1 - b p.2) J ρ ≤
      2 * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ * ENNReal.ofReal u ^ 2 +
        (N : ℝ≥0∞) * AngularResidualShell.angularShellContent (σ.prod σ)
          (fun p => p.1 - p.2) (fun p => b p.1 - b p.2) J ρ
            (u * 2 ^ k) (2 * (u * 2 ^ k)) :=
  AngularResidualShell.exists_bounded_dyadic_slope_shell σ hσ b hb hslopes J hJ ρ u hu hu1

-- The singular inverse norm is retained on the diagonal; its nullity is proved.
example (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (τ : ℝ) (hτ : 0 < τ) :
    (∫⁻ p : E3 × E3 in {p | ‖p.1 - p.2‖ ≤ τ},
      (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹ ∂σ.prod σ) ≤
        2 * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ * ENNReal.ofReal τ ^ 2 :=
  AngularResidualShell.slope_pair_short_inverse_tail_including_diagonal_le σ hσ τ hτ
