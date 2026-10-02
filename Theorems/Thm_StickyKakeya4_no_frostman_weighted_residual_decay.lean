import Theorems.Thm_StickyKakeya4_no_frostman_exact_collision_null
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Qualitative decay of the full weighted residual content

The original inverse-secant weight is integrable under a finite slope source
dominated by three-dimensional volume. The exact-collision nullity theorem
therefore gives decay of the full weighted residual content by dominated
convergence, without fixing a positive angular cutoff.

This is qualitative decay for the fixed source. The manuscript's quantitative
residual estimate of order `ρ^(2-η)` remains a separate geometric obligation.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4.NoFrostmanWeightedResidualDecay

/-- The cubic small-secant estimate controls the original inverse-secant
weight, including its genuine infinite value on the null diagonal. -/
theorem finite_inverse_secant_integral
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume) :
    (∫⁻ p : E3 × E3, (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹ ∂σ.prod σ) < ⊤ := by
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.pi * 4 / 3) * σ univ
  have hK : K ≠ ⊤ := by dsimp [K]; finiteness
  have hsub : ∀ r : ℝ, 0 < r → r < 1 →
      (σ.prod σ) {p : E3 × E3 | ‖p.1 - p.2‖ ≤ r} ≤
        ENNReal.ofReal (K.toReal * r ^ (3 : ℝ)) := by
    intro r hr _
    calc
      _ ≤ K * ENNReal.ofReal r ^ 3 := by
        simpa only [one_mul] using slope_pair_near_mass_le_cubic σ 1 (by simpa using hσ) r
      _ = _ := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK,
          ← ENNReal.ofReal_rpow_of_pos hr, ENNReal.rpow_ofNat]
  have h := finite_inverse_energy_of_sublevel_power (σ.prod σ)
    (fun p : E3 × E3 => ‖p.1 - p.2‖) (by fun_prop) (fun p => norm_nonneg _)
    K.toReal 3 1 ENNReal.toReal_nonneg (by norm_num) (by norm_num) hsub
  simpa only [ENNReal.rpow_neg_one] using h

/-- Away from exact off-diagonal contact, the literal residual-content
weight is eventually zero as the collision radius tends to zero. -/
theorem tendsto_residualContentWeight_zero
    (J : Set ℝ) (α β : E3)
    (h : ¬ (α ≠ 0 ∧ collisionResidual α β = 0)) :
    Tendsto (fun r : ℝ => residualContentWeight J α β r) (𝓝[>] 0) (𝓝 0) := by
  classical
  by_cases hα : α = 0
  · simp only [residualContentWeight, hα, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
    exact tendsto_const_nhds
  · have hres : collisionResidual α β ≠ 0 := fun he => h ⟨hα, he⟩
    have hnorm : 0 < ‖collisionResidual α β‖ := norm_pos_iff.mpr hres
    have heq : (fun r : ℝ => residualContentWeight J α β r) =ᶠ[𝓝[>] 0] (fun _ => 0) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hnorm)] with r hr
      simp only [mem_Iio] at hr
      simp [residualContentWeight, not_le.mpr hr]
    exact tendsto_const_nhds.congr' heq.symm

/-- Exact-collision nullity implies decay of the full original weighted
residual content, without any fixed-angle restriction. -/
theorem tendsto_weightedResidualContent_zero_of_exact_collision_null
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b)
    (hexact : (σ.prod σ) (NoFrostmanExactCollision.exactEdges b) = 0)
    (J : Set ℝ) (hJ : MeasurableSet J) :
    Tendsto (fun r : ℝ => weightedResidualContent (σ.prod σ)
      (fun p => p.1 - p.2) (fun p => b p.1 - b p.2) J r)
      (𝓝[>] 0) (𝓝 0) := by
  have hnot : ∀ᵐ p ∂σ.prod σ, p ∉ NoFrostmanExactCollision.exactEdges b := by
    rw [ae_iff]
    simpa only [not_not, NoFrostmanExactCollision.exactEdges, mem_ofPred_eq] using hexact
  have hlim := tendsto_lintegral_filter_of_dominated_convergence
    (μ := σ.prod σ) (f := fun _ => 0)
    (fun p : E3 × E3 => (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹)
    (F := fun r p => residualContentWeight J (p.1 - p.2) (b p.1 - b p.2) r)
    (Filter.Eventually.of_forall (fun r => measurable_residualContentWeight _ _
      (measurable_fst.sub measurable_snd)
      ((hb.comp measurable_fst).sub (hb.comp measurable_snd)) J hJ r))
    (Filter.Eventually.of_forall (fun r => Filter.Eventually.of_forall (fun p => by
      classical
      unfold residualContentWeight
      split_ifs <;> simp)))
    (finite_inverse_secant_integral σ hσ).ne
    (hnot.mono (fun p hp => tendsto_residualContentWeight_zero J _ _ (by
      simpa only [NoFrostmanExactCollision.exactEdges, mem_ofPred_eq,
        sub_ne_zero] using hp)))
  simpa only [weightedResidualContent, lintegral_zero] using hlim

/-- No supported Frostman measures forces qualitative decay of the literal
Definition 6.26 weighted residual content after summing all angular scales. -/
theorem no_front_frostman_tendsto_weightedResidualContent_zero
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v : ℝ) (huv : u < v)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hno : ¬ HasFrontFrostmanMeasures ambient) (J : Set ℝ) (hJ : MeasurableSet J) :
    Tendsto (fun r : ℝ => weightedResidualContent (σ.prod σ)
      (fun p => p.1 - p.2) (fun p => b p.1 - b p.2) J r)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_weightedResidualContent_zero_of_exact_collision_null σ hσ b hb
    (NoFrostmanExactCollision.no_front_frostman_exact_collision_null ambient hcompact
      σ hσ b hb hslopes u v huv hsupport hno) J hJ

end StickyKakeya4.NoFrostmanWeightedResidualDecay
