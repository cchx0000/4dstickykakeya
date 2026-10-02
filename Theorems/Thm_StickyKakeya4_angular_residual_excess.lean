import Theorems.Thm_StickyKakeya4_angular_residual_shell
import Theorems.Thm_StickyKakeya4_no_frostman_residual_excess
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Angular residual excess at vanishing scaled radius

This module extracts literal angular-shell excess from full weighted residual
excess. The small-secant tail and the logarithmic shell count are supplied by
the certified angular-shell theorem, rather than assumed shell mass.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4.AngularResidualExcess

/-- A logarithmic shell count is negligible compared with every positive
inverse power at the origin. -/
theorem eventually_log_shell_cost_small (A a b : ℝ) (hb : 0 < b) :
    ∀ᶠ ρ : ℝ in 𝓝[>] 0,
      (A + Real.log (2 / ρ ^ a) / Real.log 2 + 1) * ρ ^ b ≤ 1 := by
  have hp : Tendsto (fun ρ : ℝ => ρ ^ b) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuous_rpow_const hb.le).continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    simpa only [Real.zero_rpow hb.ne'] using h
  have hl := tendsto_log_mul_rpow_nhdsGT_zero hb
  have hlim : Tendsto
      (fun ρ : ℝ => (A + 2) * ρ ^ b - (a / Real.log 2) * (Real.log ρ * ρ ^ b))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (hp.const_mul (A + 2)).sub (hl.const_mul (a / Real.log 2))
  have heq : (fun ρ : ℝ => (A + Real.log (2 / ρ ^ a) / Real.log 2 + 1) * ρ ^ b) =ᶠ[𝓝[>] 0]
      (fun ρ : ℝ => (A + 2) * ρ ^ b - (a / Real.log 2) * (Real.log ρ * ρ ^ b)) := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have hr : 0 < ρ := hρ
    rw [Real.log_div (by norm_num) (Real.rpow_pos_of_pos hr a).ne', Real.log_rpow hr]
    have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    field_simp
    ring
  have hlim' := hlim.congr' heq.symm
  exact (hlim'.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)

/-- At sufficiently small radii, full residual excess forces excess on one
of the literal angular shells above `ρ^(1-η/4)`. The coefficient is exactly one. -/
theorem eventually_shell_excess_of_full_excess
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (J : Set ℝ) (hJ : MeasurableSet J) (η : ℝ) (hη : 0 < η) (hη4 : η < 4) :
    ∀ᶠ ρ : ℝ in 𝓝[>] 0, 0 < ρ → ρ ≤ 1 →
      (ENNReal.ofReal ρ) ^ (2 - η) < weightedResidualContent (σ.prod σ)
        (fun p => p.1 - p.2) (fun p => b p.1 - b p.2) J ρ →
      ∃ τ : ℝ, ρ ^ (1 - η / 4) ≤ τ ∧ τ ≤ 2 ∧
        (ENNReal.ofReal ρ) ^ (2 - η / 2) <
          AngularResidualShell.angularShellContent (σ.prod σ) (fun p => p.1 - p.2)
            (fun p => b p.1 - b p.2) J ρ τ (2 * τ) := by
  let A : ℝ≥0∞ := 2 * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ
  have hA : A ≠ ⊤ := by dsimp [A]; finiteness
  filter_upwards [eventually_log_shell_cost_small A.toReal (1 - η / 4) (η / 2) (by linarith)]
    with ρ hcost
  intro hρ hρ1 hexcess
  let u : ℝ := ρ ^ (1 - η / 4)
  have hu : 0 < u := Real.rpow_pos_of_pos hρ _
  have hu1 : u ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by linarith)
  obtain ⟨N, k, hN, hcount, hk, hulo, huhi, hbound⟩ :=
    AngularResidualShell.exists_bounded_dyadic_slope_shell σ hσ b hb hslopes J hJ ρ u hu hu1
  refine ⟨u * 2 ^ k, hulo, huhi, ?_⟩
  let M : ℝ := Real.log (2 / u) / Real.log 2 + 1
  have hM : 0 ≤ M := (Nat.cast_nonneg N).trans hcount
  have hNenn : (N : ℝ≥0∞) ≤ ENNReal.ofReal M := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcount
  have hupow : ENNReal.ofReal u ^ (2 : ℕ) = (ENNReal.ofReal ρ) ^ (2 - η / 2) := by
    rw [← ENNReal.ofReal_pow hu.le]
    have he : u ^ (2 : ℕ) = ρ ^ (2 - η / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
      congr 1
      ring
    rw [he, ENNReal.ofReal_rpow_of_pos hρ]
  have hreal : (A.toReal + M) * ρ ^ (2 - η / 2) ≤ ρ ^ (2 - η) := by
    calc
      _ = ((A.toReal + M) * ρ ^ (η / 2)) * ρ ^ (2 - η) := by
        rw [show (2 - η / 2 : ℝ) = η / 2 + (2 - η) by ring, Real.rpow_add hρ]
        ring
      _ ≤ 1 * ρ ^ (2 - η) := mul_le_mul_of_nonneg_right (by simpa only [M, u, add_assoc] using hcost) (Real.rpow_nonneg hρ.le _)
      _ = _ := one_mul _
  have hcostenn : (A + ENNReal.ofReal M) * (ENNReal.ofReal ρ) ^ (2 - η / 2) ≤
      (ENNReal.ofReal ρ) ^ (2 - η) := by
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_mul (add_nonneg ENNReal.toReal_nonneg hM),
      ENNReal.ofReal_add ENNReal.toReal_nonneg hM,
      ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_rpow_of_pos hρ,
      ← ENNReal.ofReal_rpow_of_pos hρ] at h
    exact h
  by_contra hnot
  have hsmall := le_of_not_gt hnot
  apply hexcess.not_ge
  calc
    _ ≤ A * ENNReal.ofReal u ^ 2 + (N : ℝ≥0∞) *
        AngularResidualShell.angularShellContent (σ.prod σ) (fun p => p.1 - p.2)
          (fun p => b p.1 - b p.2) J ρ (u * 2 ^ k) (2 * (u * 2 ^ k)) := hbound
    _ ≤ A * (ENNReal.ofReal ρ) ^ (2 - η / 2) +
        ENNReal.ofReal M * (ENNReal.ofReal ρ) ^ (2 - η / 2) := by
      rw [hupow]
      exact add_le_add le_rfl (mul_le_mul hNenn hsmall bot_le bot_le)
    _ = (A + ENNReal.ofReal M) * (ENNReal.ofReal ρ) ^ (2 - η / 2) := by ring
    _ ≤ _ := hcostenn

/-- The chosen angular cutoff quantitatively forces the normalized residual
radius to zero and puts the physical radius below the angular scale. -/
theorem scaled_radius_le_rpow
    (ρ τ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hη : 0 < η)
    (hcut : ρ ^ (1 - η / 4) ≤ τ) :
    0 < ρ / τ ∧ ρ / τ ≤ ρ ^ (η / 4) ∧ ρ ≤ τ := by
  have hu : 0 < ρ ^ (1 - η / 4) := Real.rpow_pos_of_pos hρ _
  have hτ : 0 < τ := hu.trans_le hcut
  have hr : ρ ≤ ρ ^ (1 - η / 4) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (show 1 - η / 4 ≤ 1 by linarith)
  refine ⟨div_pos hρ hτ, (div_le_iff₀ hτ).mpr ?_, hr.trans hcut⟩
  calc
    ρ = ρ ^ (η / 4) * ρ ^ (1 - η / 4) := by
      rw [← Real.rpow_add hρ, show η / 4 + (1 - η / 4) = 1 by ring, Real.rpow_one]
    _ ≤ ρ ^ (η / 4) * τ := mul_le_mul_of_nonneg_left hcut (Real.rpow_nonneg hρ.le _)

/-- The same extracted scale converts every angular density loss into a
controlled normalized-radius loss, with constant one. -/
theorem angular_loss_le_scaled_radius_loss
    (ρ τ η ζ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hη : 0 < η) (hζ : 0 ≤ ζ)
    (hcut : ρ ^ (1 - η / 4) ≤ τ) :
    τ ^ (-ζ) ≤ (ρ / τ) ^ (-4 * ζ / η) := by
  obtain ⟨hrpos, hrbound, hrτ⟩ := scaled_radius_le_rpow ρ τ η hρ hρ1 hη hcut
  have hpow : (ρ / τ) ^ (4 / η) ≤ ρ := by
    calc
      _ ≤ (ρ ^ (η / 4)) ^ (4 / η) :=
        Real.rpow_le_rpow hrpos.le hrbound (by positivity)
      _ = ρ := by
        rw [← Real.rpow_mul hρ.le, show η / 4 * (4 / η) = 1 by field_simp, Real.rpow_one]
  calc
    τ ^ (-ζ) ≤ ((ρ / τ) ^ (4 / η)) ^ (-ζ) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hrpos _) (hpow.trans hrτ) (by linarith)
    _ = (ρ / τ) ^ (-4 * ζ / η) := by
      rw [← Real.rpow_mul hrpos.le]
      congr 1
      ring

/-- Arbitrarily fine full residual excess produces arbitrarily fine literal
shell excess with normalized radius as small as prescribed. The angular loss
conversion holds for every nonnegative regularization exponent. -/
theorem arbitrarily_fine_shell_excess_of_full_excess
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (J : Set ℝ) (hJ : MeasurableSet J) (η : ℝ) (hη : 0 < η) (hη4 : η < 4)
    (hexcess : ∀ ρ₀ : ℝ, 0 < ρ₀ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < min ρ₀ 1 ∧
      (ENNReal.ofReal ρ) ^ (2 - η) < weightedResidualContent (σ.prod σ)
        (fun p => p.1 - p.2) (fun p => b p.1 - b p.2) J ρ)
    (ρ₀ ε : ℝ) (hρ₀ : 0 < ρ₀) (hε : 0 < ε) :
    ∃ ρ τ : ℝ, 0 < ρ ∧ ρ < min ρ₀ 1 ∧ 0 < τ ∧
      ρ ^ (1 - η / 4) ≤ τ ∧ τ ≤ 2 ∧
      0 < ρ / τ ∧ ρ / τ ≤ ρ ^ (η / 4) ∧ ρ / τ < ε ∧
      (ENNReal.ofReal ρ) ^ (2 - η / 2) <
        AngularResidualShell.angularShellContent (σ.prod σ) (fun p => p.1 - p.2)
          (fun p => b p.1 - b p.2) J ρ τ (2 * τ) ∧
      ∀ ζ : ℝ, 0 ≤ ζ → τ ^ (-ζ) ≤ (ρ / τ) ^ (-4 * ζ / η) := by
  have hp : Tendsto (fun ρ : ℝ => ρ ^ (η / 4)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuous_rpow_const (show 0 ≤ η / 4 by linarith)).continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    simpa only [Real.zero_rpow (show η / 4 ≠ 0 by linarith)] using h
  have hgood := (eventually_shell_excess_of_full_excess σ hσ b hb hslopes J hJ η hη hη4).and
    (hp.eventually (Iio_mem_nhds hε))
  obtain ⟨δ, hδ, hgoodδ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hgood
  obtain ⟨ρ, hρ, hρsmall, hZ⟩ := hexcess (min ρ₀ δ) (lt_min hρ₀ hδ)
  have hρ1 : ρ < 1 := lt_of_lt_of_le hρsmall (min_le_right _ _)
  have hρδ : ρ < δ := lt_of_lt_of_le hρsmall ((min_le_left _ _).trans (min_le_right _ _))
  have hρ₀' : ρ < ρ₀ := lt_of_lt_of_le hρsmall ((min_le_left _ _).trans (min_le_left _ _))
  obtain ⟨hshell, hpowε⟩ := hgoodδ ⟨hρ, hρδ⟩
  obtain ⟨τ, hcut, hτ2, hmass⟩ := hshell hρ hρ1.le hZ
  have hτ : 0 < τ := (Real.rpow_pos_of_pos hρ _).trans_le hcut
  obtain ⟨hrpos, hrbound, _⟩ := scaled_radius_le_rpow ρ τ η hρ hρ1.le hη hcut
  exact ⟨ρ, τ, hρ, lt_min hρ₀' hρ1, hτ, hcut, hτ2, hrpos, hrbound,
    hrbound.trans_lt hpowε, hmass,
    fun ζ hζ => angular_loss_le_scaled_radius_loss ρ τ η ζ hρ hρ1.le hη hζ hcut⟩

/-- A strict dimension deficit yields literal angular residual excess at
arbitrarily small physical and normalized radii, without assuming shell mass. -/
theorem arbitrarily_fine_shell_excess_of_dimH_lt_four
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
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
        ∀ ζ : ℝ, 0 ≤ ζ → τ ^ (-ζ) ≤ (ρ / τ) ^ (-4 * ζ / η) := by
  obtain ⟨η, hη, hη2, hexcess⟩ :=
    (NoFrostmanResidualExcess.full_residual_decay_and_excess_of_dimH_lt_four
      ambient hcompact σ hσpos hσ b hb hslopes u v d huv hd hsupport hdim).2
  refine ⟨η, hη, hη2, ?_⟩
  intro ρ₀ ε hρ₀ hε
  apply arbitrarily_fine_shell_excess_of_full_excess σ hσ b hb hslopes
    (Icc (u - d) (v + d)) measurableSet_Icc η hη (by linarith) ?_ ρ₀ ε hρ₀ hε
  intro r₀ hr₀
  simpa only [one_mul] using hexcess 1 (by norm_num) r₀ hr₀

end StickyKakeya4.AngularResidualExcess
