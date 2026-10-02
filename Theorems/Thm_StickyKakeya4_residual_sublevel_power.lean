import Theorems.Thm_StickyKakeya4_residual_collision_bridge
import Theorems.Thm_StickyKakeya4_global_terminal_band
import Theorems.Thm_StickyKakeya4_residual_energy

/-!
# Bounded direction density and the residual sublevel exponent

This is the analytic reduction in Theorem 6.27 of the original manuscript.
A three-dimensional slope measure dominated by Lebesgue measure gives the
small-secant cubic term. Together with the weighted residual estimate of
exponent `2 - η`, the exact collision fibre estimate gives the averaged
collision sublevel exponent `3 - η`. The residual estimate remains an explicit
geometric premise; no routing or residual power estimate is assumed proved.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- The small-secant term is cubic for an actual bounded-density slope measure.
The constant is the exact volume of the Euclidean unit ball in dimension three. -/
theorem slope_pair_near_mass_le_cubic
    (σ : Measure E3) [SFinite σ] (L : ℝ≥0∞)
    (hσ : σ ≤ L • volume) (r : ℝ) :
    (σ.prod σ) {p : E3 × E3 | ‖p.1 - p.2‖ ≤ r} ≤
      (L * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ) * ENNReal.ofReal r ^ 3 := by
  have hball (a : E3) : σ (Metric.closedBall a r) ≤
      L * ENNReal.ofReal (Real.pi * 4 / 3) * ENNReal.ofReal r ^ 3 := by
    calc
      σ (Metric.closedBall a r) ≤ (L • volume) (Metric.closedBall a r) := hσ _
      _ = L * ENNReal.ofReal (Real.pi * 4 / 3) * ENNReal.ofReal r ^ 3 := by
        rw [Measure.smul_apply, smul_eq_mul, EuclideanSpace.volume_closedBall_fin_three]
        ring
  have h := GlobalTerminalBand.product_band_le_of_ball_bound σ measurable_id r
    (L * ENNReal.ofReal (Real.pi * 4 / 3) * ENNReal.ofReal r ^ 3)
    (fun a => by simpa using hball a)
  simpa only [GlobalTerminalBand.directionBand, id_eq, dist_eq_norm,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- For the source's actual ordered slope pairs, the near-direction remainder
in the collision estimate is supplied by bounded Lebesgue density. -/
theorem averaged_slope_collision_mass_le_residual_cubic
    (σ : Measure E3) [SFinite σ] (L : ℝ≥0∞)
    (hσ : σ ≤ L • volume) (b : E3 → E3) (hb : Measurable b)
    (u v d ρ : ℝ) (hd : 0 < d) (hρ : 0 ≤ ρ) :
    (∫⁻ s in Icc u v, (σ.prod σ)
      {p : E3 × E3 | ‖(b p.1 - b p.2) + s • (p.1 - p.2)‖ ≤ ρ}) ≤
      ENNReal.ofReal (2 * ρ) *
        weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
          (fun p => b p.1 - b p.2) (Icc (u - d) (v + d)) ρ +
      ENNReal.ofReal (v - u) *
        ((L * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ) *
          ENNReal.ofReal (ρ / d) ^ 3) := by
  exact (averaged_collision_mass_le_residual_plus_near (σ.prod σ)
    (fun p => p.1 - p.2) (fun p => b p.1 - b p.2)
    (measurable_fst.sub measurable_snd)
    ((hb.comp measurable_fst).sub (hb.comp measurable_snd)) u v d ρ hd hρ).trans
    (by
      gcongr
      exact slope_pair_near_mass_le_cubic σ L hσ (ρ / d))

/-- The residual exponent `2 - η` yields the averaged collision exponent
`3 - η`. The constant is independent of the collision radius. -/
theorem averaged_slope_collision_mass_le_power
    (σ : Measure E3) [SFinite σ] (L C : ℝ≥0∞)
    (hσ : σ ≤ L • volume) (b : E3 → E3) (hb : Measurable b)
    (u v d η ρ : ℝ) (hd : 0 < d) (hη : 0 ≤ η)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hres : weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
      (fun p => b p.1 - b p.2) (Icc (u - d) (v + d)) ρ ≤
        C * (ENNReal.ofReal ρ) ^ (2 - η)) :
    (∫⁻ s in Icc u v, (σ.prod σ)
      {p : E3 × E3 | ‖(b p.1 - b p.2) + s • (p.1 - p.2)‖ ≤ ρ}) ≤
      (2 * C + ENNReal.ofReal (v - u) *
        (L * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ) *
          (ENNReal.ofReal d)⁻¹ ^ 3) * (ENNReal.ofReal ρ) ^ (3 - η) := by
  let a := ENNReal.ofReal ρ
  have ha : a ≠ 0 := by simp [a, hρ.not_ge]
  have ha_top : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have haone : a ≤ 1 := by simpa [a] using (ENNReal.ofReal_le_ofReal hρone)
  have hpower : a ^ (3 : ℕ) ≤ a ^ (3 - η) := by
    rw [← ENNReal.rpow_natCast]
    exact ENNReal.rpow_le_rpow_of_exponent_ge haone (by norm_num; linarith)
  have hprod : a * a ^ (2 - η) = a ^ (3 - η) := by
    rw [show (3 - η : ℝ) = 1 + (2 - η) by ring,
      ENNReal.rpow_add _ _ ha ha_top, ENNReal.rpow_one]
  calc
    _ ≤ ENNReal.ofReal (2 * ρ) *
        weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
          (fun p => b p.1 - b p.2) (Icc (u - d) (v + d)) ρ +
        ENNReal.ofReal (v - u) *
          ((L * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ) *
            ENNReal.ofReal (ρ / d) ^ 3) :=
      averaged_slope_collision_mass_le_residual_cubic σ L hσ b hb u v d ρ hd hρ.le
    _ ≤ ENNReal.ofReal (2 * ρ) * (C * a ^ (2 - η)) +
        ENNReal.ofReal (v - u) *
          ((L * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ) *
            ENNReal.ofReal (ρ / d) ^ 3) := by gcongr
    _ = 2 * C * a ^ (3 - η) +
        (ENNReal.ofReal (v - u) *
          (L * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ) *
            (ENNReal.ofReal d)⁻¹ ^ 3) * a ^ (3 : ℕ) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_div_of_pos hd]
      simp only [div_eq_mul_inv, mul_pow, ENNReal.ofReal_ofNat]
      dsimp only [a] at hprod ⊢
      rw [show 2 * ENNReal.ofReal ρ * (C * ENNReal.ofReal ρ ^ (2 - η)) =
        2 * C * (ENNReal.ofReal ρ * ENNReal.ofReal ρ ^ (2 - η)) by ring, hprod]
      ring
    _ ≤ 2 * C * a ^ (3 - η) +
        (ENNReal.ofReal (v - u) *
          (L * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ) *
            (ENNReal.ofReal d)⁻¹ ^ 3) * a ^ (3 - η) := by gcongr
    _ = _ := by dsimp only [a]; ring

/-- The finite averaged collision energy asserted in the analytic part of
Theorem 6.27. The geometric residual power bound is an explicit hypothesis;
the direction-density error and zero-distance singularity are proved here. -/
theorem finite_time_pair_energy_of_residual_power
    (σ : Measure E3) [IsFiniteMeasure σ] (L C : ℝ≥0∞)
    (hL : L ≠ ∞) (hC : C ≠ ∞)
    (hσ : σ ≤ L • volume) (b : E3 → E3) (hb : Measurable b)
    (u v d η t : ℝ) (hd : 0 < d) (hη : 0 ≤ η)
    (ht : 0 < t) (htη : t < 3 - η)
    (hres : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
        (fun p => b p.1 - b p.2) (Icc (u - d) (v + d)) ρ ≤
          C * (ENNReal.ofReal ρ) ^ (2 - η)) :
    (∫⁻ z : ℝ × (E3 × E3),
      (ENNReal.ofReal ‖(b z.2.1 - b z.2.2) + z.1 • (z.2.1 - z.2.2)‖) ^ (-t)
      ∂((volume.restrict (Icc u v)).prod (σ.prod σ))) < ∞ := by
  let K : ℝ≥0∞ := 2 * C + ENNReal.ofReal (v - u) *
    (L * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ) *
      (ENNReal.ofReal d)⁻¹ ^ 3
  have hd0 : ENNReal.ofReal d ≠ 0 := by simp [hd.not_ge]
  have hK : K ≠ ∞ := by
    dsimp [K]
    finiteness
  let f : ℝ × (E3 × E3) → ℝ :=
    fun z => ‖(b z.2.1 - b z.2.2) + z.1 • (z.2.1 - z.2.2)‖
  have hf : Measurable f := by dsimp [f]; fun_prop
  apply finite_inverse_energy_of_sublevel_power
    ((volume.restrict (Icc u v)).prod (σ.prod σ)) f hf
    (fun z => norm_nonneg _) K.toReal (3 - η) t ENNReal.toReal_nonneg ht htη
  intro ρ hρ hρone
  have hset : MeasurableSet {z | f z ≤ ρ} :=
    measurableSet_le hf measurable_const
  rw [Measure.prod_apply hset]
  have hbound := averaged_slope_collision_mass_le_power σ L C hσ b hb
    u v d η ρ hd hη hρ hρone.le (hres ρ hρ hρone)
  change (∫⁻ s in Icc u v, (σ.prod σ)
    {p : E3 × E3 | ‖(b p.1 - b p.2) + s • (p.1 - p.2)‖ ≤ ρ}) ≤ _
  calc
    _ ≤ K * ENNReal.ofReal ρ ^ (3 - η) := hbound
    _ = ENNReal.ofReal (K.toReal * ρ ^ (3 - η)) := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hK, ← ENNReal.ofReal_rpow_of_pos hρ]

end StickyKakeya4
