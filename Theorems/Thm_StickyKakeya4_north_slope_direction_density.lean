import Theorems.Thm_StickyKakeya4_actual_slope_source
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open Filter MeasureTheory Set Metric
open scoped ENNReal Topology

namespace StickyKakeya4.ActualSlopeSource

/-!
A cubic direction-marginal upper bound for an actual bounded-density slope
source.  A quantitative inverse estimate for the north-slope chart on the
closed unit slope ball reduces each direction cap to one ordinary Euclidean
slope ball.  No spherical Jacobian formula or additional density hypothesis
for the direction marginal is used.
-/

/-- The affine lift of a slope in the closed unit ball has norm at most two. -/
theorem northSlopeLift_norm_le_two {a : E3} (ha : ‖a‖ ≤ 1) :
    ‖northSlopeLift a‖ ≤ 2 := by
  have htriangle := norm_add_le (northSlopeLift a - northSlopeLift 0) (northSlopeLift 0)
  rw [sub_add_cancel, northSlopeLift_sub_norm, sub_zero, northSlopeLift_zero_norm]
    at htriangle
  linarith

/-- The north direction retains fourth coordinate at least one half on the
closed unit slope ball, including its boundary. -/
theorem northSlopeDirection_fourth_ge_half_of_norm_le_one
    {a : E3} (ha : ‖a‖ ≤ 1) :
    (1 / 2 : ℝ) ≤ (northSlopeDirection a : E4) (3 : Fin 4) := by
  have hnpos : 0 < ‖northSlopeLift a‖ :=
    zero_lt_one.trans_le (northSlopeLift_norm_ge_one a)
  rw [northSlopeDirection_fourth, inv_eq_one_div]
  exact (le_div_iff₀ hnpos).2 (by linarith [northSlopeLift_norm_le_two ha])

/-- On the closed unit slope ball, the north direction chart has inverse
Lipschitz constant six.  The proof uses only the fourth coordinate and the
norm-one property of the normalized directions. -/
theorem northSlopeDirection_inverse_dist_le_six_mul
    {a b : E3} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    dist a b ≤ 6 * dist (northSlopeDirection a : E4) (northSlopeDirection b : E4) := by
  let na : ℝ := ‖northSlopeLift a‖
  let nb : ℝ := ‖northSlopeLift b‖
  let u : E4 := northSlopeDirection a
  let v : E4 := northSlopeDirection b
  have hna : 0 < na := zero_lt_one.trans_le (northSlopeLift_norm_ge_one a)
  have hnb : 0 < nb := zero_lt_one.trans_le (northSlopeLift_norm_ge_one b)
  have hnaTwo : na ≤ 2 := northSlopeLift_norm_le_two ha
  have hnbTwo : nb ≤ 2 := northSlopeLift_norm_le_two hb
  have huvCoord : |na⁻¹ - nb⁻¹| ≤ dist u v := by
    have hcoord := PiLp.norm_apply_le (u - v) (3 : Fin 4)
    simpa only [u, v, PiLp.sub_apply, Real.norm_eq_abs,
      northSlopeDirection_fourth, dist_eq_norm, na, nb] using hcoord
  have hprod : na * nb ≤ 4 := by nlinarith
  have hscaled : (na * nb) * (na⁻¹ - nb⁻¹) = nb - na := by
    field_simp
  have hnormDiff : |na - nb| ≤ 4 * dist u v := by
    calc
      |na - nb| = |(na * nb) * (na⁻¹ - nb⁻¹)| := by rw [hscaled, abs_sub_comm]
      _ = (na * nb) * |na⁻¹ - nb⁻¹| := by
        rw [abs_mul, abs_of_nonneg (mul_nonneg hna.le hnb.le)]
      _ ≤ 4 * dist u v := mul_le_mul hprod huvCoord (abs_nonneg _) (by norm_num)
  have hnaLift : na • u = northSlopeLift a := NormedSpace.norm_smul_normalize _
  have hnbLift : nb • v = northSlopeLift b := NormedSpace.norm_smul_normalize _
  have hdecomposition : northSlopeLift a - northSlopeLift b =
      na • (u - v) + (na - nb) • v := by
    rw [smul_sub, sub_smul]
    rw [hnaLift, hnbLift]
    abel
  have hvnorm : ‖v‖ = 1 := (northSlopeDirection b).property
  calc
    dist a b = ‖northSlopeLift a - northSlopeLift b‖ := by
      rw [northSlopeLift_sub_norm, dist_eq_norm]
    _ ≤ ‖na • (u - v)‖ + ‖(na - nb) • v‖ := by
      rw [hdecomposition]
      exact norm_add_le _ _
    _ = na * dist u v + |na - nb| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hna, hvnorm, mul_one, ← dist_eq_norm]
    _ ≤ 2 * dist u v + 4 * dist u v :=
      add_le_add (mul_le_mul_of_nonneg_right hnaTwo dist_nonneg) hnormDiff
    _ = 6 * dist u v := by ring

/-- Every direction cap pulls back, on the closed unit slope ball, into one
slope ball of radius `12 * r` whenever the pullback is nonempty. -/
theorem northSlopeDirection_cap_preimage_subset_ball
    (theta : E4) (r : ℝ) (a₀ : E3) (ha₀ : ‖a₀‖ ≤ 1)
    (ha₀cap : (northSlopeDirection a₀ : E4) ∈ Metric.ball theta r) :
    {a : E3 | ‖a‖ ≤ 1} ∩
      (fun a : E3 => (northSlopeDirection a : E4)) ⁻¹' Metric.ball theta r ⊆
        Metric.ball a₀ (12 * r) := by
  intro a ha
  have haDist : dist (northSlopeDirection a : E4) theta < r := ha.2
  have ha₀Dist : dist theta (northSlopeDirection a₀ : E4) < r := by
    simpa only [Metric.mem_ball, dist_comm] using ha₀cap
  have hcapDist : dist (northSlopeDirection a : E4) (northSlopeDirection a₀ : E4) <
      2 * r := by
    calc
      dist (northSlopeDirection a : E4) (northSlopeDirection a₀ : E4) ≤
          dist (northSlopeDirection a : E4) theta +
            dist theta (northSlopeDirection a₀ : E4) := dist_triangle _ _ _
      _ < r + r := add_lt_add haDist ha₀Dist
      _ = 2 * r := by ring
  have hinverse := northSlopeDirection_inverse_dist_le_six_mul ha.1 ha₀
  change dist a a₀ < 12 * r
  linarith

/-- A slope measure dominated by ordinary three-dimensional volume and
supported almost everywhere on the closed unit slope ball has a cubic north-
direction marginal bound with an explicit finite, source-independent constant. -/
theorem northSlopeDirection_map_ball_le_cubic
    (σ : Measure E3) (hσ : σ ≤ volume)
    (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1) (theta : E4) (r : ℝ) :
    σ.map (fun a : E3 => (northSlopeDirection a : E4)) (Metric.ball theta r) ≤
      (ENNReal.ofReal (Real.pi * 4 / 3) * (12 : ENNReal) ^ (3 : ℕ)) *
        (ENNReal.ofReal r) ^ (3 : ℕ) := by
  classical
  let S : Set E3 := {a : E3 | ‖a‖ ≤ 1} ∩
    (fun a : E3 => (northSlopeDirection a : E4)) ⁻¹' Metric.ball theta r
  have hmeas : Measurable fun a : E3 => (northSlopeDirection a : E4) :=
    measurable_subtype_coe.comp measurable_northSlopeDirection
  rw [Measure.map_apply hmeas measurableSet_ball]
  have hSmeasure : σ S =
      σ ((fun a : E3 => (northSlopeDirection a : E4)) ⁻¹' Metric.ball theta r) :=
    Measure.measure_inter_eq_of_ae hslopes
  rw [← hSmeasure]
  by_cases hS : S.Nonempty
  · obtain ⟨a₀, ha₀⟩ := hS
    have hsubset : S ⊆ Metric.ball a₀ (12 * r) :=
      northSlopeDirection_cap_preimage_subset_ball theta r a₀ ha₀.1 ha₀.2
    calc
      σ S ≤ σ (Metric.ball a₀ (12 * r)) := measure_mono hsubset
      _ ≤ volume (Metric.ball a₀ (12 * r)) := hσ _
      _ = (ENNReal.ofReal (Real.pi * 4 / 3) * (12 : ENNReal) ^ (3 : ℕ)) *
          (ENNReal.ofReal r) ^ (3 : ℕ) := by
        rw [EuclideanSpace.volume_ball_fin_three,
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ 12 by norm_num), mul_pow]
        norm_num
        ac_rfl
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, measure_empty]
    positivity

/-- The cubic coefficient for the actual north-slope direction marginal is
finite.  This is the direct interface for the reference-net vertical count. -/
theorem exists_northSlopeDirection_cubic_density
    (σ : Measure E3) (hσ : σ ≤ volume)
    (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1) :
    ∃ D : ENNReal, D ≠ ⊤ ∧ ∀ (theta : E4) (r : ℝ), 0 < r →
      σ.map (fun a : E3 => (northSlopeDirection a : E4)) (Metric.ball theta r) ≤
        D * (ENNReal.ofReal r) ^ (3 : ℕ) := by
  refine ⟨ENNReal.ofReal (Real.pi * 4 / 3) * (12 : ENNReal) ^ (3 : ℕ), ?_, ?_⟩
  · finiteness
  · intro theta r _hr
    exact northSlopeDirection_map_ball_le_cubic σ hσ hslopes theta r

end StickyKakeya4.ActualSlopeSource
