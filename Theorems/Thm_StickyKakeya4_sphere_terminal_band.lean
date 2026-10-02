import Theorems.Thm_StickyKakeya4_canonical_sphere_measure
import Theorems.Thm_StickyKakeya4_measure_edge_flow

/-!
# Terminal occurrence bounds for the canonical sphere source

The original direction source is the norm-one sphere, with a measure dominated
by its canonical surface probability. This includes restrictions to positive
selector pieces and fractional submeasures, without renormalizing their mass.
The only density estimate used is the proved canonical open-cap estimate at
positive radii at most one. At a positive terminal scale `T` with `3 * T ≤ 1`,
a closed distance band of width `2 * T` has sections inside open caps of radius
`3 * T`. Thus there is no all-radius or zero-radius density hypothesis.

This supplies the source-measure specialization of the global terminal ledger.
Constructing a conservative occurrence forest, proving root product domination,
and establishing terminal band support remain genuine geometric obligations.
No per-terminal marginal-product inequality or final sticky Kakeya theorem is
asserted here.
-/

open MeasureTheory Set
open scoped ENNReal

namespace StickyKakeya4.SphereTerminalBand

/-- A submeasure of canonical surface probability has the needed closed-cap
bound at the terminal scale. The open-cap theorem is applied at `3 * T`, so
no assertion about closed radius-zero caps is required. -/
theorem closedBall_le_cubic
    (σ : Measure {theta : E4 // ‖theta‖ = 1})
    (hσ : σ ≤ (normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1}))
    (theta : {theta : E4 // ‖theta‖ = 1}) {T : ℝ}
    (hT : 0 < T) (hTsmall : 3 * T ≤ 1) :
    σ (Metric.closedBall theta (2 * T)) ≤
      27 * metricSphereCapConstant * ENNReal.ofReal T ^ 3 := by
  have hcap : Metric.closedBall theta (2 * T) ⊆ Metric.ball theta (3 * T) := by
    intro phi hphi
    rw [Metric.mem_closedBall] at hphi
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hphi (by linarith)
  calc
    σ (Metric.closedBall theta (2 * T)) ≤
        σ (Metric.ball theta (3 * T)) := measure_mono hcap
    _ ≤ (normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1})
        (Metric.ball theta (3 * T)) := hσ _
    _ ≤ metricSphereCapConstant * ENNReal.ofReal (3 * T) ^ 3 :=
      normSphereProbability_ball_upper_bound theta (by positivity) hTsmall
    _ = 27 * metricSphereCapConstant * ENNReal.ofReal T ^ 3 := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), mul_pow]
      norm_num
      ring

/-- The product direction-band bound with the actual canonical sphere density.
The factor `σ univ` is the mass of the original, possibly restricted source. -/
theorem product_band_le_cubic
    (σ : Measure {theta : E4 // ‖theta‖ = 1}) [SFinite σ]
    (hσ : σ ≤ (normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1}))
    {T : ℝ} (hT : 0 < T) (hTsmall : 3 * T ≤ 1) :
    (σ.prod σ) (GlobalTerminalBand.directionBand id (2 * T)) ≤
      27 * metricSphereCapConstant * σ univ * ENNReal.ofReal T ^ 3 := by
  calc
    (σ.prod σ) (GlobalTerminalBand.directionBand id (2 * T)) ≤
        (27 * metricSphereCapConstant * ENNReal.ofReal T ^ 3) * σ univ := by
      apply GlobalTerminalBand.product_band_le_of_ball_bound σ measurable_id
      intro theta
      simpa only [Set.preimage_id] using closedBall_le_cubic σ hσ theta hT hTsmall
    _ = 27 * metricSphereCapConstant * σ univ * ENNReal.ofReal T ^ 3 := by ring

/-- The global terminal cubic estimate for a canonical sphere submeasure. -/
theorem terminal_mass_le_cubic
    {I : Type*}
    (σ : Measure {theta : E4 // ‖theta‖ = 1}) [SFinite σ]
    (hσ : σ ≤ (normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1}))
    (root : Measure ({theta : E4 // ‖theta‖ = 1} × {theta : E4 // ‖theta‖ = 1}))
    (terminal : I → Measure
      ({theta : E4 // ‖theta‖ = 1} × {theta : E4 // ‖theta‖ = 1}))
    {T : ℝ} (hT : 0 < T) (hTsmall : 3 * T ≤ 1)
    (hbudget : Measure.sum terminal ≤ root)
    (hroot : root ≤ σ.prod σ)
    (hsupport : ∀ i, terminal i
      (GlobalTerminalBand.directionBand id (2 * T))ᶜ = 0) :
    (∑' i, terminal i univ) ≤
      27 * metricSphereCapConstant * σ univ * ENNReal.ofReal T ^ 3 := by
  exact (GlobalTerminalBand.terminal_mass_le_product_band σ root terminal
    measurable_id (2 * T) hbudget hroot hsupport).trans
      (product_band_le_cubic σ hσ hT hTsmall)

/-- At a stopping scale `T^3 ≤ m q`, the bound is quadratic in the mass `m`
of the unnormalized original sphere source. -/
theorem terminal_mass_le_quadratic
    {I : Type*}
    (σ : Measure {theta : E4 // ‖theta‖ = 1}) [SFinite σ]
    (hσ : σ ≤ (normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1}))
    (root : Measure ({theta : E4 // ‖theta‖ = 1} × {theta : E4 // ‖theta‖ = 1}))
    (terminal : I → Measure
      ({theta : E4 // ‖theta‖ = 1} × {theta : E4 // ‖theta‖ = 1}))
    (q : ℝ≥0∞) {T : ℝ} (hT : 0 < T) (hTsmall : 3 * T ≤ 1)
    (hbudget : Measure.sum terminal ≤ root)
    (hroot : root ≤ σ.prod σ)
    (hsupport : ∀ i, terminal i
      (GlobalTerminalBand.directionBand id (2 * T))ᶜ = 0)
    (hscale : ENNReal.ofReal T ^ 3 ≤ σ univ * q) :
    (∑' i, terminal i univ) ≤ 27 * metricSphereCapConstant * (σ univ) ^ 2 * q := by
  calc
    (∑' i, terminal i univ) ≤
        27 * metricSphereCapConstant * σ univ * ENNReal.ofReal T ^ 3 :=
      terminal_mass_le_cubic σ hσ root terminal hT hTsmall hbudget hroot hsupport
    _ ≤ 27 * metricSphereCapConstant * σ univ * (σ univ * q) :=
      mul_le_mul_right hscale _
    _ = 27 * metricSphereCapConstant * (σ univ) ^ 2 * q := by ring

/-- The sphere-source estimate for a finite conservative occurrence forest.
The fixed endpoint map keeps the original ordered direction pair. The
measure-valued terminal budget is derived from conservation, while source
density is supplied by canonical surface measure rather than hypothesized. -/
theorem measure_forest_terminal_mass_le_quadratic
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (tree : NestedCarrierTree n)
    (incoming paid terminal : Fin n → Measure Ω)
    (hconserve : ∀ i,
      incoming i = paid i + terminal i +
        Finset.univ.sum (fun j : Fin n =>
          if tree.parent j = some i then incoming j else 0))
    (endpoint : Ω → {theta : E4 // ‖theta‖ = 1} × {theta : E4 // ‖theta‖ = 1})
    (hendpoint : Measurable endpoint)
    (σ : Measure {theta : E4 // ‖theta‖ = 1}) [SFinite σ]
    (hσ : σ ≤ (normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1}))
    (q : ℝ≥0∞) {T : ℝ} (hT : 0 < T) (hTsmall : 3 * T ≤ 1)
    (hroot : (Finset.univ.sum (fun i : Fin n =>
      if tree.parent i = none then incoming i else 0)).map endpoint ≤ σ.prod σ)
    (hsupport : ∀ i, (terminal i).map endpoint
      (GlobalTerminalBand.directionBand id (2 * T))ᶜ = 0)
    (hscale : ENNReal.ofReal T ^ 3 ≤ σ univ * q) :
    Finset.univ.sum (fun i : Fin n => terminal i univ) ≤
      27 * metricSphereCapConstant * (σ univ) ^ 2 * q := by
  classical
  have hbudget : Measure.sum (fun i : Fin n => (terminal i).map endpoint) ≤
      (Finset.univ.sum (fun i : Fin n =>
        if tree.parent i = none then incoming i else 0)).map endpoint := by
    rw [Measure.sum_fintype]
    exact measure_terminal_flow_map_le_root tree incoming paid terminal hconserve
      endpoint hendpoint
  have hbound := terminal_mass_le_quadratic σ hσ
    ((Finset.univ.sum (fun i : Fin n =>
      if tree.parent i = none then incoming i else 0)).map endpoint)
    (fun i : Fin n => (terminal i).map endpoint)
    q hT hTsmall hbudget hroot hsupport hscale
  simpa only [tsum_fintype, Measure.map_apply hendpoint MeasurableSet.univ,
    Set.preimage_univ] using hbound

end StickyKakeya4.SphereTerminalBand
