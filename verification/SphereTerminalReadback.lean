import Theorems.Thm_StickyKakeya4_sphere_terminal_band

#check StickyKakeya4.SphereTerminalBand.closedBall_le_cubic
#check StickyKakeya4.SphereTerminalBand.product_band_le_cubic
#check StickyKakeya4.SphereTerminalBand.terminal_mass_le_cubic
#check StickyKakeya4.SphereTerminalBand.terminal_mass_le_quadratic
#check StickyKakeya4.SphereTerminalBand.measure_forest_terminal_mass_le_quadratic

#print axioms StickyKakeya4.SphereTerminalBand.closedBall_le_cubic
#print axioms StickyKakeya4.SphereTerminalBand.product_band_le_cubic
#print axioms StickyKakeya4.SphereTerminalBand.terminal_mass_le_cubic
#print axioms StickyKakeya4.SphereTerminalBand.terminal_mass_le_quadratic
#print axioms StickyKakeya4.SphereTerminalBand.measure_forest_terminal_mass_le_quadratic

-- The source hypothesis is discharged for an actual canonical restriction;
-- no normalization of this piece is introduced.
open StickyKakeya4 MeasureTheory Set in
example (directions : Set {theta : E4 // ‖theta‖ = 1})
    {T : ℝ} (hT : 0 < T) (hTsmall : 3 * T ≤ 1) :
    let σ := (normSphereProbability :
      Measure {theta : E4 // ‖theta‖ = 1}).restrict directions
    (σ.prod σ) (GlobalTerminalBand.directionBand id (2 * T)) ≤
      27 * metricSphereCapConstant * σ univ * ENNReal.ofReal T ^ 3 := by
  dsimp only
  exact SphereTerminalBand.product_band_le_cubic _ Measure.restrict_le_self hT hTsmall
