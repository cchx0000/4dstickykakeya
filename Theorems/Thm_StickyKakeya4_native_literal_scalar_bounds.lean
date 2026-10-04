import Theorems.Thm_StickyKakeya4_native_normalized_parent_output

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

namespace NativeLiteralScalarBounds

open NativeNormalizedParentOutput NativeDyadicTubeStopping ShearedGridADReference SmallFiberAlignment FractionalFiberAlignment
open LiteralAffineFiberCoordinates ActualScalarADProfiles RealScalarADInterpolation

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The vertex-indexed estimates give AD at every actual real point of every
literal scalar graph fiber. This is only an exact coordinate conversion. -/
theorem AllRealBounds.scalar_fibers {P : Finset Vertex} {M H Q L : ℕ}
    {μ angle b t s dens Bad Bcolumn Btube Htube : ℝ} {c : Plane}
    (B : AllRealBounds P M H Q L μ angle b t s dens Bad Bcolumn Btube Htube c)
    (hμ : 0 < μ) (hb : 0 < b) {y x r : ℝ}
    (hx : x ∈ fiberAt P μ angle (64 * b) c y)
    (hrlo : 64 * (μ / (64 * b)) ≤ r) (hrhi : r ≤ 1) :
    (dens / (comparisonCost (H + 1) L Q * Bcolumn * Btube)) * (r / (μ / (64 * b))) ^ s ≤
      fullInterpolationLoss M H s * ballCount (fiberAt P μ angle (64 * b) c y) x r ∧
    ballCount (fiberAt P μ angle (64 * b) c y) x r ≤
      fullInterpolationLoss M H s * Btube * (r / (μ / (64 * b))) ^ s := by
  obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hx
  obtain ⟨hkP, hky⟩ := Finset.mem_filter.mp hk
  have h := B.fibers k hkP r hrlo hrhi
  have hL : 0 < 64 * b := by positivity
  have he := fiberAt_normalCoord P μ angle (64 * b) c hμ hL k.2
  rw [hky] at he
  rw [← he, hkx] at h
  exact h

/-- Every real normal label has an actual vertex witness, so the quotient
estimate holds at all points of the literal scalar Y. -/
theorem AllRealBounds.scalar_quotient {P : Finset Vertex} {M H Q L : ℕ}
    {μ angle b t s dens Bad Bcolumn Btube Htube : ℝ} {c : Plane}
    (B : AllRealBounds P M H Q L μ angle b t s dens Bad Bcolumn Btube Htube c)
    {y r : ℝ} (hy : y ∈ quotientCoordinates P μ angle (64 * b) c)
    (hrlo : 64 * (μ / (64 * b)) ≤ r) (hrhi : r ≤ 1) :
    (dens / (comparisonCost (H + 1) L Q * Bad * Btube)) * (r / (μ / (64 * b))) ^ (t - s) ≤
      fullInterpolationLoss M H (t - s) * ballCount (quotientCoordinates P μ angle (64 * b) c) y r ∧
    ballCount (quotientCoordinates P μ angle (64 * b) c) y r ≤
      fullInterpolationLoss M H (t - s) *
        max ((comparisonCost (H + 1) L Q * Bcolumn * Bad * Btube) / dens)
          ((comparisonCost (H + 1) L Q * Bcolumn * Bad) / dens) * (r / (μ / (64 * b))) ^ (t - s) := by
  obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
  obtain ⟨k, hk, hkz⟩ := Finset.mem_image.mp hz
  have h := B.quotient k hk r hrlo hrhi
  rwa [hkz, hzy] at h

end
end NativeLiteralScalarBounds
