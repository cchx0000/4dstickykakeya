import Theorems.Thm_StickyKakeya4_actual_scalar_ad_profiles

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace FullNormalizedScalarAD

open NativeDyadicTubeStopping ShearedGridADReference SmallFiberAlignment FractionalFiberAlignment
open NativeFractionalReferenceComposition LiteralAffineFiberCoordinates ActualScalarADProfiles
open DyadicAlignmentParameters DyadicADInterpolation RealScalarADInterpolation

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Actual fiber ball bounds through every normalized radius up to one.
The top fiber ball is identified from the true longitudinal label span. -/
theorem fiber_normalized_AD (P : Finset Vertex) (M H Q J : ℕ) (hH : 0 < H)
    (t s dens Bad Bcolumn Btube μ L : ℝ) (c : Plane) (hμ : 0 < μ) (hL : 0 < L)
    (hs : 0 ≤ s) (hdens : 0 ≤ dens) (hBtube : 0 ≤ Btube)
    (hC : 0 < comparisonCost (H + 1) J Q * Bcolumn * Btube)
    (hcounts : RefinedCounts P (workingRadii M H) (2 ^ M) Q J t s dens Bad Bcolumn Btube)
    (hspan : ∀ k ∈ P, ∀ l ∈ P, |k.1 - l.1| ≤ (2 ^ M : ℕ))
    (hscale : (μ / L) * (2 : ℝ) ^ M = 1 / 64)
    {p : Vertex} (hp : p ∈ P) {r : ℝ} (hrlo : μ / L ≤ r) (hrhi : r ≤ 1) :
    (dens / (comparisonCost (H + 1) J Q * Bcolumn * Btube)) * (r / (μ / L)) ^ s ≤
        fullInterpolationLoss M H s * ballCount (fiberCoordinates P μ L c p.2) (timeCoord μ (c 0) L p.1) r ∧
      ballCount (fiberCoordinates P μ L c p.2) (timeCoord μ (c 0) L p.1) r ≤
        fullInterpolationLoss M H s * Btube * (r / (μ / L)) ^ s := by
  have hw : ∀ j ≤ H,
      (dens / (comparisonCost (H + 1) J Q * Bcolumn * Btube)) * ((2 : ℝ) ^ level M H j) ^ s ≤
        ballCount (fiberCoordinates P μ L c p.2) (timeCoord μ (c 0) L p.1) (scale (μ / L) (level M H j)) ∧
      ballCount (fiberCoordinates P μ L c p.2) (timeCoord μ (c 0) L p.1) (scale (μ / L) (level M H j)) ≤
        Btube * ((2 : ℝ) ^ level M H j) ^ s := by
    intro j hj
    let jj : Fin (H + 1) := ⟨j, by omega⟩
    have h := (hcounts p hp).2 jj
    have hradius : scale (μ / L) (level M H j) = (μ / L) * (workingRadii M H jj : ℝ) := by
      simp only [scale, workingRadii, jj, Nat.cast_pow, Nat.cast_ofNat]
    rw [hradius, fiber_ballCount_eq P μ L c hμ hL p]
    constructor
    · rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hC).mpr
      simpa only [workingRadii, jj, Nat.cast_pow, Nat.cast_ofNat, mul_comm] using h.2.2.1
    · simpa only [workingRadii, jj, Nat.cast_pow, Nat.cast_ofNat] using h.2.2.2.1
  have hglobal : ((fiberCoordinates P μ L c p.2).card : ℝ) ≤ Btube * ((2 : ℝ) ^ M) ^ s := by
    have hh := (hcounts p hp).2 ⟨H, by omega⟩
    have h := hh.2.2.2.1
    simp only [workingRadii, level_endpoint M H hH] at h
    rw [fiberBall_top_eq P (2 ^ M) hspan hp] at h
    rw [fiberCoordinates_card P μ L c p.2 hμ hL]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  have h := normalized_full_ball_interpolation _ _ M H hH (div_pos hμ hL) hs
    (div_nonneg hdens hC.le) hBtube hBtube hw hglobal hscale hrlo hrhi
  simpa only [max_self] using h

/-- Actual quotient ball bounds through every normalized radius up to one.
Its large-radius upper bound comes from summing full fibers and the derived
global vertex count, rather than assuming the radius-N normal ball is full. -/
theorem quotient_normalized_AD (P : Finset Vertex) (M H Q J : ℕ) (hH : 0 < H)
    (t s dens Bad Bcolumn Btube μ angle L : ℝ) (c : Plane) (hμ : 0 < μ) (hL : 0 < L)
    (hst : s ≤ t) (hdens : 0 < dens) (hBad : 0 ≤ Bad) (hBcolumn : 0 ≤ Bcolumn)
    (hClow : 0 < comparisonCost (H + 1) J Q * Bad * Btube)
    (hCup : 0 ≤ comparisonCost (H + 1) J Q * Bcolumn * Bad * Btube)
    (hcounts : RefinedCounts P (workingRadii M H) (2 ^ M) Q J t s dens Bad Bcolumn Btube)
    (hvertices : (P.card : ℝ) ≤ Bad * ((2 : ℝ) ^ M) ^ t)
    (hscale : (μ / L) * (2 : ℝ) ^ M = 1 / 64)
    {p : Vertex} (hp : p ∈ P) {r : ℝ} (hrlo : μ / L ≤ r) (hrhi : r ≤ 1) :
    (dens / (comparisonCost (H + 1) J Q * Bad * Btube)) * (r / (μ / L)) ^ (t - s) ≤
        fullInterpolationLoss M H (t - s) *
          ballCount (quotientCoordinates P μ angle L c) (normalCoord μ angle L c p.2) r ∧
      ballCount (quotientCoordinates P μ angle L c) (normalCoord μ angle L c p.2) r ≤
        fullInterpolationLoss M H (t - s) *
          max ((comparisonCost (H + 1) J Q * Bcolumn * Bad * Btube) / dens)
            ((comparisonCost (H + 1) J Q * Bcolumn * Bad) / dens) * (r / (μ / L)) ^ (t - s) := by
  have hw : ∀ j ≤ H,
      (dens / (comparisonCost (H + 1) J Q * Bad * Btube)) * ((2 : ℝ) ^ level M H j) ^ (t - s) ≤
        ballCount (quotientCoordinates P μ angle L c) (normalCoord μ angle L c p.2) (scale (μ / L) (level M H j)) ∧
      ballCount (quotientCoordinates P μ angle L c) (normalCoord μ angle L c p.2) (scale (μ / L) (level M H j)) ≤
        ((comparisonCost (H + 1) J Q * Bcolumn * Bad * Btube) / dens) * ((2 : ℝ) ^ level M H j) ^ (t - s) := by
    intro j hj
    let jj : Fin (H + 1) := ⟨j, by omega⟩
    have h := (hcounts p hp).2 jj
    have hradius : scale (μ / L) (level M H j) = (μ / L) * (workingRadii M H jj : ℝ) := by
      simp only [scale, workingRadii, jj, Nat.cast_pow, Nat.cast_ofNat]
    rw [hradius, quotient_ballCount_eq P μ angle L c hμ hL p.2]
    constructor
    · rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hClow).mpr
      simpa only [workingRadii, jj, Nat.cast_pow, Nat.cast_ofNat, mul_comm] using h.2.2.2.2.1
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hdens).mpr
      simpa only [workingRadii, jj, Nat.cast_pow, Nat.cast_ofNat, mul_comm] using h.2.2.2.2.2
  have hcost : 0 ≤ comparisonCost (H + 1) J Q := by unfold comparisonCost; positivity
  have hC : 0 ≤ comparisonCost (H + 1) J Q * Bcolumn := mul_nonneg hcost hBcolumn
  have hglobal : ((quotientCoordinates P μ angle L c).card : ℝ) ≤
      ((comparisonCost (H + 1) J Q * Bcolumn * Bad) / dens) * ((2 : ℝ) ^ M) ^ (t - s) := by
    have hh := global_quotient_from_fibers P (show 0 < (2 : ℕ) ^ M by positivity)
      s t dens (comparisonCost (H + 1) J Q * Bcolumn) Bad hC
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hvertices) (fun q hq => (hcounts q hq).1)
    rw [quotientCoordinates_card P μ angle L c hμ hL, div_mul_eq_mul_div]
    apply (le_div_iff₀ hdens).mpr
    simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_comm] using hh
  exact normalized_full_ball_interpolation _ _ M H hH (div_pos hμ hL) (sub_nonneg.mpr hst)
    (div_nonneg hdens.le hClow.le) (div_nonneg hCup hdens.le)
    (div_nonneg (mul_nonneg hC hBad) hdens.le) hw hglobal hscale hrlo hrhi

end
end FullNormalizedScalarAD
