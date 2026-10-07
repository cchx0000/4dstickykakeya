import Theorems.Thm_StickyKakeya4_canonical_grid_recoding

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeConfiguredTimeCoarsening

/-- The literal coarse-height center after the second physical contraction. -/
def finalTime (delta : ℝ) (height : ℤ) : ℝ :=
  (delta / 512) * ((height : ℝ) + 1 / 2)

/-- Natural coarsening of actual midpoint centers preserves the exact
integer quotient, including all negative height indices. -/
theorem floor_finalTime (delta : ℝ) (hdelta : 0 < delta) (J : ℕ) (height : ℤ) :
    ⌊finalTime delta height / ((delta / 512) * (J : ℝ))⌋ = height / (J : ℤ) := by
  have hbase : delta / 512 ≠ 0 := ne_of_gt (div_pos hdelta (by norm_num))
  have heq : finalTime delta height / ((delta / 512) * (J : ℝ)) =
      ((height : ℝ) + 1 / 2) / (J : ℝ) := mul_div_mul_left _ _ hbase
  rw [heq, Int.floor_div_natCast, Int.floor_intCast_add]
  norm_num

/-- Exact first-to-second time-window readback. The explicit factor512
changes the physical window width; it is not removed by an isometry. -/
theorem floor_from_original (delta rho time : ℝ) (hdelta : 0 < delta) (J : ℕ)
    (hscale : 512 * rho = delta * (J : ℝ)) :
    ⌊finalTime delta ⌊time / delta⌋ / rho⌋ = ⌊time / (512 * rho)⌋ := by
  have hrho : rho = (delta / 512) * (J : ℝ) := by nlinarith only [hscale]
  calc
    _ = ⌊finalTime delta ⌊time / delta⌋ / ((delta / 512) * (J : ℝ))⌋ := by rw [hrho]
    _ = ⌊time / delta⌋ / (J : ℤ) := floor_finalTime delta hdelta J _
    _ = ⌊time / (delta * (J : ℝ))⌋ := by
      rw [← Int.floor_div_natCast]
      congr 1
      ring
    _ = _ := by rw [hscale]

theorem same_final_window_iff (delta rho time time' : ℝ) (hdelta : 0 < delta) (J : ℕ)
    (hscale : 512 * rho = delta * (J : ℝ)) :
    ⌊finalTime delta ⌊time / delta⌋ / rho⌋ = ⌊finalTime delta ⌊time' / delta⌋ / rho⌋ ↔
      ⌊time / (512 * rho)⌋ = ⌊time' / (512 * rho)⌋ := by
  rw [floor_from_original delta rho time hdelta J hscale,
    floor_from_original delta rho time' hdelta J hscale]

end NativeConfiguredTimeCoarsening
