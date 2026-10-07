import Theorems.Thm_StickyKakeya4_native_window_base_cover
import Theorems.Thm_StickyKakeya4_native_literal_grid_euclidean_cover

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable section
namespace NativeWindowOriginalCover
open Classical Finset NativeWindowXYLabels NativeWindowNesting NativeWindowRealInterpolation
open NativeWindowBaseCover NativeLiteralGridEuclideanCover FiniteVoronoiRealADCoarsening

/-- The unchanged base-normal Y union in its actual final time window
satisfies the paper's localized Euclidean occupied-cube AD law. Both
inputs are supplied by source_all_dyadic_windows on the SAME original T. -/
theorem actual_time_window_cover_AD {k l : ℕ} (S : Finset (XY k l))
    {mu K s : ℝ} (hmu : 0 < mu) (R0 D : ℕ) (hR0 : 0 < R0) (hD : 0 < D)
    (z : XY k l) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (H : ADBounds (points S (R0*D) (mu*((R0*D:ℕ):ℝ)) z) (mu*((R0*D:ℕ):ℝ)) K s)
    (Hglobal : ((atPoint S (R0*D) z).card:ℝ) ≤ K*(mu*((R0*D:ℕ):ℝ))^(-s)) :
    EuclideanCoverAD (actualTimeWindow S mu R0 D z) (mu*((R0*D:ℕ):ℝ))
      ((max 1 (l:ℝ))^s*((2:ℝ)^s*K)) s := by
  have HH := base_union_cover_AD S hmu R0 D hR0 hD z hK hs H Hglobal
  simp only [max_self] at HH
  rw [actualTimeWindow_eq S hmu R0 D hR0 z]
  apply euclidean_cover_of_sup_cover _ (by positivity)
    (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) hs) hK) hs HH

end NativeWindowOriginalCover
