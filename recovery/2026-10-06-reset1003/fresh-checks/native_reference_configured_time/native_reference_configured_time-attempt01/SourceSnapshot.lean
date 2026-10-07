import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_points
import Theorems.Thm_StickyKakeya4_canonical_configured_point_rounding
import Theorems.Thm_StickyKakeya4_native_configured_time_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeReferenceConfiguredTime
open StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeReferenceXYGridPoints
open NativeTranslatedGrainHeightOverlap NativeAnisotropicShortRowGeometry

/-- Time is not multiplied by the first-parent anisotropic dilation.
The raw/old time error therefore has the sharper phase-scale bound. -/
theorem raw_old_time_error {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (p : Parent) (k : Index) :
    |rawPoint D a m p k (3 : Fin 4) - oldPoint D a m p k (3 : Fin 4)| ≤ sigma m / 256 := by
  have hcoord : |NativeOriginalPacketReference.rawVertex D (NativeSquaredGrainQueries.phaseDepth m) k (3 : Fin 4) -
      cellCenter (mesh D) k (3 : Fin 4)| ≤ 2 * sigma m := by
    have hh := PiLp.dist_apply_le
      (NativeOriginalPacketReference.rawVertex D (NativeSquaredGrainQueries.phaseDepth m) k)
      (cellCenter (mesh D) k) (3 : Fin 4)
    have hc : |NativeOriginalPacketReference.rawVertex D (NativeSquaredGrainQueries.phaseDepth m) k (3 : Fin 4) -
        cellCenter (mesh D) k (3 : Fin 4)| ≤
        dist (NativeOriginalPacketReference.rawVertex D (NativeSquaredGrainQueries.phaseDepth m) k)
          (cellCenter (mesh D) k) := by
      simpa only [Real.dist_eq] using hh
    exact hc.trans (original_phase_rounding D m k)
  unfold rawPoint oldPoint
  rw [chart_height_sub, abs_div]
  norm_num only [abs_ofNat]
  linarith only [hcoord]

/-- The literal pxy coarse height is exactly the coarse physical bin of
the original microcell center's time, including negative height labels. -/
theorem coarse_height_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (p : Parent) (R : ℕ) (k : Index) :
    translatedHeight D a m k / ((8 * R : ℕ) : ℤ) =
      ⌊oldPoint D a m p k (3 : Fin 4) / (mu m * (R : ℝ))⌋ := by
  rw [← pref_height D a m p k, pref_height_floor, floor_div_scale, heightMesh_eq]
  congr 1
  push_cast
  ring

/-- The actual configured height keeps the old reference label, and its
distance from rawPoint time is bounded without identifying those times. -/
theorem coarse_height_error {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (p : Parent) (R : ℕ) (hR : 0 < R) (k : Index) :
    |(mu m * (R : ℝ)) *
        (((translatedHeight D a m k / ((8 * R : ℕ) : ℤ) : ℤ) : ℝ) + 1 / 2) -
      rawPoint D a m p k (3 : Fin 4)| ≤ (mu m * (R : ℝ)) / 2 + sigma m / 256 := by
  rw [coarse_height_readback D a m p R k]
  have hbase : 0 < mu m * (R : ℝ) := mul_pos (mu_pos m) (by exact_mod_cast hR)
  have hmid := CanonicalConfiguredPointRounding.midpoint_error
    (mu m * (R : ℝ)) (oldPoint D a m p k (3 : Fin 4)) hbase
  have htime : |oldPoint D a m p k (3 : Fin 4) - rawPoint D a m p k (3 : Fin 4)| ≤ sigma m / 256 := by
    simpa only [abs_sub_comm] using raw_old_time_error D a m p k
  exact (abs_sub_le _ (oldPoint D a m p k (3 : Fin 4)) _).trans (add_le_add hmid htime)

/-- At the actual configured scale above rho, the corrected height fits
the same 3/2 coordinate budget as the spatial recoding coordinates. -/
theorem coarse_height_coordinate_budget {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (hm : 6 ≤ m) (p : Parent) (R : ℕ) (hR : 0 < R) (k : Index)
    (hcfg : rho m ≤ mu m * (R : ℝ)) :
    |(mu m * (R : ℝ)) *
        (((translatedHeight D a m k / ((8 * R : ℕ) : ℤ) : ℤ) : ℝ) + 1 / 2) -
      rawPoint D a m p k (3 : Fin 4)| ≤ (3 / 2 : ℝ) * (mu m * (R : ℝ)) := by
  have hN : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
  have h64 : (64 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hm
    norm_num at hh
    exact_mod_cast hh
  have hrho : rho m ≤ 1 := (div_le_one hN).mpr h64
  have hsquare : sigma m = (rho m) ^ 2 := NativeSquaredGrainQueries.squared_scale_identity m hm
  have hsigma : sigma m ≤ rho m := by
    rw [hsquare]
    nlinarith [rho_pos m]
  have hbase : 0 < mu m * (R : ℝ) := mul_pos (mu_pos m) (by exact_mod_cast hR)
  exact (coarse_height_error D a m p R hR k).trans (by linarith only [hsigma, hcfg, hbase])

/-- The actual translated pxy height gives the exact old physical time
window after configuration and the second contraction. -/
theorem final_height_floor {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (p : Parent) (R : ℕ) (hR : 0 < R) (k : Index) (rhoFinal : ℝ) (J : ℕ)
    (hscale : 512 * rhoFinal = (mu m * (R : ℝ)) * (J : ℝ)) :
    ⌊NativeConfiguredTimeCoarsening.finalTime (mu m * (R : ℝ))
      (translatedHeight D a m k / ((8 * R : ℕ) : ℤ)) / rhoFinal⌋ =
      ⌊oldPoint D a m p k (3 : Fin 4) / (512 * rhoFinal)⌋ := by
  rw [coarse_height_readback D a m p R k]
  exact NativeConfiguredTimeCoarsening.floor_from_original (mu m * (R : ℝ)) rhoFinal
    (oldPoint D a m p k (3 : Fin 4)) (mul_pos (mu_pos m) (by exact_mod_cast hR)) J hscale

end NativeReferenceConfiguredTime
