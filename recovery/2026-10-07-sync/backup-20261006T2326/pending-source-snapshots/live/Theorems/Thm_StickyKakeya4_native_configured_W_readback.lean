import Theorems.Thm_StickyKakeya4_native_configured_incidence_fibers
import Theorems.Thm_StickyKakeya4_native_actual_reference_W_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeConfiguredWReadback
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeReferenceXYGridPoints NativeSquaredGrainQueries

/-- The old graph in the configured fiber theorem is exactly the existing
deduplicated reference W graph at the actual squared phase, not the original
microcell-edge set. -/
theorem reference_incidence_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (p : Parent) (H : Finset (Fin n × Index)) :
    NativeActualReferenceWGeometry.incidences D a m (phaseDepth m) p H =
      H.image (fun z => (pref D a m p z.2, parentLabel D a (2^(phaseDepth m)) z.1)) := rfl

theorem reference_points_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (p : Parent) (H : Finset (Fin n × Index)) :
    TwoTubePathCollisionCount.points
      (NativeActualReferenceWGeometry.incidences D a m (phaseDepth m) p H) =
      (H.image Prod.snd).image (pref D a m p) := by
  rw [reference_incidence_readback]
  simp only [TwoTubePathCollisionCount.points, image_image, Function.comp_def]

end NativeConfiguredWReadback
