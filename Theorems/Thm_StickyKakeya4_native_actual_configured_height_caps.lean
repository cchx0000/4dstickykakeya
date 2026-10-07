import Theorems.Thm_StickyKakeya4_native_actual_configured_point
import Theorems.Thm_StickyKakeya4_native_configured_height_caps

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeActualConfiguredHeightCaps
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeHorizontalGrainSlice NativeReferenceXYGridPoints CanonicalConfiguredE4Bridge
open NativeActualConfiguredPoint NativeConfiguredTimeCoarsening NativeConfiguredHeightCaps

/-- Actual configured heights are an image of the unchanged translated
integer heights. Original point multiplicities are removed by the image. -/
theorem actual_height_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (S : Finset Index) :
    S.image (fun k => point D a m p s P hP hd F Fcfg R k (3:Fin 4)) =
      (S.image (fun k => NativeTranslatedGrainHeightOverlap.translatedHeight D a m k/(8*R:ℕ))).image
        (finalTime (mu m*(R:ℝ))) := by
  rw [image_image]
  congr 1
  funext k
  simp only [Function.comp_def, point, graphGrid_height, sourceLabel_height]

/-- The unconditional midpoint lattice gives a timeMesh separated height
set directly, even before any global residue choice. -/
theorem actual_height_separation {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (hR : 0 < R) (S : Finset Index) :
    let Z := S.image (fun k => point D a m p s P hP hd F Fcfg R k (3:Fin 4))
    ∀ z∈Z, ∀ w∈Z, z≠w → (mu m*(R:ℝ))/512 ≤ |z-w| := by
  dsimp only
  rw [actual_height_image]
  simpa only [Nat.cast_one, mul_one] using time_image_separation
    (S.image (fun k => NativeTranslatedGrainHeightOverlap.translatedHeight D a m k/(8*R:ℕ)))
    (mu m*(R:ℝ)) (by have hmu := mu_pos m; positivity) 1 (by decide)
    (by intro x _ y _; simp)

/-- The original height interval count is derived for these literal
configured heights; the physical tube thickness is not changed. -/
theorem actual_height_interval_cap {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (hR : 0 < R) (S : Finset Index) (c r : ℝ) (hr : 0 ≤ r) :
    (((S.image (fun k => point D a m p s P hP hd F Fcfg R k (3:Fin 4))).filter
      (fun z => c≤z ∧ z≤c+r)).card:ℝ) ≤ r/((mu m*(R:ℝ))/512)+2 := by
  rw [actual_height_image]
  exact unconditional_interval_cap _ _ (by have hmu := mu_pos m; positivity) c r hr

end NativeActualConfiguredHeightCaps
