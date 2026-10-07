import Theorems.Thm_StickyKakeya4_native_zero_parent_physical_map
import Theorems.Thm_StickyKakeya4_native_configured_tube_containment

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeZeroParentRadiusContainment
open StickyKakeya4 NativeOriginalParentSelection NativeUnitParentNormalization
open NativeContractedUnitParent NativeCoarsePhysicalContainment NativeZeroParentPhysicalMap
open NativeConfiguredTubeContainment CanonicalConfiguredE4Bridge

/-- The input radius is independent of the source's fine thickness. At
common height zero its contribution contracts by exactly 1/512. -/
theorem radius_infDist {n : ℕ} {D : FiniteScaleSource n} {eta t : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) 0 - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (M : ℕ) (hM : 0 < M) (i j : Fin n)
    (hcell : parentLabel D 0 M i = parentLabel D 0 M j)
    (x : E4) (hx : x ∈ markedUnitTube (D.line i) t) :
    Metric.infDist (physicalMap D 0 (0, 0) x)
      (unitFront {NativeContractedUnitParent.line D 0 (0, 0) j}) ≤
        t / 512 + (1 / (M : ℝ)) / 32 := by
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨u, hu, hxu⟩ := exists_rawFrontParam_dist_lt_of_infDist_le
    (D.line i) x hx (show 0 < 512 * eps by positivity)
  let s := (rawFrontParam (D.line i, u) (3 : Fin 4) - (shift D 0 : ℝ) * mesh D) / 16
  have hs : |s| ≤ 1 / 4 := original_front_height_bound h ha i hu
  have hp := graphPoint_mem_front h 0 j hs
  have he : physicalMap D 0 (0, 0) (rawFrontParam (D.line i, u)) = graphPoint D 0 i s := by
    unfold physicalMap graphPoint
    rw [map_rawFront_graph _ _ _ _ _
      (show direction (D.line i) (3 : Fin 4) ≠ 0 by linarith [h.2.1.1 i])]
  have hd := graphPoint_same_cell_dist D 0 M hM i j hcell hs
  have hh := zero_map_dist D x (rawFrontParam (D.line i, u))
  have ht := dist_triangle (physicalMap D 0 (0, 0) x)
    (physicalMap D 0 (0, 0) (rawFrontParam (D.line i, u))) (graphPoint D 0 j s)
  rw [he] at ht hh
  apply (Metric.infDist_le_dist_of_mem hp).trans
  nlinarith only [hxu, hd, hh, ht]

/-- This fixed margin permits the actual fat raw-point tube, rather than
requiring membership in a tube at the reference source's fine thickness. -/
theorem rounded_radius_mem {n : ℕ} {D : FiniteScaleSource n} {eta t base : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) 0 - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (M : ℕ) (hM : 0 < M) (i j : Fin n)
    (hcell : parentLabel D 0 M i = parentLabel D 0 M j)
    (x y : E4) (hx : x ∈ markedUnitTube (D.line i) t)
    (hround : dist y (physicalMap D 0 (0, 0) x) ≤ 3 * base)
    (ht : t ≤ 12288 / (M : ℝ)) (hbase : base ≤ 8 / (M : ℝ)) :
    y ∈ markedUnitTube (NativeContractedUnitParent.line D 0 (0, 0) j) (64 / (M : ℝ)) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hnear := radius_infDist h ha M hM i j hcell x hx
  have hmove := Metric.infDist_le_infDist_add_dist
    (x := y) (y := physicalMap D 0 (0, 0) x)
    (s := unitFront {NativeContractedUnitParent.line D 0 (0, 0) j})
  change Metric.infDist y _ ≤ 64 / (M : ℝ)
  calc
    _ ≤ t / 512 + (1 / (M : ℝ)) / 32 + 3 * base := by linarith only [hnear, hmove, hround]
    _ ≤ (12288 / (M : ℝ)) / 512 + (1 / (M : ℝ)) / 32 + 3 * (8 / (M : ℝ)) := by
      linarith only [ht, hbase]
    _ = (1537 / 32 : ℝ) / (M : ℝ) := by field_simp; norm_num
    _ ≤ 64 / (M : ℝ) := div_le_div_of_nonneg_right (by norm_num) hMr.le

/-- Literal configured rounding, including inverse-chart translation, stays
inside the same actual representative tube at the displayed source scales. -/
theorem actual_configured_radius_mem {n : ℕ} {D : FiniteScaleSource n} {eta t : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) 0 - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (M : ℕ) (hM : 0 < M) (i j : Fin n)
    (hcell : parentLabel D 0 M i = parentLabel D 0 M j)
    (x : E4) (hx : x ∈ markedUnitTube (D.line i) t)
    (s : Split) (mu : ℝ) (R : ℕ) (hmu : 0 < mu) (hR : 0 < R)
    (Fold Fcfg : Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hOld : ∀ u v, |Fold u v| ≤ 1 / 4) (hCfg : ∀ u v, |Fcfg u v| ≤ 1 / 4)
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    (ht : t ≤ 12288 / (M : ℝ)) (hbase : mu * (R : ℝ) ≤ 8 / (M : ℝ)) :
    O.symm (configuredPoint s mu R Fold Fcfg O c (physicalMap D 0 (0, 0) x)) + c ∈
      markedUnitTube (NativeContractedUnitParent.line D 0 (0, 0) j) (64 / (M : ℝ)) := by
  apply rounded_radius_mem h ha M hM i j hcell x _ hx ?_ ht hbase
  rw [chart_pullback_dist]
  exact configuredPoint_distance s mu R hmu hR Fold Fcfg hOld hCfg O c (physicalMap D 0 (0, 0) x)

end NativeZeroParentRadiusContainment
