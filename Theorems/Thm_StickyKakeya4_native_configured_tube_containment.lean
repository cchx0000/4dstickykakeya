import Theorems.Thm_StickyKakeya4_native_coarse_physical_containment
import Theorems.Thm_StickyKakeya4_canonical_configured_E4_bridge

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeConfiguredTubeContainment
open Classical StickyKakeya4 NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeUnitParentNormalization NativeContractedUnitParent
open NativeCoarsePhysicalContainment CanonicalConfiguredE4Bridge

/-- The actual old front and its common-height representative give the
unrounded error before any coarse-scale absorption. -/
theorem original_infDist {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (i j : Fin n)
    (hcell : parentLabel D a N i = parentLabel D a N j)
    (x : E4) (hx : x ∈ markedUnitTube (D.line i) D.thickness) :
    Metric.infDist (physicalMap D a (0, 0) x)
      (unitFront {NativeContractedUnitParent.line D a (0, 0) j}) ≤
        D.thickness / 64 + (1 / (N : ℝ)) / 32 := by
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨t, ht, hxt⟩ := exists_rawFrontParam_dist_lt_of_infDist_le
    (D.line i) x hx (show 0 < 64 * eps by positivity)
  let s := (rawFrontParam (D.line i, t) (3 : Fin 4) - (shift D a : ℝ) * mesh D) / 16
  have hs : |s| ≤ 1 / 4 := original_front_height_bound h ha i ht
  have hp := graphPoint_mem_front h a j hs
  have he : physicalMap D a (0, 0) (rawFrontParam (D.line i, t)) = graphPoint D a i s := by
    unfold physicalMap graphPoint
    rw [map_rawFront_graph _ _ _ _ _
      (show direction (D.line i) (3 : Fin 4) ≠ 0 by linarith [h.2.1.1 i])]
  have hd := graphPoint_same_cell_dist D a N hN i j hcell hs
  have hh := physicalMap_dist_zero D a x (rawFrontParam (D.line i, t))
  have ht' := dist_triangle (physicalMap D a (0, 0) x)
    (physicalMap D a (0, 0) (rawFrontParam (D.line i, t))) (graphPoint D a j s)
  rw [he] at ht' hh
  apply (Metric.infDist_le_dist_of_mem hp).trans
  nlinarith only [hxt, hd, hh, ht']

/-- The sharp margin in the existing coarse representative tube is
3/(64N), using only the actual fine/coarse scale relation. -/
theorem original_infDist_sharp {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (hscale : (N : ℝ) * D.thickness ≤ 1)
    (i j : Fin n) (hcell : parentLabel D a N i = parentLabel D a N j)
    (x : E4) (hx : x ∈ markedUnitTube (D.line i) D.thickness) :
    Metric.infDist (physicalMap D a (0, 0) x)
      (unitFront {NativeContractedUnitParent.line D a (0, 0) j}) ≤ 3 / (64 * (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdr : D.thickness ≤ 1 / (N : ℝ) :=
    (le_div_iff₀ hNr).mpr (by nlinarith only [hscale])
  calc
    _ ≤ D.thickness / 64 + (1 / (N : ℝ)) / 32 := original_infDist h ha N hN i j hcell x hx
    _ ≤ (1 / (N : ℝ)) / 64 + (1 / (N : ℝ)) / 32 := by linarith only [hdr]
    _ = _ := by field_simp; norm_num

/-- Rounding is charged as actual movement of the point, while the tube
remains the same original representative tube. -/
theorem rounded_infDist {n : ℕ} {D : FiniteScaleSource n} {eta a base : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (hscale : (N : ℝ) * D.thickness ≤ 1)
    (i j : Fin n) (hcell : parentLabel D a N i = parentLabel D a N j)
    (x y : E4) (hx : x ∈ markedUnitTube (D.line i) D.thickness)
    (hround : dist y (physicalMap D a (0, 0) x) ≤ 3 * base) :
    Metric.infDist y (unitFront {NativeContractedUnitParent.line D a (0, 0) j}) ≤
      3 * base + 3 / (64 * (N : ℝ)) := by
  have hnear := original_infDist_sharp h ha N hN hscale i j hcell x hx
  have hmove := Metric.infDist_le_infDist_add_dist
    (x := y) (y := physicalMap D a (0, 0) x)
    (s := unitFront {NativeContractedUnitParent.line D a (0, 0) j})
  linarith only [hnear, hmove, hround]

/-- The configured base scale may be as large as 8/N. Its C=3 movement
still fits inside the unchanged representative's radius 64/N. -/
theorem rounded_mem_representative {n : ℕ} {D : FiniteScaleSource n} {eta a base : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (hscale : (N : ℝ) * D.thickness ≤ 1)
    (i j : Fin n) (hcell : parentLabel D a N i = parentLabel D a N j)
    (x y : E4) (hx : x ∈ markedUnitTube (D.line i) D.thickness)
    (hround : dist y (physicalMap D a (0, 0) x) ≤ 3 * base)
    (hbase : base ≤ 8 / (N : ℝ)) :
    y ∈ markedUnitTube (NativeContractedUnitParent.line D a (0, 0) j) (64 / (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  change Metric.infDist y _ ≤ 64 / (N : ℝ)
  calc
    _ ≤ 3 * base + 3 / (64 * (N : ℝ)) := rounded_infDist h ha N hN hscale i j hcell x y hx hround
    _ ≤ 3 * (8 / (N : ℝ)) + 3 / (64 * (N : ℝ)) := by linarith only [hbase]
    _ = (1539 / 64 : ℝ) / (N : ℝ) := by field_simp; norm_num
    _ ≤ 64 / (N : ℝ) := div_le_div_of_nonneg_right (by norm_num) hNr.le

/-- Exact inverse-chart metric readback, including its translation. -/
lemma chart_pullback_dist (O : E4 ≃ₗᵢ[ℝ] E4) (c z p : E4) :
    dist (O.symm z + c) p = dist z (O (p - c)) := by
  calc
    _ = dist (O.symm z + c) ((p - c) + c) := by rw [sub_add_cancel]
    _ = dist (O.symm z) (p - c) := dist_add_right _ _ _
    _ = dist (O.symm z) (O.symm (O (p - c))) := by rw [O.symm_apply_apply]
    _ = _ := O.symm.dist_map _ _

/-- Pull a rounded chart point back before reading membership in the same
physical representative tube. Configured coordinates are not identified
with the unchanged physical point. -/
theorem charted_mem_representative {n : ℕ} {D : FiniteScaleSource n} {eta a base : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (hscale : (N : ℝ) * D.thickness ≤ 1)
    (i j : Fin n) (hcell : parentLabel D a N i = parentLabel D a N j)
    (x : E4) (hx : x ∈ markedUnitTube (D.line i) D.thickness)
    (O : E4 ≃ₗᵢ[ℝ] E4) (c configured : E4)
    (hround : dist configured (O (physicalMap D a (0, 0) x - c)) ≤ 3 * base)
    (hbase : base ≤ 8 / (N : ℝ)) :
    O.symm configured + c ∈
      markedUnitTube (NativeContractedUnitParent.line D a (0, 0) j) (64 / (N : ℝ)) := by
  exact rounded_mem_representative h ha N hN hscale i j hcell x (O.symm configured + c) hx
    (by simpa only [chart_pullback_dist] using hround) hbase

/-- The literal configured-point construction supplies its own C=3 error;
this endpoint has no rounding or containment premise for the output point. -/
theorem actual_configured_mem_representative {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (hscale : (N : ℝ) * D.thickness ≤ 1)
    (i j : Fin n) (hcell : parentLabel D a N i = parentLabel D a N j)
    (x : E4) (hx : x ∈ markedUnitTube (D.line i) D.thickness)
    (s : Split) (mu : ℝ) (R : ℕ) (hmu : 0 < mu) (hR : 0 < R)
    (Fold Fcfg : Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hOld : ∀ u v, |Fold u v| ≤ 1 / 4) (hCfg : ∀ u v, |Fcfg u v| ≤ 1 / 4)
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (hbase : mu * (R : ℝ) ≤ 8 / (N : ℝ)) :
    O.symm (configuredPoint s mu R Fold Fcfg O c (physicalMap D a (0, 0) x)) + c ∈
      markedUnitTube (NativeContractedUnitParent.line D a (0, 0) j) (64 / (N : ℝ)) := by
  exact charted_mem_representative h ha N hN hscale i j hcell x hx O c _
    (configuredPoint_distance s mu R hmu hR Fold Fcfg hOld hCfg O c (physicalMap D a (0, 0) x)) hbase

end NativeConfiguredTubeContainment
