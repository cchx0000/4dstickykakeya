import Theorems.Thm_StickyKakeya4_native_padded_cell_source
import Theorems.Thm_StickyKakeya4_native_original_slope_cube_packing
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace NativePaddedSourceADUpper
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeOriginalCellChartGeometry
open NativeCommonCubicalMesh NativePaddedCellSource NativeContractedUnitParent NativeUnitParentDirections
open NativeOriginalSlopeCubePacking

/-- Actual direction separation supplies the new source's carrier-ball upper
bound by the already proved three-dimensional slope-grid injection. There
is no new carrier AD assumption. The estimate holds at all larger radii. -/
theorem source_carrier_upper {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (p : Parent) (hp : ∀i∈R,parentLabel D a 1 i=p)
    (i : Fin R.card) {r : ℝ} (hr : (source h original R a p hp).thickness ≤ r) :
    (wzCarrierBallCount (source h original R a p hp) i r:ℝ) ≤
      10077696*(r/(source h original R a p hp).thickness)^3 := by
  let S := source h original R a p hp
  let A := (univ : Finset (Fin R.card)).filter (fun j => dist (wzCarrierPoint S j) (wzCarrierPoint S i) ≤ r)
  have hd : 0 < S.thickness := by change 0 < D.thickness/64; have hh:=h.1.2.1; positivity
  have hrp : 0 < r := hd.trans_le hr
  have hg (j : Fin R.card) : IsValidLine (S.line j) ∧ (1/2:ℝ) ≤ direction (S.line j) (3:Fin 4) := by
    have hh := contracted_line_common_slab D a p (originalLabel R j) (hp _ (originalLabel_mem R j))
    exact ⟨hh.1,hh.2.1⟩
  have hsep (j k : Fin R.card) (hne : j ≠ k) : S.thickness ≤ dist (direction (S.line j)) (direction (S.line k)) := by
    exact contracted_direction_separation h p _ _ (hp _ (originalLabel_mem R j)) (hp _ (originalLabel_mem R k))
      (fun he => hne (originalLabel_injective R he))
  have hbox (j : Fin R.card) (hj : j∈A) (k : Fin 3) :
      slope (S.line i) k-6*r ≤ slope (S.line j) k ∧
        slope (S.line j) k ≤ (slope (S.line i) k-6*r)+12*r := by
    have hdir : dist (direction (S.line j)) (direction (S.line i)) ≤ r :=
      (show dist (direction (S.line j)) (direction (S.line i)) ≤
        dist (wzCarrierPoint S j) (wzCarrierPoint S i) from le_max_left _ _).trans (mem_filter.mp hj).2
    have hs := (slope_sub_le_direction_dist (S.line j) (S.line i) (hg i).1 (hg j).2 (hg i).2 k).trans
      (mul_le_mul_of_nonneg_left hdir (by norm_num : (0:ℝ) ≤ 6))
    have hb := abs_le.mp hs
    constructor <;> linarith
  have hh := original_cube_card_le_ratio A S.line hd (show S.thickness ≤ 12*r by linarith)
    (fun j _hj => (hg j).1) (fun j _hj => (hg j).2)
    (fun j _hj k _hk hne => hsep j k hne) (fun k => slope (S.line i) k-6*r) hbox
  change (A.card:ℝ) ≤ 10077696*(r/S.thickness)^3
  exact hh.trans_eq (by ring)
end NativePaddedSourceADUpper
