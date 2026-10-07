import Theorems.Thm_StickyKakeya4_native_actual_configured_point
import Theorems.Thm_StickyKakeya4_native_configured_original_cell_selection
import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeActualConfiguredCellSelection
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeHorizontalGrainSlice NativeReferenceXYGridPoints CanonicalConfiguredE4Bridge
open NativeMatrixHeightWholePoint NativePackedFrameIsometry
open scoped Matrix.Norms.Elementwise

/-- Source-facing support selection for the unique actual configured map.
Original parent membership supplies raw/old displacement; the actual pxy
reader supplies rounding. Only one subset of original point labels is cut. -/
theorem select_actual_edges {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (A : Finset (Fin n × Index)) (hparent : ∀ z ∈ A, parentLabel D a (2 ^ m) z.1 = p)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t, ‖F t‖ ≤ (1 / 4 : ℝ)) (hCfg : ∀ t, ‖Fcfg t‖ ≤ (1 / 4 : ℝ))
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m * (R0 : ℝ))
    (K : ℕ) (M : Fin K → ℕ) (hM : ∀ j, 0 < M j)
    (hmenu : ∀ j, mu m * (R0 : ℝ) ≤ 64 / (M j : ℝ)) :
    ∃ B ⊆ A.image Prod.snd, let T := edgeLift A Prod.snd B
      T ⊆ A ∧ A.card ≤ 53 ^ (4 * K) * T.card ∧
      (∀ k ∈ B, T.filter (fun z => z.2 = k) = A.filter (fun z => z.2 = k)) ∧
      ∀ j, ∀ x ∈ T, ∀ y ∈ T,
        wzDyadicCellIndex ((64 / (M j : ℝ)) / 64)
            (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 x.2) =
          wzDyadicCellIndex ((64 / (M j : ℝ)) / 64)
            (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 y.2) →
        NativeNormalizedCellRelativeMenu.physicalCell D a (2 ^ m) (M j) p x.2 =
          NativeNormalizedCellRelativeMenu.physicalCell D a (2 ^ m) (M j) p y.2 := by
  have hFe (t) (i) (j) : |F t i j| ≤ (1 / 4 : ℝ) := by
    simpa only [Real.norm_eq_abs] using (Matrix.norm_le_iff (by norm_num : (0 : ℝ) ≤ 1 / 4)).mp (hF t) i j
  have hCe (t) (i) (j) : |Fcfg t i j| ≤ (1 / 4 : ℝ) := by
    simpa only [Real.norm_eq_abs] using (Matrix.norm_le_iff (by norm_num : (0 : ℝ) ≤ 1 / 4)).mp (hCfg t) i j
  have hraw : ∀ k ∈ A.image Prod.snd, dist (rawPoint D a m p k) (oldPoint D a m p k) ≤ 128 * mu m := by
    intro k hk
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hk
    exact physical_rounding h m hm p z.1 (hparent z hz) z.2
  have hscale (j : Fin K) : 64 * mu m ≤ 64 / (M j : ℝ) := by
    have heq : 64 * mu m = rho m := by unfold mu; ring
    rw [heq]
    exact hbase.trans (hmenu j)
  have hround (j : Fin K) (k : Index) (_hk : k ∈ A.image Prod.snd) :
      dist (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 k)
        (frame s P hP hd ((1 / 512 : ℝ) • rawPoint D a m p k - 0)) ≤
          3 * ((64 / (M j : ℝ)) / 512) := by
    rw [sub_zero]
    exact (NativeActualConfiguredPoint.point_distance D a m hm p s P hP hd F Fcfg hFe hCe R0 hR0 k hbase).trans
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hmenu j) (by norm_num)) (by norm_num))
  exact NativeConfiguredOriginalCellSelection.select_original_edges K A Prod.snd
    (oldPoint D a m p) (rawPoint D a m p)
    (fun _ => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0)
    (fun _ => frame s P hP hd) (fun _ => 0) (mu m) (fun j => 64 / (M j : ℝ))
    (fun j => div_pos (by norm_num) (by exact_mod_cast hM j))
    hscale hraw hround

end NativeActualConfiguredCellSelection
