import Theorems.Thm_StickyKakeya4_native_actual_configured_height_caps
import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeMatchedHeightBound
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeOriginalCellChartGeometry CanonicalConfiguredE4Bridge NativeActualConfiguredPoint

/-- Actual configured time stays in the fixed source interval. This uses
the original shading-cell time and its literal midpoint, not rawHeight. -/
lemma point_time_bound {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (m : ℕ) (p : Parent) (i : Fin n) (k : Index) (hk : k ∈ original i)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R0 : ℕ) (hR0 : 0 < R0) (hsmall : mu m * (R0 : ℝ) ≤ 64) :
    |point D a m p s P hP hd F Fcfg R0 k (3 : Fin 4)| ≤ 1 := by
  have ht := (NativeOriginalParentPhysicalData.original_cell_bounds h original horiginal a ha
    ((mem_incidences original i k).mpr hk)).1
  change |NativeOriginalPaddedCells.oldTime D a k| ≤ 1 at ht
  have htold : |oldPoint D a m p k (3 : Fin 4)| ≤ 1 / 128 := by
    unfold oldPoint
    rw [NativeLocalCellCoherence.physicalCell_height, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 128)]
    exact div_le_div_of_nonneg_right ht (by norm_num)
  let d := mu m * (R0 : ℝ)
  let t := oldPoint D a m p k (3 : Fin 4)
  have hdpos : 0 < d := mul_pos (mu_pos m) (by exact_mod_cast hR0)
  have hmid := CanonicalConfiguredPointRounding.midpoint_error d t hdpos
  have habs : |d * ((⌊t / d⌋ : ℝ) + 1 / 2)| ≤ d / 2 + 1 / 128 := by
    have hh := (abs_add_le (d * ((⌊t / d⌋ : ℝ) + 1 / 2) - t) t).trans
      (add_le_add hmid htold)
    simpa only [sub_add_cancel] using hh
  have hread : point D a m p s P hP hd F Fcfg R0 k (3 : Fin 4) =
      (d * ((⌊t / d⌋ : ℝ) + 1 / 2)) / 512 := by
    rw [point, graphGrid_height, sourceLabel_height,
      NativeReferenceConfiguredTime.coarse_height_readback D a m p R0 k]
    unfold NativeConfiguredTimeCoarsening.finalTime
    dsimp only [d, t]
    ring
  rw [hread, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 512)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 512)).mpr
  change d ≤ 64 at hsmall
  linarith only [habs, hsmall]

/-- A genuine original baseline has only O(1/Delta) distinct configured
heights. The unconditional midpoint lattice has spacing Delta/8; no new
height selection or projected separation certificate is required. -/
theorem baseline_height_bound {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (B : Finset (Fin n × Index)) (hB : B ⊆ incidences original)
    (m b : ℕ) (hb : 6 ≤ b) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R0 : ℕ) (hR0 : 0 < R0)
    (hmatch : mu m * (R0 : ℝ) = 4096 / ((2 ^ b : ℕ) : ℝ)) :
    ((B.image (fun z => point D a m p s P hP hd F Fcfg R0 z.2 (3 : Fin 4))).card : ℝ) ≤
      18 / (64 / ((2 ^ b : ℕ) : ℝ)) := by
  let Delta : ℝ := 64 / ((2 ^ b : ℕ) : ℝ)
  have hD : 0 < Delta := by dsimp [Delta]; positivity
  have hD1 : Delta ≤ 1 := NativeCoarseShadingPruning.coarse_thickness_le_one b hb
  have hsmall : mu m * (R0 : ℝ) ≤ 64 := by
    rw [hmatch]
    calc
      _ = 64 * Delta := by dsimp [Delta]; ring
      _ ≤ 64 * 1 := mul_le_mul_of_nonneg_left hD1 (by norm_num)
      _ = 64 := by ring
  let S := B.image Prod.snd
  let Z := S.image (fun k => point D a m p s P hP hd F Fcfg R0 k (3 : Fin 4))
  have hZ : Z = B.image (fun z => point D a m p s P hP hd F Fcfg R0 z.2 (3 : Fin 4)) := by
    rw [Z, S, image_image]
    rfl
  have htime : ∀ z ∈ Z, -1 ≤ z ∧ z ≤ 1 := by
    intro z hz
    rw [hZ] at hz
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hz
    exact abs_le.mp (point_time_bound h original horiginal ha m p v.1 v.2
      ((mem_incidences original v.1 v.2).mp (hB hv)) s P hP hd F Fcfg R0 hR0 hsmall)
  have hfilter : Z.filter (fun z => (-1 : ℝ) ≤ z ∧ z ≤ -1 + 2) = Z := by
    apply filter_eq_self.mpr
    intro z hz
    simpa only [show (-1 : ℝ) + 2 = 1 by norm_num] using htime z hz
  have hh := NativeActualConfiguredHeightCaps.actual_height_interval_cap
    D a m p s P hP hd F Fcfg R0 hR0 S (-1) 2 (by norm_num)
  change ((Z.filter (fun z => (-1 : ℝ) ≤ z ∧ z ≤ -1 + 2)).card : ℝ) ≤ _ at hh
  rw [hfilter] at hh
  have hmesh : (mu m * (R0 : ℝ)) / 512 = Delta / 8 := by
    rw [hmatch]
    dsimp [Delta]
    ring
  rw [hmesh] at hh
  have hmul := mul_le_mul_of_nonneg_right hh hD.le
  have hid : (2 / (Delta / 8) + 2) * Delta = 16 + 2 * Delta := by
    rw [div_div_eq_mul_div, add_mul, div_mul_cancel₀ _ hD.ne']
    norm_num
  rw [hid] at hmul
  rw [← hZ]
  apply (le_div_iff₀ hD).mpr
  linarith only [hmul, hD1]

end NativeMatchedHeightBound
