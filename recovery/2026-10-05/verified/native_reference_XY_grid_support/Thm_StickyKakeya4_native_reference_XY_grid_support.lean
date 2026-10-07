import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_incidence
import Theorems.Thm_StickyKakeya4_native_parent_slice_height_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeReferenceXYGridSupport
open Classical Finset StickyKakeya4 NativeReferenceXYGridLinear NativeReferenceXYGridPoints
open NativeReferenceXYGridMaps NativeGrainQuotientInjection NativeGrainQuotientBins
open NativeHorizontalGrainSlice NativeOriginalParentSelection NativeOriginalCellChartGeometry
open NativeOriginalParentPhysicalData NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeSquaredGrainQueries
open scoped BigOperators Matrix.Norms.Elementwise

/-- The integer half-width matching the genuine XY mesh exactly. -/
def halfWidth (m : ℕ) : ℕ := 2^(m-1)

lemma mu_halfWidth (m : ℕ) (hm : 1 ≤ m) : mu m*(halfWidth m:ℝ)=1/2 := by
  have he : (2^m:ℕ)=2^(m-1)*2 := by
    conv_lhs => rw [show m=(m-1)+1 by omega]
    rw [pow_succ]
  unfold mu rho halfWidth
  rw [he]
  push_cast
  have hn : (2:ℝ)^(m-1)≠0 := by positivity
  field_simp

lemma mu_fullWidth (m : ℕ) (hm : 1 ≤ m) : mu m*(2*(halfWidth m:ℝ))=1 := by
  have hh := mu_halfWidth m hm
  linarith

lemma terminal_bounds (m : ℕ) (hm : 12 ≤ m) :
    mu m ≤ 1/4096 ∧ ((2^m:ℕ):ℝ)*(rho m)^2 ≤ 1 := by
  have hn : (4096:ℝ) ≤ ((2^m:ℕ):ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hm
  have hp : (0:ℝ) < ((2^m:ℕ):ℝ) := by positivity
  have hmu : mu m=1/((2^m:ℕ):ℝ) := by unfold mu rho; ring
  have he : ((2^m:ℕ):ℝ)*(rho m)^2=4096/((2^m:ℕ):ℝ) := by
    unfold rho
    field_simp
    norm_num
  rw [hmu,he]
  constructor
  · apply (div_le_iff₀ hp).mpr
    linarith
  · apply (div_le_iff₀ hp).mpr
    linarith

/-- Actual original incidence and actual parent membership give a fixed
ambient support bound for the unchanged physical microcell center. -/
theorem oldPoint_norm {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m : ℕ) (hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (p : Parent) (i : Fin n) (k : Index) (hk : (i,k)∈incidences cells)
    (hi : parentLabel D a (2^m) i=p) : ‖oldPoint D a m p k‖ ≤ 49/128 := by
  have hs := NativeParentSliceHeightGeometry.physical_parent_spatial_bound h cells hcells ha
    (2^m) hscale p i hi k ((mem_incidences cells i k).mp hk)
  have ht : |oldPoint D a m p k (3:Fin 4)| ≤ 1/128 := by
    unfold oldPoint
    rw [NativeLocalCellCoherence.physicalCell_height,abs_div,abs_of_pos (by norm_num : (0:ℝ)<128)]
    have hh := (original_cell_bounds h cells hcells a ha hk).1
    change |NativeOriginalPaddedCells.oldTime D a k| ≤ 1 at hh
    exact div_le_div_of_nonneg_right hh (by norm_num)
  have hn := euclidean_norm_le_sum (oldPoint D a m p k)
  rw [Fin.sum_univ_four] at hn
  have h0 := hs (0:Fin 3)
  have h1 := hs (1:Fin 3)
  have h2 := hs (2:Fin 3)
  change |oldPoint D a m p k 0| ≤ 1/8 at h0
  change |oldPoint D a m p k 1| ≤ 1/8 at h1
  change |oldPoint D a m p k 2| ≤ 1/8 at h2
  linarith

/-- Raw phase rounding costs at most4/128 at m≥12, so the same point used
by the XY map has norm at most53/128. -/
theorem rawPoint_norm {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m : ℕ) (hm : 12 ≤ m) (hscale : D.thickness ≤ (rho m)^2)
    (p : Parent) (i : Fin n) (k : Index) (hk : (i,k)∈incidences cells)
    (hi : parentLabel D a (2^m) i=p) : ‖rawPoint D a m p k‖ ≤ 53/128 := by
  have hb := terminal_bounds m hm
  have hs : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 :=
    (mul_le_mul_of_nonneg_left hscale (by positivity)).trans hb.2
  have hold := oldPoint_norm h cells hcells ha m hs p i k hk hi
  have hr := physical_rounding h m (by omega) p i hi k
  have ht := norm_le_norm_add_const_of_dist_le hr
  linarith

/-- Exact integer support obtained from the real support, including both
signs of the floor label. -/
lemma label_support {d : ℕ} {r : ℝ} (hr : 0 < r) (N : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (hx : ‖x‖ ≤ r*(N:ℝ)) (j : Fin d) :
    |label r x j| ≤ (N:ℤ) := by
  have hcoord : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
  have hc : |x j| ≤ r*(N:ℝ) := hcoord.trans hx
  have hl : -((N:ℤ):ℝ) ≤ x j/r := by
    apply (le_div_iff₀ hr).mpr
    have hh := (abs_le.mp hc).1
    push_cast
    nlinarith
  have hu : x j/r ≤ ((N:ℤ):ℝ) := by
    apply (div_le_iff₀ hr).mpr
    exact (abs_le.mp hc).2.trans_eq (mul_comm _ _)
  have hfl := Int.floor_mono hl
  have hfu := Int.floor_mono hu
  norm_num only [Int.floor_neg,Int.ceil_intCast,Int.floor_intCast] at hfl hfu
  exact abs_le.mpr ⟨hfl,hfu⟩

/-- Honest support of the actual XY labels at the physical mesh mu. The
fixed full width2N satisfies mu·2N=1; no support hypothesis is introduced. -/
theorem pxy_support {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m : ℕ) (hm : 12 ≤ m) (hscale : D.thickness ≤ (rho m)^2)
    (p : Parent) (i : Fin n) (k : Index) (hk : (i,k)∈incidences cells)
    (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ)) :
    (∀j,|(pxy D a m ell p P hP hell hell4 hd F k).2.1 j| ≤ (halfWidth m:ℤ)) ∧
    (∀j,|(pxy D a m ell p P hP hell hell4 hd F k).2.2 j| ≤ (2*halfWidth m:ℕ)) := by
  have hr := rawPoint_norm h cells hcells ha m hm hscale p i k hk hi
  have ht := tangent_norm_le P ell hd (rawPoint D a m p k)
  have hq := quotient_norm_le P hP ell hell hell4 hd (F (NativeTranslatedGrainHeightOverlap.translatedHeight D a m k))
    (hF _) (rawPoint D a m p k)
  have hhalf := mu_halfWidth m (by omega)
  constructor
  · intro j
    apply label_support (mu_pos m) (halfWidth m) _ ?_ j
    linarith
  · intro j
    apply label_support (mu_pos m) (2*halfWidth m) _ ?_ j
    push_cast
    nlinarith

/-- The support endpoint with the squared-scale premise derived from the
original source dyadic level, preserving the same raw point and XY field. -/
theorem dyadic_pxy_support {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : phaseDepth m ≤ level)
    (p : Parent) (i : Fin n) (k : Index) (hk : (i,k)∈incidences cells)
    (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ)) :
    (∀j,|(pxy D a m ell p P hP hell hell4 hd F k).2.1 j| ≤ (halfWidth m:ℤ)) ∧
    (∀j,|(pxy D a m ell p P hP hell hell4 hd F k).2.2 j| ≤ (2*halfWidth m:ℕ)) :=
  pxy_support h cells hcells ha m hm
    (NativeActualSquaredGrainSelection.thickness_le_squared_scale m level (by omega) hdy hf)
    p i k hk hi P hP ell hell hell4 hd F hF

end NativeReferenceXYGridSupport
