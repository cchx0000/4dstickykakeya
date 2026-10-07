import Theorems.Thm_StickyKakeya4_native_actual_configured_point
import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeMatchedShadowConfiguredGeometry
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeRelativeCoarseGeometry NativeRelativeCoarsePointMenu NativeRelativeParentLabels
open NativeNormalizedCellRelativeMenu CanonicalConfiguredE4Bridge NativeActualConfiguredPoint

/-- Four Euclidean coordinates bounded by e have distance at most 2e. -/
lemma distance_of_coordinates (x y : E4) (e : ℝ) (he : 0 ≤ e)
    (h : ∀ v : Fin 4, |x v - y v| ≤ e) : dist x y ≤ 2 * e := by
  have hh := dist_le_three_of_coordinate_error ((2 / 3 : ℝ) * e)
    (by positivity) x y (fun v => (h v).trans_eq (by ring))
  nlinarith only [hh]

/-- The actual point and actual relative representative front at the matched
scale differ by at most the output thickness. The fine reference mesh enters
only through its genuine relative-scale guard. -/
theorem point_front_distance {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (m M : ℕ) (hm : 6 ≤ m) (hM : 0 < M)
    (hNscale : ((2 ^ m : ℕ) : ℝ) * D.thickness ≤ 1)
    (hRelScale : ((2 ^ m : ℕ) : ℝ) * D.thickness * (M : ℝ) ≤ 64)
    (p : Parent) (i j : Fin n) (k : Index) (hk : k ∈ original i)
    (hi : parentLabel D a (2 ^ m) i = p)
    (hr : relativeLabel D a (2 ^ m) p M j = relativeLabel D a (2 ^ m) p M i)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t u v, |F t u v| ≤ 1 / 4) (hCfg : ∀ t u v, |Fcfg t u v| ≤ 1 / 4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m * (R0 : ℝ))
    (hmatch : mu m * (R0 : ℝ) ≤ 4096 / (M : ℝ)) :
    dist (point D a m p s P hP hd F Fcfg R0 k)
      (NativePackedFrameIsometry.frame s P hP hd (doubleFront D a (2 ^ m) p j i k)) ≤
        64 / (M : ℝ) := by
  let O := NativePackedFrameIsometry.frame s P hP hd
  let cfg := point D a m p s P hP hd F Fcfg R0 k
  let raw := (1 / 512 : ℝ) • rawPoint D a m p k
  let old := (1 / 512 : ℝ) • oldPoint D a m p k
  let front := doubleFront D a (2 ^ m) p j i k
  have hfront : dist front old ≤ 2 / (M : ℝ) := by
    apply (distance_of_coordinates front old (1 / (M : ℝ)) (by positivity) ?_).trans_eq
      (by ring)
    intro v
    have hv := double_front_physical_error h original horiginal ha (2 ^ m) M
      (by positivity) hM hNscale hRelScale p i j k hk hi hr v
    simpa only [front, old, PiLp.smul_apply, smul_eq_mul, one_div, div_eq_mul_inv,
      mul_comm, oldPoint, physicalPoint, one_mul, mul_one] using hv
  have hround : dist cfg (O raw) ≤ 3 * ((mu m * (R0 : ℝ)) / 512) :=
    point_distance D a m hm p s P hP hd F Fcfg hF hCfg R0 hR0 k hbase
  have hraw : dist (O raw) (O old) ≤ (128 * mu m) / 512 := by
    rw [O.dist_map]
    change dist ((1 / 512 : ℝ) • rawPoint D a m p k)
      ((1 / 512 : ℝ) • oldPoint D a m p k) ≤ _
    rw [dist_smul₀]
    norm_num
    have hh := physical_rounding h m hm p i hi k
    nlinarith only [hh]
  have htotal : dist cfg (O front) ≤
      3 * ((mu m * (R0 : ℝ)) / 512) + (128 * mu m) / 512 + 2 / (M : ℝ) := by
    have hfront' : dist (O old) (O front) ≤ 2 / (M : ℝ) := by
      rw [O.dist_map, dist_comm old front]
      exact hfront
    calc
      _ ≤ dist cfg (O raw) + dist (O raw) (O front) := dist_triangle _ _ _
      _ ≤ dist cfg (O raw) + (dist (O raw) (O old) + dist (O old) (O front)) := by
        linarith only [dist_triangle (O raw) (O old) (O front)]
      _ ≤ _ := by linarith only [hround, hraw, hfront']
  have hrho : rho m = 64 * mu m := by unfold mu; ring
  rw [hrho] at hbase
  have hmu : mu m ≤ 64 / (M : ℝ) := by
    calc
      _ = (64 * mu m) / 64 := by ring
      _ ≤ (4096 / (M : ℝ)) / 64 :=
        div_le_div_of_nonneg_right (hbase.trans hmatch) (by norm_num)
      _ = _ := by ring
  have hc : 3 * ((mu m * (R0 : ℝ)) / 512) ≤ 24 / (M : ℝ) := by
    calc
      _ ≤ 3 * ((4096 / (M : ℝ)) / 512) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hmatch (by norm_num)) (by norm_num)
      _ = _ := by ring
  have hrawBound : (128 * mu m) / 512 ≤ 16 / (M : ℝ) := by
    calc
      _ = mu m / 4 := by ring
      _ ≤ (64 / (M : ℝ)) / 4 := div_le_div_of_nonneg_right hmu (by norm_num)
      _ = _ := by ring
  change dist cfg (O front) ≤ _
  calc
    _ ≤ 3 * ((mu m * (R0 : ℝ)) / 512) + (128 * mu m) / 512 + 2 / (M : ℝ) := htotal
    _ ≤ 24 / (M : ℝ) + 16 / (M : ℝ) + 2 / (M : ℝ) := by
      linarith only [hc, hrawBound]
    _ = 42 / (M : ℝ) := by ring
    _ ≤ 64 / (M : ℝ) := div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg M)

/-- The shading cell is the actual doubleLabel at mesh Delta/2. Its center
is within 2Delta of the configured point in the same fixed frame. -/
theorem point_shadow_center_distance {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (m M : ℕ) (hm : 6 ≤ m) (hM : 0 < M)
    (hNscale : ((2 ^ m : ℕ) : ℝ) * D.thickness ≤ 1)
    (hRelScale : ((2 ^ m : ℕ) : ℝ) * D.thickness * (M : ℝ) ≤ 64)
    (p : Parent) (i j : Fin n) (k : Index) (hk : k ∈ original i)
    (hi : parentLabel D a (2 ^ m) i = p)
    (hr : relativeLabel D a (2 ^ m) p M j = relativeLabel D a (2 ^ m) p M i)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t u v, |F t u v| ≤ 1 / 4) (hCfg : ∀ t u v, |Fcfg t u v| ≤ 1 / 4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m * (R0 : ℝ))
    (hmatch : mu m * (R0 : ℝ) ≤ 4096 / (M : ℝ)) :
    dist (point D a m p s P hP hd F Fcfg R0 k)
      (NativePackedFrameIsometry.frame s P hP hd
        (cellCenter (32 / (M : ℝ)) (doubleLabel D a (2 ^ m) M p j i k))) ≤
        2 * (64 / (M : ℝ)) := by
  let O := NativePackedFrameIsometry.frame s P hP hd
  have hf := point_front_distance h original horiginal ha m M hm hM hNscale hRelScale
    p i j k hk hi hr s P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
  have hc : dist (doubleFront D a (2 ^ m) p j i k)
      (cellCenter (32 / (M : ℝ)) (doubleLabel D a (2 ^ m) M p j i k)) ≤ 32 / (M : ℝ) := by
    apply (distance_of_coordinates _ _ ((32 / (M : ℝ)) / 2) (by positivity) ?_).trans_eq
      (by ring)
    intro v
    simpa only [doubleLabel, abs_sub_comm] using
      cell_center_coordinate_error (by positivity : 0 < 32 / (M : ℝ))
        (doubleFront D a (2 ^ m) p j i k) v
  have hh := dist_triangle (point D a m p s P hP hd F Fcfg R0 k)
    (O (doubleFront D a (2 ^ m) p j i k))
    (O (cellCenter (32 / (M : ℝ)) (doubleLabel D a (2 ^ m) M p j i k)))
  rw [O.dist_map] at hh
  change dist (point D a m p s P hP hd F Fcfg R0 k)
    (O (cellCenter _ _)) ≤ _
  calc
    _ ≤ dist (point D a m p s P hP hd F Fcfg R0 k)
        (O (doubleFront D a (2 ^ m) p j i k)) +
        dist (doubleFront D a (2 ^ m) p j i k)
          (cellCenter (32 / (M : ℝ)) (doubleLabel D a (2 ^ m) M p j i k)) := hh
    _ ≤ 64 / (M : ℝ) + 32 / (M : ℝ) := add_le_add hf hc
    _ = 96 / (M : ℝ) := by ring
    _ ≤ 128 / (M : ℝ) := div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg M)
    _ = _ := by ring

end NativeMatchedShadowConfiguredGeometry
