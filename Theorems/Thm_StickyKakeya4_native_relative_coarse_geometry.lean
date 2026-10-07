import Theorems.Thm_StickyKakeya4_native_relative_parent_labels
import Theorems.Thm_StickyKakeya4_native_local_parent_source
import Theorems.Thm_StickyKakeya4_native_coarse_scale_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeRelativeCoarseGeometry
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeOriginalCellChartGeometry
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeLocalParentGeometry
open NativeRelativeParentLabels NativeUnitParentNormalization NativeContractedUnitParent
open scoped BigOperators

/-- The literal second zero-parent normalization of a graph point. -/
def zeroGraphPoint (line : MarkedLine) (t : ℝ) : E4 :=
  ActualSlopeSource.heightPoint
    (WithLp.toLp 2 (fun j : Fin 3 => (intercept line j+slope line j*t)/512)) (t/512)

/-- Map between the two already-normalized physical coarse pictures.
In particular its height coordinate is not multiplied by N. -/
def bridgePoint (N : ℕ) (p : Parent) (y : E4) : E4 :=
  ActualSlopeSource.heightPoint
    (WithLp.toLp 2 (fun j : Fin 3 =>
      ((N:ℝ)*y j.castSucc-(p.1 j:ℝ)*y (3:Fin 4)-(p.2 j:ℝ)/128)/512))
    (y (3:Fin 4)/512)

/-- This is an exact formula for the existing coarse constructor's front
point at common height zero, not a replacement grid center. -/
lemma zero_front_formula {n : ℕ} (S : FiniteScaleSource n) (i : Fin n) (k : Index) :
    NativeOriginalPaddedCells.frontPoint S 0 (0,0) i k =
      zeroGraphPoint (S.line i) (cellCenter (mesh S) k (3:Fin 4)) := by
  ext v
  refine Fin.lastCases ?_ (fun j => ?_) v
  · change NativeOriginalPaddedCells.frontPoint S 0 (0,0) i k (3:Fin 4) =
      cellCenter (mesh S) k (3:Fin 4)/512
    rw [NativeOriginalPaddedCells.frontPoint_height]
    dsimp [NativeOriginalPaddedCells.oldTime,ShearBinFibers.oldCenter,chartIndex,shift,cellCenter]
    norm_num
    ring
  · simp only [NativeOriginalPaddedCells.frontPoint,zeroGraphPoint,contractPoint,
      PiLp.smul_apply,PiLp.add_apply,smul_eq_mul,ActualSlopeSource.heightPoint_castSucc,
      newIntercept,newSlope,shiftedIntercept,shift,zero_div,Int.floor_zero,Int.cast_zero,
      zero_mul,mul_zero,add_zero,Pi.zero_apply,sub_zero]
    dsimp [NativeOriginalPaddedCells.oldTime,ShearBinFibers.oldCenter,chartIndex,shift,cellCenter]
    norm_num
    ring

/-- Exact coordinate relation before the local fine cell is rounded. -/
lemma local_front_bridge {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (i : Fin n) (k : Index) :
    zeroGraphPoint (NativeLocalParentGeometry.line D a N p i)
      (NativeLocalParentCells.frontPoint D a N p i k (3:Fin 4)) =
      bridgePoint N p (NativeOriginalPaddedCells.frontPoint D a (0,0) i k) := by
  ext v
  refine Fin.lastCases ?_ (fun j => ?_) v
  · change NativeLocalParentCells.frontPoint D a N p i k (3:Fin 4)/512 =
      NativeOriginalPaddedCells.frontPoint D a (0,0) i k (3:Fin 4)/512
    rw [NativeLocalParentCells.frontPoint_height,NativeOriginalPaddedCells.frontPoint_height]
  · simp only [zeroGraphPoint,bridgePoint,ActualSlopeSource.heightPoint_castSucc,
      actual_local_intercept,slope_line,NativeLocalParentCells.frontPoint_height,
      NativeOriginalPaddedCells.frontPoint_height]
    simp only [NativeOriginalPaddedCells.frontPoint,contractPoint,
      ActualSlopeSource.heightPoint_castSucc,PiLp.smul_apply,PiLp.add_apply,smul_eq_mul,
      newIntercept,newSlope,localIntercept,localSlope,Pi.zero_apply,Int.cast_zero,sub_zero]
    ring

lemma cell_center_coordinate_error {e : ℝ} (he : 0 < e) (x : E4) (v : Fin 4) :
    |cellCenter e (wzDyadicCellIndex e x) v-x v| ≤ e/2 := by
  have hlo := (le_div_iff₀ he).mp (Int.floor_le (x v/e))
  have hhi := (div_lt_iff₀ he).mp (Int.lt_floor_add_one (x v/e))
  change |e*((⌊x v/e⌋:ℝ)+1/2)-x v| ≤ e/2
  apply abs_le.mpr
  constructor <;> linarith

lemma zero_graph_time_error (line : MarkedLine)
    (hs : ∀ j, |slope line j| ≤ 1) (t u : ℝ) (v : Fin 4) :
    |zeroGraphPoint line t v-zeroGraphPoint line u v| ≤ |t-u|/512 := by
  refine Fin.lastCases ?_ (fun j => ?_) v
  · simp only [zeroGraphPoint,ActualSlopeSource.heightPoint_last]
    rw [←sub_div,abs_div]
    norm_num
  · have he : zeroGraphPoint line t j.castSucc-zeroGraphPoint line u j.castSucc =
        slope line j*(t-u)/512 := by
      simp only [zeroGraphPoint,ActualSlopeSource.heightPoint_castSucc]
      ring
    rw [he,abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<512)]
    exact div_le_div_of_nonneg_right
      (by simpa using mul_le_mul_of_nonneg_right (hs j) (abs_nonneg (t-u))) (by norm_num)

/-- The relative representative perturbation is controlled by the actual
local slope and quarter-intercept cells, at the same physical height. -/
lemma same_relative_front_error {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N M : ℕ) (hM : 0 < M) (p : Parent) (i j : Fin n)
    (he : relativeLabel D a N p M j = relativeLabel D a N p M i)
    (t : ℝ) (ht : |t| ≤ 4) (v : Fin 4) :
    |zeroGraphPoint (NativeLocalParentGeometry.line D a N p j) t v-
      zeroGraphPoint (NativeLocalParentGeometry.line D a N p i) t v| ≤ 1/(64*(M:ℝ)) := by
  refine Fin.lastCases ?_ (fun u => ?_) v
  · simp only [zeroGraphPoint,ActualSlopeSource.heightPoint_last,sub_self,abs_zero]
    positivity
  · let lj := NativeLocalParentGeometry.line D a N p j
    let li := NativeLocalParentGeometry.line D a N p i
    have hs := NativeNormalizedParentCarrierMetric.same_floor_mul_close
      (slope lj u) (slope li u) M hM (congrFun (congrArg Prod.fst he) u)
    have hb := NativeNormalizedParentCarrierMetric.same_floor_mul_close
      (shiftedIntercept lj 1 0 u) (shiftedIntercept li 1 0 u) M hM
      (congrFun (congrArg Prod.snd he) u)
    simp only [shiftedIntercept,Int.cast_zero,zero_mul,mul_zero,add_zero] at hb
    have hbi : |intercept lj u-intercept li u| ≤ 4/(M:ℝ) := by
      have hid : intercept lj u-intercept li u=4*(intercept lj u/4-intercept li u/4) := by ring
      rw [hid,abs_mul]
      norm_num
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 4)
    have hst : |(slope lj u-slope li u)*t| ≤ 4/(M:ℝ) := by
      rw [abs_mul]
      exact (mul_le_mul hs ht (abs_nonneg _) (by positivity)).trans_eq (by ring)
    have hid : zeroGraphPoint lj t u.castSucc-zeroGraphPoint li t u.castSucc =
        ((intercept lj u-intercept li u)+(slope lj u-slope li u)*t)/512 := by
      simp only [zeroGraphPoint,ActualSlopeSource.heightPoint_castSucc]
      ring
    change |zeroGraphPoint lj t u.castSucc-zeroGraphPoint li t u.castSucc| ≤ _
    rw [hid,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    have hh := (abs_add_le _ _).trans (add_le_add hbi hst)
    calc
      _ ≤ (4/(M:ℝ)+4/(M:ℝ))/512 := div_le_div_of_nonneg_right hh (by norm_num)
      _ = _ := by ring

/-- A global cube has a bounded image under the common anisotropic map.
This is the forward bound; it asserts no bounded inverse spatial menu. -/
lemma bridge_center_error (N : ℕ) (hN : 0 < N) (p : Parent)
    (hp : ∀j, |(p.1 j:ℝ)| ≤ 3*(N:ℝ)) {g : ℝ} (hg : 0 < g) (y : E4) (v : Fin 4) :
    |bridgePoint N p y v-bridgePoint N p (cellCenter g (wzDyadicCellIndex g y)) v| ≤
      (N:ℝ)*g/256 := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  let c := cellCenter g (wzDyadicCellIndex g y)
  have hc (w : Fin 4) : |y w-c w| ≤ g/2 := by
    simpa only [abs_sub_comm] using cell_center_coordinate_error hg y w
  refine Fin.lastCases ?_ (fun j => ?_) v
  · change |y (3:Fin 4)/512-c (3:Fin 4)/512| ≤ _
    rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    have hh := div_le_div_of_nonneg_right (hc 3) (by norm_num : (0:ℝ)≤512)
    have hn := mul_le_mul_of_nonneg_right hN1 hg.le
    nlinarith
  · have hid : bridgePoint N p y j.castSucc-bridgePoint N p c j.castSucc =
        ((N:ℝ)*(y j.castSucc-c j.castSucc)-(p.1 j:ℝ)*(y (3:Fin 4)-c (3:Fin 4)))/512 := by
      simp only [bridgePoint,ActualSlopeSource.heightPoint_castSucc]
      ring
    rw [hid,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    have h1 : |(N:ℝ)*(y j.castSucc-c j.castSucc)| ≤ (N:ℝ)*(g/2) := by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg N)]
      exact mul_le_mul_of_nonneg_left (hc j.castSucc) (Nat.cast_nonneg N)
    have h2 : |(p.1 j:ℝ)*(y (3:Fin 4)-c (3:Fin 4))| ≤ (3*(N:ℝ))*(g/2) := by
      rw [abs_mul]
      exact mul_le_mul (hp j) (hc 3) (abs_nonneg _) (by positivity)
    have hh := (abs_sub _ _).trans (add_le_add h1 h2)
    calc
      _ ≤ ((N:ℝ)*(g/2)+(3*(N:ℝ))*(g/2))/512 := div_le_div_of_nonneg_right hh (by norm_num)
      _ = _ := by ring

end NativeRelativeCoarseGeometry
