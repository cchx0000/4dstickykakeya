import Theorems.Thm_StickyKakeya4_native_relative_coarse_readback
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_incidence

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeCurrentSourceGeometry
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeLocalParentGeometry
open NativeRelativeCoarseGeometry NativeRelativeCoarsePointMenu NativeReferenceXYGridPoints
open NativeLocalParentCells NativeLocalCellCoherence NativeReferenceXYGridLinear
open NativeRelativeParentLabels
open scoped BigOperators

/-- The relative coarse depth matching the actual final XY mesh. -/
lemma final_scale (m : ℕ) : (64:ℝ)/((2^(m+6):ℕ):ℝ)=mu m := by
  simp only [mu,rho,pow_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  norm_num
  ring

lemma final_mesh (m : ℕ) : (32:ℝ)/((2^(m+6):ℕ):ℝ)=mu m/2 := by
  rw [←final_scale m]
  ring

/-- At its actual height the local front is exactly on its actual local
graph line. The second coarse normalization is the fixed homothety 1/512. -/
lemma second_front_homothety {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (i : Fin n) (k : Index) :
    zeroGraphPoint (NativeLocalParentGeometry.line D a N p i)
      (frontPoint D a N p i k (3:Fin 4))=(1/512:ℝ) • frontPoint D a N p i k := by
  ext v
  refine Fin.lastCases ?_ (fun j => ?_) v
  · change frontPoint D a N p i k (3:Fin 4)/512=(1/512:ℝ)*frontPoint D a N p i k (3:Fin 4)
    ring
  · rw [zeroGraphPoint,ActualSlopeSource.heightPoint_castSucc,
      actual_local_intercept,slope_line,frontPoint_height]
    simp only [frontPoint,NativeContractedUnitParent.contractPoint,
      PiLp.smul_apply,PiLp.add_apply,smul_eq_mul,ActualSlopeSource.heightPoint_castSucc]
    ring

/-- Source-derived comparison with the old physical point. It keeps the
second homothety explicit and includes both representative and fine-height
rounding errors; it does not identify their shading cells. -/
theorem double_front_oldPoint_error {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m M : ℕ) (hM : 0 < M) (hscale : ((2^m:ℕ):ℝ)*D.thickness≤1)
    (p : Parent) (i j : Fin n) (k : Index) (hk : k∈original i)
    (hi : parentLabel D a (2^m) i=p)
    (hr : NativeRelativeParentLabels.relativeLabel D a (2^m) p M j=
      NativeRelativeParentLabels.relativeLabel D a (2^m) p M i) (v : Fin 4) :
    |doubleFront D a (2^m) p j i k v-(oldPoint D a m p k) v/512| ≤
      1/(64*(M:ℝ))+localMesh D (2^m)/256 := by
  have hd := h.1.2.1
  have ht := (NativeOriginalParentPhysicalData.original_cell_bounds h original horiginal a ha
    ((mem_incidences original i k).mpr hk)).1
  change |NativeOriginalPaddedCells.oldTime D a k|≤1 at ht
  have h1 := same_relative_front_error D a (2^m) M hM p i j hr
    (roundedHeight D a (2^m) p i k)
    (rounded_height_bound hd a (2^m) (by positivity) hscale p i k ht) v
  have h2 := zero_graph_time_error (NativeLocalParentGeometry.line D a (2^m) p i)
    (by intro u; rw [slope_line]; exact localSlope_bound D a (2^m) p i hi u)
    (roundedHeight D a (2^m) p i k) (frontPoint D a (2^m) p i k (3:Fin 4)) v
  rw [second_front_homothety,PiLp.smul_apply,smul_eq_mul] at h2
  have hheight := rounded_height_error hd a (2^m) (by positivity) p i k
  have hfront := frontPoint_near_physicalCell h original horiginal ha (2^m) p i k hk v
  change |frontPoint D a (2^m) p i k v-oldPoint D a m p k v| ≤
    (3/2:ℝ)*localMesh D (2^m) at hfront
  have h3 : |(1/512:ℝ)*frontPoint D a (2^m) p i k v-oldPoint D a m p k v/512| ≤
      ((3/2:ℝ)*localMesh D (2^m))/512 := by
    rw [show (1/512:ℝ)*frontPoint D a (2^m) p i k v-oldPoint D a m p k v/512=
      (frontPoint D a (2^m) p i k v-oldPoint D a m p k v)/512 by ring,
      abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    exact div_le_div_of_nonneg_right hfront (by norm_num)
  have h12 := (abs_sub_le
    (doubleFront D a (2^m) p j i k v)
    (zeroGraphPoint (NativeLocalParentGeometry.line D a (2^m) p i)
      (roundedHeight D a (2^m) p i k) v)
    ((1/512:ℝ)*frontPoint D a (2^m) p i k v)).trans (add_le_add h1 h2)
  have h123 := (abs_sub_le
    (doubleFront D a (2^m) p j i k v)
    ((1/512:ℝ)*frontPoint D a (2^m) p i k v)
    (oldPoint D a m p k v/512)).trans (add_le_add h12 h3)
  linarith

/-- Every final-mesh source cube has an actual original-edge antecedent
whose unchanged rawPoint, after the fixed second homothety, is within mu
in each coordinate. This is a displacement bound, not point equality. -/
theorem final_center_rawPoint_error {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m : ℕ) (hm : 6 ≤ m) (hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ mu m)
    (p : Parent) (i j : Fin n) (k : Index) (hk : k∈original i)
    (hi : parentLabel D a (2^m) i=p)
    (hr : NativeRelativeParentLabels.relativeLabel D a (2^m) p (2^(m+6)) j=
      NativeRelativeParentLabels.relativeLabel D a (2^m) p (2^(m+6)) i) (v : Fin 4) :
    |cellCenter (mu m/2) (doubleLabel D a (2^m) (2^(m+6)) p j i k) v-
      rawPoint D a m p k v/512| ≤ mu m := by
  have hmu := mu_pos m
  have hmu1 : mu m≤1 := by
    unfold mu rho
    have hn : (1:ℝ)≤((2^m:ℕ):ℝ) := by exact_mod_cast (show 1≤2^m by positivity)
    have hp : (0:ℝ)<((2^m:ℕ):ℝ) := by positivity
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<64)).mpr
    exact (div_le_iff₀ hp).mpr (by nlinarith)
  have h1 := cell_center_coordinate_error (by positivity : 0<mu m/2)
    (doubleFront D a (2^m) p j i k) v
  have hlabel : doubleLabel D a (2^m) (2^(m+6)) p j i k=
      wzDyadicCellIndex (mu m/2) (doubleFront D a (2^m) p j i k) := by
    rw [doubleLabel,final_mesh]
  rw [←hlabel] at h1
  have h2 := double_front_oldPoint_error h original horiginal ha m (2^(m+6))
    (by positivity) (hscale.trans hmu1) p i j k hk hi hr v
  have hrnd := physical_rounding h m hm p i hi k
  have hc : |oldPoint D a m p k v-rawPoint D a m p k v| ≤ 128*mu m := by
    have hh := PiLp.dist_apply_le (rawPoint D a m p k) (oldPoint D a m p k) v
    have hh' : |oldPoint D a m p k v-rawPoint D a m p k v| ≤
        dist (rawPoint D a m p k) (oldPoint D a m p k) := by
      simpa only [Real.dist_eq,abs_sub_comm] using hh
    exact hh'.trans hrnd
  have h3 : |oldPoint D a m p k v/512-rawPoint D a m p k v/512| ≤ (128*mu m)/512 := by
    rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    exact div_le_div_of_nonneg_right hc (by norm_num)
  have h12 := (abs_sub_le
    (cellCenter (mu m/2) (doubleLabel D a (2^m) (2^(m+6)) p j i k) v)
    (doubleFront D a (2^m) p j i k v) (oldPoint D a m p k v/512)).trans (add_le_add h1 h2)
  have h123 := (abs_sub_le
    (cellCenter (mu m/2) (doubleLabel D a (2^m) (2^(m+6)) p j i k) v)
    (oldPoint D a m p k v/512) (rawPoint D a m p k v/512)).trans (add_le_add h12 h3)
  have hs : 1/(64*((2^(m+6):ℕ):ℝ))=mu m/4096 := by rw [←final_scale m]; ring
  rw [hs] at h123
  dsimp only [localMesh] at h123
  linarith

end NativeCurrentSourceGeometry
