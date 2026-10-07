import Theorems.Thm_StickyKakeya4_native_relative_coarse_readback
import Theorems.Thm_StickyKakeya4_native_local_cell_coherence
import Theorems.Thm_StickyKakeya4_native_anisotropic_short_row_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000

noncomputable section
namespace NativeNormalizedCellRelativeMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeOriginalParentPhysicalData
open NativeLocalParentGeometry NativeLocalParentPhysicalMap NativeRelativeParentLabels
open NativeRelativeCoarseGeometry NativeRelativeCoarsePointMenu NativeRelativeCoarseReadback
open NativeLocalCellCoherence NativeAnisotropicShortRowGeometry

def physicalPoint {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent)
    (k : Index) : E4 := physicalMap D a N p (cellCenter (mesh D) k)

def physicalCell {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N M : ℕ) (p : Parent)
    (k : Index) : Index := wzDyadicCellIndex (64/(M:ℝ)) (physicalPoint D a N p k)

lemma zero_local_front {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (i : Fin n) (k : Index) (v : Fin 4) :
    zeroGraphPoint (NativeLocalParentGeometry.line D a N p i)
      (NativeLocalParentCells.frontPoint D a N p i k (3:Fin 4)) v=
      NativeLocalParentCells.frontPoint D a N p i k v/512 := by
  refine Fin.lastCases ?_ (fun j => ?_) v
  · rfl
  · rw [NativeLocalParentCells.frontPoint_height]
    simp only [zeroGraphPoint,ActualSlopeSource.heightPoint_castSucc,
      actual_local_intercept,slope_line,
      NativeLocalParentCells.frontPoint,NativeContractedUnitParent.contractPoint,
      PiLp.smul_apply,PiLp.add_apply,smul_eq_mul]
    ring

/-- Exact original geometry relates the existing doubleFront to the common
physical point after its second fixed contraction. The 512 factor is kept. -/
theorem double_front_physical_error {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hNscale : (N:ℝ)*D.thickness ≤ 1) (hRelScale : (N:ℝ)*D.thickness*(M:ℝ) ≤ 64)
    (p : Parent) (i j : Fin n) (k : Index) (hk : k∈original i)
    (hp : parentLabel D a N i=p)
    (hr : relativeLabel D a N p M j=relativeLabel D a N p M i) (v : Fin 4) :
    |doubleFront D a N p j i k v-physicalPoint D a N p k v/512| ≤ 1/(M:ℝ) := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hd := h.1.2.1
  have ht := (original_cell_bounds h original horiginal a ha ((mem_incidences original i k).mpr hk)).1
  change |NativeOriginalPaddedCells.oldTime D a k| ≤ 1 at ht
  have h1 := same_relative_front_error D a N M hM p i j hr
    (roundedHeight D a N p i k) (rounded_height_bound hd a N hN hNscale p i k ht) v
  have h2 := zero_graph_time_error (NativeLocalParentGeometry.line D a N p i)
    (fun u => by rw [slope_line]; exact localSlope_bound D a N p i hp u)
    (roundedHeight D a N p i k) (NativeLocalParentCells.frontPoint D a N p i k (3:Fin 4)) v
  rw [zero_local_front] at h2
  have h2b := h2.trans (div_le_div_of_nonneg_right (rounded_height_error hd a N hN p i k) (by norm_num))
  have h3 : |NativeLocalParentCells.frontPoint D a N p i k v/512-physicalPoint D a N p k v/512| ≤
      ((3/2:ℝ)*localMesh D N)/512 := by
    rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    exact div_le_div_of_nonneg_right (frontPoint_near_physicalCell h original horiginal ha N p i k hk v) (by norm_num)
  have h12 := (abs_sub_le (doubleFront D a N p j i k v)
    (zeroGraphPoint (NativeLocalParentGeometry.line D a N p i) (roundedHeight D a N p i k) v)
    (NativeLocalParentCells.frontPoint D a N p i k v/512)).trans (add_le_add h1 h2b)
  have h123 := (abs_sub_le (doubleFront D a N p j i k v)
    (NativeLocalParentCells.frontPoint D a N p i k v/512)
    (physicalPoint D a N p k v/512)).trans (add_le_add h12 h3)
  have hmesh : localMesh D N ≤ 1/(2*(M:ℝ)) := by
    unfold localMesh
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hRelScale]
  have hpositive : 0 < 1/(M:ℝ) := by positivity
  have he : 1/(64*(M:ℝ))=(1/(M:ℝ))/64 := by ring
  rw [he] at h123
  have hm : localMesh D N ≤ (1/(M:ℝ))/2 := by simpa only [div_div,mul_comm] using hmesh
  linarith only [h123,hm,hpositive]

/-- An actual rho=64/M physical cube has a fixed 81-cell relative menu.
Relative projected cells have width rho/2 AFTER the extra 1/512 contraction. -/
def forwardMenu (M : ℕ) (q : Index) : Finset Index :=
  columnHalo 1 1 (wzDyadicCellIndex (32/(M:ℝ)) ((1/512:ℝ) • cellCenter (64/(M:ℝ)) q))

lemma forwardMenu_card (M : ℕ) (q : Index) : (forwardMenu M q).card=81 := by
  rw [forwardMenu,columnHalo_card]
  norm_num

theorem double_label_mem_forward {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hNscale : (N:ℝ)*D.thickness ≤ 1) (hRelScale : (N:ℝ)*D.thickness*(M:ℝ) ≤ 64)
    (p : Parent) (i j : Fin n) (k : Index) (hk : k∈original i)
    (hp : parentLabel D a N i=p)
    (hr : relativeLabel D a N p M j=relativeLabel D a N p M i) :
    doubleLabel D a N M p j i k∈forwardMenu M (physicalCell D a N M p k) := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  apply Fintype.mem_piFinset.mpr
  intro v
  simp only [ite_self]
  change ⌊doubleFront D a N p j i k v/(32/(M:ℝ))⌋∈
    Icc (⌊((1/512:ℝ) • cellCenter (64/(M:ℝ)) (physicalCell D a N M p k)) v/(32/(M:ℝ))⌋-1)
      (⌊((1/512:ℝ) • cellCenter (64/(M:ℝ)) (physicalCell D a N M p k)) v/(32/(M:ℝ))⌋+1)
  apply NativeCoarseScaleInterpolation.floor_close (by positivity)
  have h1 := double_front_physical_error h original horiginal ha N M hN hM hNscale hRelScale p i j k hk hp hr v
  have h2 : |physicalPoint D a N p k v/512-
      ((1/512:ℝ) • cellCenter (64/(M:ℝ)) (physicalCell D a N M p k)) v| ≤ (1/(M:ℝ))/16 := by
    simp only [PiLp.smul_apply,smul_eq_mul]
    rw [show physicalPoint D a N p k v/512-(1/512:ℝ)*cellCenter (64/(M:ℝ))
      (physicalCell D a N M p k) v=(physicalPoint D a N p k v-cellCenter (64/(M:ℝ))
      (physicalCell D a N M p k) v)/512 by ring,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    have hh := cell_center_coordinate_error (by positivity : (0:ℝ)<64/(M:ℝ)) (physicalPoint D a N p k) v
    rw [abs_sub_comm] at hh
    have hh' := div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ)≤512)
    simpa only [physicalCell] using hh' |>.trans_eq (by ring)
  have hh := (abs_sub_le (doubleFront D a N p j i k v) (physicalPoint D a N p k v/512)
    (((1/512:ℝ) • cellCenter (64/(M:ℝ)) (physicalCell D a N M p k)) v)).trans (add_le_add h1 h2)
  have he : 32/(M:ℝ)=32*(1/(M:ℝ)) := by ring
  rw [he]
  linarith only [hh,show 0 < 1/(M:ℝ) by positivity]

end NativeNormalizedCellRelativeMenu
