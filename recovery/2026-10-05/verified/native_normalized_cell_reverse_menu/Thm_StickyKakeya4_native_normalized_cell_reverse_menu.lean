import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeNormalizedCellReverseMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeRelativeParentLabels NativeRelativeCoarseGeometry
open NativeRelativeCoarsePointMenu NativeNormalizedCellRelativeMenu NativeAnisotropicShortRowGeometry

/-- The inverse menu pays only the fixed contraction ratio. It does not
identify a relative projected point with the physical point. -/
def reverseMenu (M : ℕ) (q : Index) : Finset Index :=
  columnHalo 137 137 (wzDyadicCellIndex (64/(M:ℝ)) ((512:ℝ) • cellCenter (32/(M:ℝ)) q))

lemma reverseMenu_card (M : ℕ) (q : Index) : (reverseMenu M q).card=275^4 := by
  rw [reverseMenu,columnHalo_card]
  norm_num

theorem physical_cell_mem_reverse {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hNscale : (N:ℝ)*D.thickness ≤ 1) (hRelScale : (N:ℝ)*D.thickness*(M:ℝ) ≤ 64)
    (p : Parent) (i j : Fin n) (k : Index) (hk : k∈original i)
    (hp : parentLabel D a N i=p)
    (hr : relativeLabel D a N p M j=relativeLabel D a N p M i) :
    physicalCell D a N M p k∈reverseMenu M (doubleLabel D a N M p j i k) := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  apply Fintype.mem_piFinset.mpr
  intro v
  simp only [ite_self]
  change ⌊physicalPoint D a N p k v/(64/(M:ℝ))⌋∈
    Icc (⌊((512:ℝ) • cellCenter (32/(M:ℝ)) (doubleLabel D a N M p j i k)) v/(64/(M:ℝ))⌋-137)
      (⌊((512:ℝ) • cellCenter (32/(M:ℝ)) (doubleLabel D a N M p j i k)) v/(64/(M:ℝ))⌋+137)
  apply NativeSpatialAngularGeometry.floor_mem_interval 136
  rw [←sub_div,abs_div,abs_of_pos (by positivity : (0:ℝ)<64/(M:ℝ))]
  apply (div_le_iff₀ (by positivity)).mpr
  have h1 := double_front_physical_error h original horiginal ha N M hN hM hNscale hRelScale p i j k hk hp hr v
  rw [abs_sub_comm] at h1
  have h2 := cell_center_coordinate_error (by positivity : (0:ℝ)<32/(M:ℝ)) (doubleFront D a N p j i k) v
  rw [abs_sub_comm] at h2
  have hh := (abs_sub_le (physicalPoint D a N p k v/512) (doubleFront D a N p j i k v)
    (cellCenter (32/(M:ℝ)) (doubleLabel D a N M p j i k) v)).trans (add_le_add h1 h2)
  have hi : physicalPoint D a N p k v-
      ((512:ℝ) • cellCenter (32/(M:ℝ)) (doubleLabel D a N M p j i k)) v=
      512*(physicalPoint D a N p k v/512-cellCenter (32/(M:ℝ)) (doubleLabel D a N M p j i k) v) := by
    simp only [PiLp.smul_apply,smul_eq_mul]
    ring
  rw [hi,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<512)]
  have hbound := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤512)
  have he : 512*(1/(M:ℝ)+(32/(M:ℝ))/2)=(136:ℝ)*(64/(M:ℝ)) := by ring
  simpa only [he,Nat.cast_ofNat] using hbound

end NativeNormalizedCellReverseMenu
