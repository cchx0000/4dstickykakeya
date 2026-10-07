import Theorems.Thm_StickyKakeya4_native_zero_parent_physical_map
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_points
import Theorems.Thm_StickyKakeya4_native_local_parent_source
import Theorems.Thm_StickyKakeya4_native_original_parent_physical_data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeReferenceZeroParentReadback
open StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeReferenceXYGridPoints NativeZeroParentPhysicalMap

/-- The actual third-source raw position receives the second contraction
when it is used with the full coarse source of a local reference source. -/
theorem rawPoint_readback {n n' : ℕ} (D : FiniteScaleSource n) (S : FiniteScaleSource n')
    (a : ℝ) (m : ℕ) (p : Parent) (k : Index) :
    NativeContractedUnitParent.physicalMap S 0 (0, 0) (rawPoint D a m p k) =
      (1 / 512 : ℝ) • rawPoint D a m p k := zero_map S _

/-- The genuine old-cell center uses the same second physical map. -/
theorem oldPoint_readback {n n' : ℕ} (D : FiniteScaleSource n) (S : FiniteScaleSource n')
    (a : ℝ) (m : ℕ) (p : Parent) (k : Index) :
    NativeContractedUnitParent.physicalMap S 0 (0, 0) (oldPoint D a m p k) =
      (1 / 512 : ℝ) • oldPoint D a m p k := zero_map S _

/-- Original phase rounding costs mu/4 after the second contraction. This
is an actual displacement between images of the same original point label. -/
theorem raw_old_displacement {n n' : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (S : FiniteScaleSource n')
    (m : ℕ) (hm : 6 ≤ m) (p : Parent) (i : Fin n)
    (hi : parentLabel D a (2 ^ m) i = p) (k : Index) :
    dist (NativeContractedUnitParent.physicalMap S 0 (0, 0) (rawPoint D a m p k))
      (NativeContractedUnitParent.physicalMap S 0 (0, 0) (oldPoint D a m p k)) ≤ mu m / 4 := by
  rw [zero_map_dist]
  have hh := physical_rounding h m hm p i hi k
  linarith only [hh]

/-- The genuine old-cell center belongs to its actual line in the local
reference source. This supplies the fine-tube input for the second coarse
containment argument, without claiming it for the rounded rawPoint. -/
theorem oldPoint_mem_local_source {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀ i, D.shading i = wzCellShading (mesh D) cells i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (R : Finset (Fin n)) (Eref : Finset (Fin n × Index)) (m : ℕ) (p : Parent)
    (i : Fin (NativeLocalParentSource.parentLabels D R a (2 ^ m) p).card) (k : Index)
    (hk : (NativePaddedCellSource.originalLabel
      (NativeLocalParentSource.parentLabels D R a (2 ^ m) p) i, k) ∈
        NativeCubicalIncidenceCounts.incidences cells) :
    oldPoint D a m p k ∈ markedUnitTube ((NativeLocalParentSource.source h R Eref a m p).line i)
      (NativeLocalParentSource.source h R Eref a m p).thickness := by
  have hp := (NativeLocalParentSource.mem_parentLabels D R a (2 ^ m) p _).mp
    (NativePaddedCellSource.originalLabel_mem
      (NativeLocalParentSource.parentLabels D R a (2 ^ m) p) i)
  have hcell := NativeOriginalParentPhysicalData.original_cell_in_tube h cells hcells hk
  have hdelta : 2 * mesh D = D.thickness := by unfold mesh; ring
  rw [hdelta] at hcell
  have hh := NativeLocalParentPhysicalMap.original_tube_maps h ha (2 ^ m) (by positivity) p _ hp.2
    (Set.mem_image_of_mem (NativeLocalParentPhysicalMap.physicalMap D a (2 ^ m) p) hcell)
  simpa only [oldPoint, NativeLocalParentSource.source_line, NativeLocalParentSource.source_thickness] using hh

end NativeReferenceZeroParentReadback
