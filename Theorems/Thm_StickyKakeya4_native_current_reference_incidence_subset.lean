import Theorems.Thm_StickyKakeya4_native_local_parent_source

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace NativeCurrentReferenceIncidenceSubset
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeCubicalIncidenceCounts

/-- Sparse original shading remains a literal subset of the admitted
reference's source cells, on the same full parent index set. -/
theorem source_cells_mono {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (T Eref : Finset (Fin n × Index)) (hTE : T ⊆ Eref)
    (a : ℝ) (N : ℕ) (p : Parent) (i : Fin (parentLabels D R a N p).card) :
    sourceCells D R T a N p i ⊆ sourceCells D R Eref a N p i := by
  intro q hq
  let j := NativePaddedCellSource.originalLabel (parentLabels D R a N p) i
  change q ∈ outputCells D T a N p j at hq
  change q ∈ outputCells D Eref a N p j
  obtain ⟨k,hk,he⟩ := (mem_outputCells D T a N p j q).mp hq
  exact (mem_outputCells D Eref a N p j q).mpr ⟨k,hTE hk,he⟩

/-- This is the subset premise of coarse selection on the admitted Eref
source. It needs no native-input proof for the sparse current T. -/
theorem source_incidences_mono {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (T Eref : Finset (Fin n × Index)) (hTE : T ⊆ Eref)
    (a : ℝ) (N : ℕ) (p : Parent) :
    incidences (sourceCells D R T a N p) ⊆ incidences (sourceCells D R Eref a N p) := by
  rintro ⟨i,k⟩ hik
  exact (mem_incidences _ i k).mpr
    (source_cells_mono D R T Eref hTE a N p i ((mem_incidences _ i k).mp hik))

end NativeCurrentReferenceIncidenceSubset
