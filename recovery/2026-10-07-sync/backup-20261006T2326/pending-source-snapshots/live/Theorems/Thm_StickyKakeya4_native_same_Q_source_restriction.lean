import Theorems.Thm_StickyKakeya4_native_current_reference_readback
import Theorems.Thm_StickyKakeya4_native_current_reference_incidence_subset
import Theorems.Thm_StickyKakeya4_native_configured_output_pairs

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeSameQSourceRestriction
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeRelativeParentLabels NativeRelativeParentProfiles
open NativeCubicalIncidenceCounts NativeCoarseShadingCapacity

/-- Restrict original occurrences by their actual relative parent. -/
def restrict {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m b : ℕ) (p : Parent)
    (Q : Finset Parent) (T : Finset (Fin n × Index)) : Finset (Fin n × Index) :=
  T.filter (fun z => relativeLabel D a (2 ^ m) p (2 ^ b) z.1 ∈ Q)

/-- The original phase cut commutes with the literal source-cell map.
The fine native source and its complete tube index set remain fixed. -/
theorem source_cells_restrict {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (a : ℝ) (m b : ℕ) (p : Parent)
    (Q : Finset Parent) (i : Fin (parentLabels D R a (2 ^ m) p).card) :
    sourceCells D R (restrict D a m b p Q T) a (2 ^ m) p i =
      if parentLabel (source h R Eref a m p) 0 (2 ^ b) i ∈ Q then
        sourceCells D R T a (2 ^ m) p i else ∅ := by
  rw [source_parentLabel]
  let j := NativePaddedCellSource.originalLabel (parentLabels D R a (2 ^ m) p) i
  change outputCells D (restrict D a m b p Q T) a (2 ^ m) p j =
    if relativeLabel D a (2 ^ m) p (2 ^ b) j ∈ Q then
      outputCells D T a (2 ^ m) p j else ∅
  by_cases hj : relativeLabel D a (2 ^ m) p (2 ^ b) j ∈ Q
  · rw [if_pos hj]
    ext q
    constructor
    · intro hq
      obtain ⟨k, hk, he⟩ := (mem_outputCells D _ a (2 ^ m) p j q).mp hq
      exact (mem_outputCells D T a (2 ^ m) p j q).mpr
        ⟨k, (mem_filter.mp hk).1, he⟩
    · intro hq
      obtain ⟨k, hk, he⟩ := (mem_outputCells D T a (2 ^ m) p j q).mp hq
      exact (mem_outputCells D _ a (2 ^ m) p j q).mpr
        ⟨k, mem_filter.mpr ⟨hk, hj⟩, he⟩
  · rw [if_neg hj]
    apply eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨k, hk, _he⟩ := (mem_outputCells D _ a (2 ^ m) p j q).mp hq
    exact hj (mem_filter.mp hk).2

theorem source_incidences_restrict {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (a : ℝ) (m b : ℕ) (p : Parent)
    (Q : Finset Parent) :
    incidences (sourceCells D R (restrict D a m b p Q T) a (2 ^ m) p) =
      (incidences (sourceCells D R T a (2 ^ m) p)).filter
        (fun z => parentLabel (source h R Eref a m p) 0 (2 ^ b) z.1 ∈ Q) := by
  ext z
  rw [mem_incidences, mem_filter, mem_incidences,
    source_cells_restrict h R Eref T a m b p Q z.1]
  by_cases hz : parentLabel (source h R Eref a m p) 0 (2 ^ b) z.1 ∈ Q
  · simp [hz]
  · simp [hz]

/-- A retained coarse row is unchanged by keeping exactly its Q parents. -/
lemma rows_filter_parent {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N B : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (Q : Finset Parent)
    (q : Parent) (hq : q ∈ Q) :
    rows D a N B rep (E.filter (fun z => parentLabel D a N z.1 ∈ Q)) q =
      rows D a N B rep E q := by
  have he : (E.filter (fun z => parentLabel D a N z.1 ∈ Q)).filter
      (fun z => parentLabel D a N z.1 = q) =
      E.filter (fun z => parentLabel D a N z.1 = q) := by
    ext z
    simp only [mem_filter]
    constructor
    · exact fun hz => ⟨hz.1.1, hz.2⟩
    · intro hz
      exact ⟨⟨hz.1, by rw [hz.2]; exact hq⟩, hz.2⟩
  unfold rows coarse
  simp only [filter_image]
  change (((E.filter (fun z => parentLabel D a N z.1 ∈ Q)).filter
      (fun z => parentLabel D a N z.1 = q)).image (label D a N B rep)).image Prod.snd =
    ((E.filter (fun z => parentLabel D a N z.1 = q)).image (label D a N B rep)).image Prod.snd
  rw [he]

/-- The actual Q core uses identical cubical shading rows before and after
the original TQ restriction. This does not identify fine configured points
with the coarse shadow cells. -/
theorem source_rows_restrict {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (a : ℝ) (m b B : ℕ) (p : Parent)
    (Q : Finset Parent)
    (rep : Parent → Fin (parentLabels D R a (2 ^ m) p).card)
    (q : Parent) (hq : q ∈ Q) :
    rows (source h R Eref a m p) 0 (2 ^ b) B rep
        (incidences (sourceCells D R (restrict D a m b p Q T) a (2 ^ m) p)) q =
      rows (source h R Eref a m p) 0 (2 ^ b) B rep
        (incidences (sourceCells D R T a (2 ^ m) p)) q := by
  rw [source_incidences_restrict]
  exact rows_filter_parent _ _ _ _ _ _ Q q hq

end NativeSameQSourceRestriction
