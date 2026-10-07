import Theorems.Thm_StickyKakeya4_native_original_shading_restriction
import Theorems.Thm_StickyKakeya4_native_original_parent_density_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section
namespace NativeOriginalCellPresentationUnique
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts
open NativeLocalParentSource NativeOriginalParentDensityCore NativeOriginalParentSelection

/-- At positive mesh, the center of an original half-open cell reads back its
literal integer label from any finite cubical presentation. -/
theorem mem_cells_iff_center_mem {n : ℕ} {s : ℝ} (hs : 0 < s)
    (cells : Fin n → Finset Index) (i : Fin n) (k : Index) :
    k ∈ cells i ↔ cellCenter s k ∈ wzCellShading s cells i := by
  constructor
  · intro hk
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, cellCenter_mem hs k⟩⟩
  · intro hx
    simp only [wzCellShading, Set.mem_iUnion, mem_coe] at hx
    obtain ⟨l,hl,hxl⟩ := hx
    have hkl : k = l := by
      by_contra hne
      exact Set.disjoint_left.mp (wzDyadicCell_disjoint hs hne)
        (cellCenter_mem hs k) hxl
    simpa only [hkl] using hl

/-- A literal finite cubical presentation is unique at every positive mesh. -/
theorem cells_eq_of_shading_eq {n : ℕ} {s : ℝ} (hs : 0 < s)
    (cells cells' : Fin n → Finset Index)
    (H : ∀ i, wzCellShading s cells i = wzCellShading s cells' i) :
    cells = cells' := by
  funext i
  ext k
  rw [mem_cells_iff_center_mem hs cells i k,
    mem_cells_iff_center_mem hs cells' i k, H i]

/-- Presenting a restricted source with any newly chosen finite cell family
recovers the exact selected original cells, without changing any labels. -/
theorem restricted_cells_eq {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (F : Finset (Fin n × Index))
    (cells : Fin n → Finset Index)
    (H : ∀ i, (NativeOriginalShadingRestriction.source D F).shading i =
      wzCellShading (mesh (NativeOriginalShadingRestriction.source D F)) cells i) :
    cells = selectedCells F := by
  apply cells_eq_of_shading_eq (s := mesh D) (half_pos hd)
  intro i
  exact (H i).symm

theorem restricted_incidences_eq {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (F : Finset (Fin n × Index))
    (cells : Fin n → Finset Index)
    (H : ∀ i, (NativeOriginalShadingRestriction.source D F).shading i =
      wzCellShading (mesh (NativeOriginalShadingRestriction.source D F)) cells i) :
    incidences cells = F := by
  rw [restricted_cells_eq D hd F cells H, selected_incidences]

/-- Any literal incidence refinement chosen after reconstructing the source's
cell presentation remains inside the original cut. -/
theorem subset_original_cut {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (F E : Finset (Fin n × Index))
    (cells : Fin n → Finset Index)
    (H : ∀ i, (NativeOriginalShadingRestriction.source D F).shading i =
      wzCellShading (mesh (NativeOriginalShadingRestriction.source D F)) cells i)
    (hE : E ⊆ incidences cells) : E ⊆ F := by
  rwa [restricted_incidences_eq D hd F cells H] at hE

/-- In particular, the existing native core constructor cannot lose an
original rank or plane witness by choosing another cubical presentation. -/
theorem core_subset_original_cut {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (F E : Finset (Fin n × Index))
    (cells : Fin n → Finset Index)
    (H : ∀ i, (NativeOriginalShadingRestriction.source D F).shading i =
      wzCellShading (mesh (NativeOriginalShadingRestriction.source D F)) cells i)
    (R : Finset (Fin n)) (a eta zeta : ℝ) (d g L : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (scales : Fin g → ℕ)
    (hcore : IsCore (NativeOriginalShadingRestriction.source D F) cells R
      a eta zeta d g L Rel scales E) : E ⊆ F := by
  apply subset_original_cut D hd F E cells H
  exact hcore.1.trans (filter_subset _ _)

/-- Arbitrary predicates on the unchanged original tube/cell edge survive the
source presentation and its subsequent native core selection. -/
theorem core_preserves_original_predicate {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (F E : Finset (Fin n × Index))
    (cells : Fin n → Finset Index)
    (H : ∀ i, (NativeOriginalShadingRestriction.source D F).shading i =
      wzCellShading (mesh (NativeOriginalShadingRestriction.source D F)) cells i)
    (R : Finset (Fin n)) (a eta zeta : ℝ) (d g L : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (scales : Fin g → ℕ)
    (hcore : IsCore (NativeOriginalShadingRestriction.source D F) cells R
      a eta zeta d g L Rel scales E)
    (P : (Fin n × Index) → Prop) (hP : ∀ z ∈ F, P z) : ∀ z ∈ E, P z := by
  intro z hz
  exact hP z (core_subset_original_cut D hd F E cells H R a eta zeta d g L
    Rel scales hcore hz)

end NativeOriginalCellPresentationUnique
