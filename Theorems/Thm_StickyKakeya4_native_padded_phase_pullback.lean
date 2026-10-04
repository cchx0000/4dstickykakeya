import Theorems.Thm_StickyKakeya4_native_padded_cell_source
import Theorems.Thm_StickyKakeya4_native_padded_cell_fiber_count
import Theorems.Thm_StickyKakeya4_native_dyadic_coarse_normalization
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativePaddedPhasePullback
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativePaddedCellSource NativeOriginalCellChartGeometry NativeSourceCoarseReadback
variable {n : ℕ}
def paddedCells (D : FiniteScaleSource n) (original : Fin n → Finset Index)
    (Q : Finset (Fin n)) (a : ℝ) (p : Parent) (i : Fin Q.card) : Finset Index :=
  NativeOriginalPaddedCells.cells D original a p (originalLabel Q i)
def oldRows (original : Fin n → Finset Index) (Q : Finset (Fin n)) : Finset (Fin Q.card × Index) :=
  NativeCubicalIncidenceCounts.incidences (fun i => original (originalLabel Q i))
def paddingMap (D : FiniteScaleSource n) (Q : Finset (Fin n)) (a : ℝ) (p : Parent)
    (e : Fin Q.card × Index) : Fin Q.card × Index :=
  (e.1,NativeOriginalPaddedCells.cellLabel D a p (originalLabel Q e.1) e.2)
def selectedOldRows (D : FiniteScaleSource n) (original : Fin n → Finset Index)
    (Q : Finset (Fin n)) (a : ℝ) (p : Parent) (E : Finset (Fin Q.card × Index)) : Finset (Fin Q.card × Index) :=
  (oldRows original Q).filter (fun e => paddingMap D Q a p e ∈ E)
def originalRowMap (Q : Finset (Fin n)) (e : Fin Q.card × Index) : Fin n × Index :=
  (originalLabel Q e.1,e.2)
def originalPullback (D : FiniteScaleSource n) (original : Fin n → Finset Index)
    (Q : Finset (Fin n)) (a : ℝ) (p : Parent) (E : Finset (Fin Q.card × Index)) : Finset (Fin n × Index) :=
  (selectedOldRows D original Q a p E).image (originalRowMap Q)
lemma mem_selectedOldRows (D : FiniteScaleSource n) (original : Fin n → Finset Index)
    (Q : Finset (Fin n)) (a : ℝ) (p : Parent) (E : Finset (Fin Q.card × Index)) (e : Fin Q.card × Index) :
    e ∈ selectedOldRows D original Q a p E ↔
      e.2 ∈ original (originalLabel Q e.1) ∧ paddingMap D Q a p e ∈ E := by
  rcases e with ⟨i,k⟩
  simp only [selectedOldRows,oldRows,mem_filter,NativeCubicalIncidenceCounts.mem_incidences]
/-- Every selected padded incidence is the image of its complete original
 cell fiber, using the actual cellLabel map from the admitted source. -/
theorem padding_image (D : FiniteScaleSource n) (original : Fin n → Finset Index)
    (Q : Finset (Fin n)) (a : ℝ) (p : Parent) (E : Finset (Fin Q.card × Index))
    (hE : E ⊆ NativeCubicalIncidenceCounts.incidences (paddedCells D original Q a p)) :
    (selectedOldRows D original Q a p E).image (paddingMap D Q a p)=E := by
  ext e
  constructor
  · intro he
    obtain ⟨old,hold,rfl⟩ := mem_image.mp he
    exact (mem_selectedOldRows D original Q a p E old).mp hold |>.2
  · intro he
    rcases e with ⟨i,k⟩
    have hk := (NativeCubicalIncidenceCounts.mem_incidences (paddedCells D original Q a p) i k).mp (hE he)
    obtain ⟨old,hold,hlabel⟩ := mem_image.mp hk
    have hmap : paddingMap D Q a p (i,old)=(i,k) := Prod.ext rfl hlabel
    exact mem_image.mpr ⟨(i,old),(mem_selectedOldRows D original Q a p E (i,old)).mpr
      ⟨hold,hmap.symm ▸ he⟩,hmap⟩
lemma originalRowMap_injective (Q : Finset (Fin n)) : Function.Injective (originalRowMap Q) := by
  intro e f hef
  have hfst := congrArg (fun z : Fin n × Index => z.1) hef
  have hsnd : e.2=f.2 := by
    simpa only [originalRowMap] using congrArg (fun z : Fin n × Index => z.2) hef
  exact Prod.ext (originalLabel_injective Q hfst) hsnd
/-- The pullback uses only actual original cubical incidences and retained
 original tube labels. Removed labels are never restored. -/
theorem original_pullback_readback (D : FiniteScaleSource n) (original : Fin n → Finset Index)
    (Q : Finset (Fin n)) (a : ℝ) (p : Parent) (E : Finset (Fin Q.card × Index)) :
    originalPullback D original Q a p E ⊆ NativeCubicalIncidenceCounts.incidences original ∧
      (originalPullback D original Q a p E).image Prod.fst ⊆ Q ∧
      (originalPullback D original Q a p E).card=(selectedOldRows D original Q a p E).card := by
  refine ⟨?_,?_,card_image_of_injective _ (originalRowMap_injective Q)⟩
  · intro e he
    obtain ⟨old,hold,rfl⟩ := mem_image.mp he
    exact (NativeCubicalIncidenceCounts.mem_incidences original _ _).mpr
      ((mem_selectedOldRows D original Q a p E old).mp hold).1
  · intro i hi
    obtain ⟨e,he,rfl⟩ := mem_image.mp hi
    obtain ⟨old,_hold,rfl⟩ := mem_image.mp he
    exact originalLabel_mem Q old.1
/-- The actual whole original preimage has the proved padded-cell capacity.
 No retained-fiber population bound is assumed. -/
theorem selected_old_card_le {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀ i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (Q : Finset (Fin n)) (p : Parent) (E : Finset (Fin Q.card × Index)) :
    (selectedOldRows D original Q a p E).card ≤ 175616*E.card := by
  let S := selectedOldRows D original Q a p E
  apply card_le_mul_card_image_of_maps_to
    (f := paddingMap D Q a p) (t := E)
    (fun e he => ((mem_selectedOldRows D original Q a p E e).mp he).2) 175616
  intro v _hv
  let F := S.filter (fun e => paddingMap D Q a p e=v)
  let B := (original (originalLabel Q v.1)).filter
    (fun k => NativeOriginalPaddedCells.cellLabel D a p (originalLabel Q v.1) k=v.2)
  have hm : Set.MapsTo Prod.snd (F:Set (Fin Q.card × Index)) (B:Set Index) := by
    intro e he
    obtain ⟨heS,hev⟩ := mem_filter.mp he
    have hrow := (mem_selectedOldRows D original Q a p E e).mp heS |>.1
    have hi : e.1=v.1 := by
      simpa only [paddingMap] using congrArg (fun z : Fin Q.card × Index => z.1) hev
    have hk := congrArg Prod.snd hev
    change NativeOriginalPaddedCells.cellLabel D a p (originalLabel Q e.1) e.2=v.2 at hk
    rw [hi] at hrow hk
    exact mem_filter.mpr ⟨hrow,hk⟩
  have hi : Set.InjOn Prod.snd (F:Set (Fin Q.card × Index)) := by
    intro e he f hf hef
    have h1 : e.1=v.1 := by
      simpa only [paddingMap] using congrArg (fun z : Fin Q.card × Index => z.1) (mem_filter.mp he).2
    have h2 : f.1=v.1 := by
      simpa only [paddingMap] using congrArg (fun z : Fin Q.card × Index => z.1) (mem_filter.mp hf).2
    exact Prod.ext (h1.trans h2.symm) hef
  exact (card_le_card_of_injOn Prod.snd hm hi).trans
    (NativePaddedCellFiberCount.output_cell_fiber_card_le h original horiginal ha p (originalLabel Q v.1) v.2)
def phaseFamily (Q : Finset (Fin n)) (P : PhysicalRescalingIncidenceTransfer.Data (Fin Q.card))
    (shiftNew : ℤ) (E : Finset (Fin Q.card × Index)) : Finset (ShearBinFibers.Index × Fin n) :=
  (originalFamily P shiftNew E).image (fun e => (e.1,originalLabel Q e.2))
def compositeMap (D : FiniteScaleSource n) (Q : Finset (Fin n)) (a : ℝ) (p : Parent)
    (P : PhysicalRescalingIncidenceTransfer.Data (Fin Q.card)) (shiftNew : ℤ)
    (e : Fin Q.card × Index) : ShearBinFibers.Index × Fin n :=
  (P.cellBin (chartIndex shiftNew (NativeOriginalPaddedCells.cellLabel D a p (originalLabel Q e.1) e.2)),
    originalLabel Q e.1)
/-- Exact original incidence-to-padded-cell-to-chart-to-coarse-cell image.
 This composes the two distinct geometric maps instead of equating records. -/
theorem phase_original_image (D : FiniteScaleSource n) (original : Fin n → Finset Index)
    (Q : Finset (Fin n)) (a : ℝ) (p : Parent) (E : Finset (Fin Q.card × Index))
    (hE : E ⊆ NativeCubicalIncidenceCounts.incidences (paddedCells D original Q a p))
    (P : PhysicalRescalingIncidenceTransfer.Data (Fin Q.card)) (shiftNew : ℤ) :
    phaseFamily Q P shiftNew E=
      (selectedOldRows D original Q a p E).image (compositeMap D Q a p P shiftNew) := by
  have hp := padding_image D original Q a p E hE
  calc
    _ = phaseFamily Q P shiftNew ((selectedOldRows D original Q a p E).image (paddingMap D Q a p)) :=
      congrArg (phaseFamily Q P shiftNew) hp.symm
    _ = _ := by
      simp only [phaseFamily,originalFamily,image_image]
      apply image_congr
      intro e _he
      rfl
/-- A literal physical height window is the image of its entire original
cubical preimage through the same padding/chart/bin composition. -/
theorem phase_height_window_original_image (D : FiniteScaleSource n)
    (original : Fin n → Finset Index) (Q : Finset (Fin n)) (a : ℝ) (p : Parent)
    (E : Finset (Fin Q.card × Index))
    (hE : E ⊆ NativeCubicalIncidenceCounts.incidences (paddedCells D original Q a p))
    (P : PhysicalRescalingIncidenceTransfer.Data (Fin Q.card)) (shiftNew : ℤ) (R lo width : ℝ) :
    ((selectedOldRows D original Q a p E).filter (fun e =>
      lo ≤ NativeCoarseOriginalIncidences.height P R (compositeMap D Q a p P shiftNew e).1 ∧
      NativeCoarseOriginalIncidences.height P R (compositeMap D Q a p P shiftNew e).1 ≤ lo+width)).image
      (compositeMap D Q a p P shiftNew) =
    (phaseFamily Q P shiftNew E).filter (fun e =>
      lo ≤ NativeCoarseOriginalIncidences.height P R e.1 ∧
      NativeCoarseOriginalIncidences.height P R e.1 ≤ lo+width) := by
  rw [phase_original_image D original Q a p E hE P shiftNew]
  rw [filter_image]
/-- Relabeling with the injective originalLabel map preserves actual edge
 cardinalities, even though the physical point map is a genuine composition. -/
theorem phaseFamily_card (Q : Finset (Fin n)) (P : PhysicalRescalingIncidenceTransfer.Data (Fin Q.card))
    (shiftNew : ℤ) (E : Finset (Fin Q.card × Index)) :
    (phaseFamily Q P shiftNew E).card=(originalFamily P shiftNew E).card := by
  apply card_image_of_injective
  intro e f hef
  have hx := congrArg (fun z : ShearBinFibers.Index × Fin n => z.1) hef
  have ht := congrArg (fun z : ShearBinFibers.Index × Fin n => z.2) hef
  exact Prod.ext hx (originalLabel_injective Q ht)
/-- Original tube labels in the actual composite family are read back
 exactly, with no assumption that all full-backbone labels are incident. -/
theorem phaseFamily_tubes (Q : Finset (Fin n)) (P : PhysicalRescalingIncidenceTransfer.Data (Fin Q.card))
    (shiftNew : ℤ) (E : Finset (Fin Q.card × Index)) :
    TwoTubePathCollisionCount.tubes (phaseFamily Q P shiftNew E)=(E.image Prod.fst).image (originalLabel Q) := by
  simp only [TwoTubePathCollisionCount.tubes,phaseFamily,originalFamily,image_image]
  ext i
  simp only [mem_image,Function.comp_apply]
/-- The composed ORIGINAL cell fiber loses exactly the proved padding cap
 followed by the proved N-row phase capacity. -/
theorem original_composite_capacity {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀ i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (Q : Finset (Fin n)) (p : Parent) (E : Finset (Fin Q.card × Index))
    (P : PhysicalRescalingIncidenceTransfer.Data (Fin Q.card)) (hP : P.Hypotheses)
    (shiftNew : ℤ) (hE : chartFamily shiftNew E ⊆ P.incidences) :
    (originalPullback D original Q a p E).card ≤ 175616*P.N*(phaseFamily Q P shiftNew E).card := by
  rw [(original_pullback_readback D original Q a p E).2.2,phaseFamily_card]
  calc
    _ ≤ 175616*E.card := selected_old_card_le h original horiginal ha Q p E
    _ ≤ 175616*(P.N*(originalFamily P shiftNew E).card) :=
      Nat.mul_le_mul_left _ (original_capacity P hP shiftNew E hE)
    _ = _ := (Nat.mul_assoc _ _ _).symm
/-- The admitted source's actual cubes have exactly the common mesh needed
 by the subsequent generic phase constructor. -/
theorem admitted_source_cells {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (Q : Finset (Fin n)) (a : ℝ) (p : Parent) (hp : ∀ i ∈ Q,parentLabel D a 1 i=p) :
    ∀ i,(source h original Q a p hp).shading i=
      wzCellShading (mesh (source h original Q a p hp)) (paddedCells D original Q a p) i := by
  intro i
  have hm : mesh (source h original Q a p hp)=D.thickness/128 := by
    unfold mesh
    rw [source_thickness]
    ring
  rw [hm]
  rfl
/-- The two actual normalizations have the honest composed dyadic mesh.
 No identification with the original-source R=32 family is asserted. -/
theorem admitted_phase_mesh {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (Q : Finset (Fin n)) (a : ℝ) (p : Parent) (hp : ∀ i ∈ Q,parentLabel D a 1 i=p)
    (phaseTime : ℝ) (N : ℕ) (phaseParent : Parent) :
    (data (source h original Q a p hp) (paddedCells D original Q a p) phaseTime N phaseParent).σ/32=
      (N:ℝ)*D.thickness/16384 := by
  rw [NativeDyadicCoarseNormalization.native_dyadic_scale,source_thickness]
  ring
/-- The actual composite point retains its normalized height, window, and
residual bounds. The original tube label has an explicit witness in the
admitted source, so transformed slopes are never replaced by old slopes. -/
theorem admitted_phase_geometry {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (Q : Finset (Fin n)) (a : ℝ) (p : Parent) (hp : ∀ i ∈ Q,parentLabel D a 1 i=p)
    (phaseTime : ℝ) (N : ℕ) (phaseParent : Parent)
    (E : Finset (Fin Q.card × Index))
    (hP : (data (source h original Q a p hp) (paddedCells D original Q a p)
      phaseTime N phaseParent).Hypotheses)
    (hE : chartFamily (shift (source h original Q a p hp) phaseTime) E ⊆
      (data (source h original Q a p hp) (paddedCells D original Q a p) phaseTime N phaseParent).incidences) :
    let S := source h original Q a p hp
    let P := data S (paddedCells D original Q a p) phaseTime N phaseParent
    ∀ e ∈ phaseFamily Q P (shift S phaseTime) E, ∃ i : Fin Q.card,
      originalLabel Q i=e.2 ∧
      |NativeCoarseOriginalIncidences.height P 32 e.1| ≤ 1 ∧
      (∀ j, |(NativeCoarseOriginalIncidences.coordinates P 32 e.1).1 j| ≤ 1) ∧
      (∀ j, |(NativeCoarseOriginalIncidences.coordinates P 32 e.1).1 j-P.offset i j/32-
        P.slope i j*NativeCoarseOriginalIncidences.height P 32 e.1| ≤
          13*((N:ℝ)*D.thickness/16384)) := by
  let S := source h original Q a p hp
  let P := data S (paddedCells D original Q a p) phaseTime N phaseParent
  change ∀ e ∈ phaseFamily Q P (shift S phaseTime) E, _
  intro e he
  obtain ⟨f,hf,rfl⟩ := mem_image.mp he
  refine ⟨f.2,rfl,?_⟩
  have hg := native_original_geometry S (paddedCells D original Q a p) phaseTime N phaseParent hP E hE f hf
  have hnorm : NativeCoarseOriginalGeometry.normalization P=28 :=
    (native_scale_readback S (paddedCells D original Q a p) phaseTime N phaseParent).2.1
  have hscale : P.σ/NativeCoarseOriginalGeometry.normalization P=(N:ℝ)*S.thickness/224 :=
    (native_scale_readback S (paddedCells D original Q a p) phaseTime N phaseParent).2.2
  have hnew : P.σ/32=(N:ℝ)*D.thickness/16384 :=
    admitted_phase_mesh h original Q a p hp phaseTime N phaseParent
  have hb := NativeDyadicCoarseNormalization.larger_normalization_box P f.1
    (NativeCoarseOriginalGeometry.normalization_pos P)
    (show NativeCoarseOriginalGeometry.normalization P ≤ 32 by rw [hnorm]; norm_num) hg.1 hg.2.1
  refine ⟨hb.1,hb.2,?_⟩
  intro j
  have hr : |(NativeCoarseOriginalIncidences.coordinates P (NativeCoarseOriginalGeometry.normalization P) f.1).1 j-
      P.offset f.2 j/NativeCoarseOriginalGeometry.normalization P-
      P.slope f.2 j*NativeCoarseOriginalIncidences.height P (NativeCoarseOriginalGeometry.normalization P) f.1| ≤
      13*(P.σ/NativeCoarseOriginalGeometry.normalization P) := by
    rw [hscale]
    exact hg.2.2 j
  have hh := NativeDyadicCoarseNormalization.larger_normalization_residual P f.1 f.2 j
    (NativeCoarseOriginalGeometry.normalization_pos P) (by norm_num : (0:ℝ)<32) hr
  rwa [hnew] at hh
end NativePaddedPhasePullback
