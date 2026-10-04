import Theorems.Thm_StickyKakeya4_native_contracted_unit_parent
import Theorems.Thm_StickyKakeya4_native_original_parent_physical_data
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeOriginalPaddedCells
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentPhysicalData
open NativeUnitParentNormalization NativeContractedUnitParent

/-- The original common-height chart coordinate of the ORIGINAL shading cell. -/
def oldTime {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (k : Index) : ℝ :=
  (ShearBinFibers.oldCenter (mesh D/4) (chartIndex (shift D a) k)).2

/-- A genuine point of the new padded marked segment, with the ORIGINAL
shading cell's actual height. No artificial grid center is put on the line. -/
def frontPoint {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (p : Parent) (i : Fin n) (k : Index) : E4 :=
  contractPoint (ActualSlopeSource.heightPoint
    (newIntercept (D.line i) (mesh D) (shift D a) p +
      (oldTime D a k/4) • newSlope (D.line i) p) (oldTime D a k/4))
def cellLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (p : Parent) (i : Fin n) (k : Index) : Index :=
  wzDyadicCellIndex (D.thickness/128) (frontPoint D a p i k)
def cells {n : ℕ} (D : FiniteScaleSource n) (original : Fin n → Finset Index)
    (a : ℝ) (p : Parent) (i : Fin n) : Finset Index :=
  (original i).image (cellLabel D a p i)

lemma frontPoint_mem_front {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (p : Parent) (i : Fin n) (hp : parentLabel D a 1 i=p) (k : Index) (hk : k∈original i) :
    frontPoint D a p i k ∈ unitFront {NativeContractedUnitParent.line D a p i} := by
  have ht := (original_cell_bounds h original horiginal a ha ((mem_incidences original i k).mpr hk)).1
  have hb (j : Fin 3) : |newSlope (D.line i) p j| ≤ 1 := by
    have hh := (parameter_box D a p i hp).1 j
    exact abs_le.mpr ⟨by linarith [hh.1],hh.2.le⟩
  have hf := NativeGraphMarkedLine.graphPoint_mem_unitFront
    (newSlope (D.line i) p) (newIntercept (D.line i) (mesh D) (shift D a) p) 0
    (oldTime D a k/4) hb (by
      rw [sub_zero,abs_div]
      norm_num
      change |oldTime D a k| ≤ 1 at ht
      linarith)
  exact contract_front _ (Set.mem_image_of_mem contractPoint hf)

/-- Every selected output cube meets the actual new marked segment. -/
theorem cells_meet_front {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (p : Parent) (i : Fin n) (hp : parentLabel D a 1 i=p) (q : Index) (hq : q∈cells D original a p i) :
    ∃t : Set.Icc (-(1/2:ℝ)) (1/2:ℝ),
      rawFrontParam (NativeContractedUnitParent.line D a p i,(t:ℝ)) ∈ wzDyadicCell (D.thickness/128) q := by
  obtain ⟨k,hk,rfl⟩ := mem_image.mp hq
  obtain ⟨l,hl,t,ht,he⟩ := frontPoint_mem_front h original horiginal ha p i hp k hk
  have hl' : l=NativeContractedUnitParent.line D a p i := by simpa using hl
  subst l
  refine ⟨⟨t,ht⟩,?_⟩
  have hcell := mem_wzDyadicCell_index (show 0 < D.thickness/128 by have hd:=h.1.2.1; positivity)
    (frontPoint D a p i k)
  simpa only [cellLabel,he,rawFrontParam] using hcell

/-- The actual output cell shadings have the geometrically correct mesh
and lie inside the actual direction-separated output tubes. -/
theorem cell_shading_subset_contracted_tube {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (p : Parent) (i : Fin n) (hp : parentLabel D a 1 i=p) :
    wzCellShading (D.thickness/128) (cells D original a p) i ⊆
      markedUnitTube (NativeContractedUnitParent.line D a p i) (D.thickness/64) := by
  have hd : 0 < D.thickness/128 := by have hh:=h.1.2.1; positivity
  have hh := wzDyadicCells_meeting_markedLine_subset_two_mul_tube
    (NativeContractedUnitParent.line D a p i) hd (cells D original a p i)
    (cells_meet_front h original horiginal ha p i hp)
  simpa only [wzCellShading,show 2*(D.thickness/128)=D.thickness/64 by ring] using hh

lemma frontPoint_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (p : Parent)
    (i : Fin n) (k : Index) : frontPoint D a p i k (3:Fin 4)=oldTime D a k/128 := by
  unfold frontPoint contractPoint
  rw [PiLp.smul_apply,smul_eq_mul]
  rw [show (3:Fin 4)=Fin.last 3 by rfl,ActualSlopeSource.heightPoint_last]
  ring

/-- Exact dyadic height grouping: eight original rows occupy each output row. -/
lemma cellLabel_height {n : ℕ} {D : FiniteScaleSource n} (hd : 0 < D.thickness)
    (a : ℝ) (p : Parent) (i : Fin n) (k : Index) :
    cellLabel D a p i k (3:Fin 4)= (k (3:Fin 4)-shift D a)/8 := by
  change ⌊frontPoint D a p i k (3:Fin 4)/(D.thickness/128)⌋=_
  rw [frontPoint_height]
  have he : (oldTime D a k/128)/(D.thickness/128)=
      ((k (3:Fin 4):ℝ)-(shift D a:ℝ)+1/2)/8 := by
    dsimp [oldTime,ShearBinFibers.oldCenter,chartIndex,mesh]
    push_cast
    field_simp [hd.ne']
    ring
  rw [he]
  have hf := Int.floor_div_natCast (((k (3:Fin 4)-shift D a:ℤ):ℝ)+1/2) 8
  norm_num only [Nat.cast_ofNat] at hf
  have hx : ⌊(((k (3:Fin 4)-shift D a:ℤ):ℝ)+1/2)⌋=k (3:Fin 4)-shift D a := by
    rw [Int.floor_intCast_add]
    norm_num
  push_cast at hf
  rw [hf]
  push_cast at hx
  rw [hx]
end NativeOriginalPaddedCells
