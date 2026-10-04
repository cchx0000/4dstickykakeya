import Theorems.Thm_StickyKakeya4_native_local_parent_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeLocalParentCells
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentPhysicalData
open NativeContractedUnitParent NativeLocalParentGeometry

/-- Original cell heights are kept by the local anisotropic normalization. -/
def frontPoint {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent)
    (i : Fin n) (k : Index) : E4 :=
  contractPoint (ActualSlopeSource.heightPoint
    (localIntercept D a N p i + (NativeOriginalPaddedCells.oldTime D a k/4) • localSlope D N p i)
    (NativeOriginalPaddedCells.oldTime D a k/4))
def cellLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent)
    (i : Fin n) (k : Index) : Index :=
  wzDyadicCellIndex ((N:ℝ)*D.thickness/128) (frontPoint D a N p i k)
def cells {n : ℕ} (D : FiniteScaleSource n) (original : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) (i : Fin n) : Finset Index :=
  (original i).image (cellLabel D a N p i)

lemma frontPoint_mem_front {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p)
    (k : Index) (hk : k∈original i) :
    frontPoint D a N p i k∈unitFront {NativeLocalParentGeometry.line D a N p i} := by
  have ht := (original_cell_bounds h original horiginal a ha ((mem_incidences original i k).mpr hk)).1
  have hf := NativeGraphMarkedLine.graphPoint_mem_unitFront
    (localSlope D N p i) (localIntercept D a N p i) 0
    (NativeOriginalPaddedCells.oldTime D a k/4) (localSlope_bound D a N p i hp) (by
      rw [sub_zero,abs_div]
      norm_num
      change |NativeOriginalPaddedCells.oldTime D a k| ≤ 1 at ht
      linarith)
  exact contract_front _ (Set.mem_image_of_mem contractPoint hf)

theorem cells_meet_front {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p)
    (q : Index) (hq : q∈cells D original a N p i) :
    ∃t : Set.Icc (-(1/2:ℝ)) (1/2:ℝ),
      rawFrontParam (NativeLocalParentGeometry.line D a N p i,(t:ℝ))∈
        wzDyadicCell ((N:ℝ)*D.thickness/128) q := by
  obtain ⟨k,hk,rfl⟩ := mem_image.mp hq
  obtain ⟨l,hl,t,ht,he⟩ := frontPoint_mem_front h original horiginal ha N p i hp k hk
  have hl' : l=NativeLocalParentGeometry.line D a N p i := by simpa using hl
  subst l
  refine ⟨⟨t,ht⟩,?_⟩
  have hcell := mem_wzDyadicCell_index
    (show 0 < (N:ℝ)*D.thickness/128 by have hd:=h.1.2.1; positivity) (frontPoint D a N p i k)
  simpa only [cellLabel,he,rawFrontParam] using hcell

/-- Actual front-meeting cubes have exactly half the local output thickness. -/
theorem shading_subset_tube {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p) :
    wzCellShading ((N:ℝ)*D.thickness/128) (cells D original a N p) i⊆
      markedUnitTube (NativeLocalParentGeometry.line D a N p i) ((N:ℝ)*D.thickness/64) := by
  have hd : 0 < (N:ℝ)*D.thickness/128 := by have hh:=h.1.2.1; positivity
  have hh := wzDyadicCells_meeting_markedLine_subset_two_mul_tube
    (NativeLocalParentGeometry.line D a N p i) hd (cells D original a N p i)
    (cells_meet_front h original horiginal ha N hN p i hp)
  simpa only [wzCellShading,show 2*((N:ℝ)*D.thickness/128)=(N:ℝ)*D.thickness/64 by ring] using hh

lemma frontPoint_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent)
    (i : Fin n) (k : Index) :
    frontPoint D a N p i k (3:Fin 4)=NativeOriginalPaddedCells.oldTime D a k/128 := by
  unfold frontPoint contractPoint
  rw [PiLp.smul_apply,smul_eq_mul]
  rw [show (3:Fin 4)=Fin.last 3 by rfl,ActualSlopeSource.heightPoint_last]
  ring

/-- Literal integer row fibers are8N original rows. This is not a new
height-separation hypothesis or a relabeling of the original delta. -/
lemma cellLabel_height {n : ℕ} {D : FiniteScaleSource n} (hd : 0 < D.thickness)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) (k : Index) :
    cellLabel D a N p i k (3:Fin 4)=(k (3:Fin 4)-shift D a)/(8*N:ℕ) := by
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  change ⌊frontPoint D a N p i k (3:Fin 4)/((N:ℝ)*D.thickness/128)⌋=_
  rw [frontPoint_height]
  have he : (NativeOriginalPaddedCells.oldTime D a k/128)/((N:ℝ)*D.thickness/128)=
      ((k (3:Fin 4):ℝ)-(shift D a:ℝ)+1/2)/(8*(N:ℝ)) := by
    dsimp [NativeOriginalPaddedCells.oldTime,ShearBinFibers.oldCenter,chartIndex,mesh]
    push_cast
    field_simp [hd.ne',hNr]
    ring
  rw [he]
  have hf := Int.floor_div_natCast (((k (3:Fin 4)-shift D a:ℤ):ℝ)+1/2) (8*N)
  have hx : ⌊(((k (3:Fin 4)-shift D a:ℤ):ℝ)+1/2)⌋=k (3:Fin 4)-shift D a := by
    rw [Int.floor_intCast_add]
    norm_num
  push_cast at hf hx ⊢
  rw [hf,hx]
end NativeLocalParentCells
