import Theorems.Thm_StickyKakeya4_native_original_padded_cells
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace NativePaddedCellUnionBound
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentPhysicalData
open NativeUnitParentNormalization NativeContractedUnitParent NativeOriginalPaddedCells
open scoped BigOperators ENNReal

lemma frontPoint_coordinate_error {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (p : Parent)
    (i : Fin n) (k : Index) (j : Fin 3) :
    frontPoint D a p i k j.castSucc-physicalMap D a p (cellCenter (mesh D) k) j.castSucc =
      -((ShearBinFibers.oldCenter (mesh D/4) (chartIndex (shift D a) k)).1 j-
        shiftedIntercept (D.line i) (mesh D) (shift D a) j-
        slope (D.line i) j*oldTime D a k)/128 := by
  simp only [frontPoint,physicalMap,contractPoint,pointMap,
    ActualSlopeSource.heightPoint_castSucc,PiLp.smul_apply,PiLp.add_apply,smul_eq_mul]
  dsimp [newIntercept,newSlope,shiftedIntercept,oldTime,ShearBinFibers.oldCenter,chartIndex,cellCenter]
  push_cast
  ring

lemma physicalCell_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (p : Parent) (k : Index) :
    physicalMap D a p (cellCenter (mesh D) k) (3:Fin 4)=oldTime D a k/128 := by
  change (1/32:ℝ)*((cellCenter (mesh D) k (3:Fin 4)-(shift D a:ℝ)*mesh D)/16)=_
  rw [oldTime,chart_center_time]
  ring

lemma frontPoint_near_physicalCell {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (p : Parent) (i : Fin n) (k : Index) (hk : k∈original i) (j : Fin 4) :
    |frontPoint D a p i k j-physicalMap D a p (cellCenter (mesh D) k) j| ≤ 2*(D.thickness/128) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [show (Fin.last 3:Fin 4)=3 by rfl,frontPoint_height,physicalCell_height,sub_self,abs_zero]
    have hd:=h.1.2.1
    positivity
  · rw [frontPoint_coordinate_error,abs_div,abs_neg]
    have hh := (original_cell_bounds h original horiginal a ha ((mem_incidences original i k).mpr hk)).2 j
    change |(ShearBinFibers.oldCenter (mesh D/4) (chartIndex (shift D a) k)).1 j-
      shiftedIntercept (D.line i) (mesh D) (shift D a) j-slope (D.line i) j*oldTime D a k| ≤ 12*(mesh D/4) at hh
    norm_num
    dsimp [mesh] at hh ⊢
    nlinarith [h.1.2.1]

/-- A fixed menu in the ACTUAL output grid around the common affine image of
one original spatial cell, shared by every original tube incident to it. -/
def neighborBox (e : ℝ) (x : E4) : Finset Index :=
  Fintype.piFinset (fun j => Icc (⌊x j/e⌋-2) (⌊x j/e⌋+2))

lemma neighborBox_card (e : ℝ) (x : E4) : (neighborBox e x).card=625 := by
  have hi (j : Fin 4) : (Icc (⌊x j/e⌋-2) (⌊x j/e⌋+2)).card=5 := by
    have hh : ((Icc (⌊x j/e⌋-2) (⌊x j/e⌋+2)).card:ℤ)=5 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simp [neighborBox,Fintype.card_piFinset,hi]

lemma cellIndex_mem_neighborBox {e : ℝ} (he : 0 < e) (x y : E4)
    (hxy : ∀j,|x j-y j| ≤ 2*e) : wzDyadicCellIndex e x∈neighborBox e y := by
  apply Fintype.mem_piFinset.mpr
  intro j
  have ha := abs_le.mp (hxy j)
  have hlo : y j/e-1-1 ≤ x j/e := by
    apply (le_div_iff₀ he).mpr
    field_simp [he.ne']
    nlinarith
  have hhi : x j/e ≤ y j/e+1+1 := by
    apply (div_le_iff₀ he).mpr
    field_simp [he.ne']
    nlinarith
  have hl := Int.floor_mono hlo
  have hu := Int.floor_mono hhi
  rw [Int.floor_sub_one,Int.floor_sub_one] at hl
  rw [Int.floor_add_one,Int.floor_add_one] at hu
  change ⌊x j/e⌋∈Icc (⌊y j/e⌋-2) (⌊y j/e⌋+2)
  apply mem_Icc.mpr
  omega

lemma original_cell_output_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (p : Parent) (i : Fin n) (k : Index) (hk : k∈original i) :
    cellLabel D a p i k ∈ neighborBox (D.thickness/128) (physicalMap D a p (cellCenter (mesh D) k)) := by
  exact cellIndex_mem_neighborBox (by have hd:=h.1.2.1; positivity) _ _
    (frontPoint_near_physicalCell h original horiginal ha p i k hk)

/-- Joint source-union count. All original tubes incident to the SAME original
cell contribute only a fixed625 output-cell menu, so no tube multiplicity is
charged to the original shaded union. -/
theorem output_support_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (p : Parent) :
    (R.biUnion (cells D original a p)).card ≤ 625*(R.biUnion original).card := by
  let box := fun k => neighborBox (D.thickness/128) (physicalMap D a p (cellCenter (mesh D) k))
  have hs : R.biUnion (cells D original a p) ⊆ (R.biUnion original).biUnion box := by
    intro q hq
    obtain ⟨i,hi,hqi⟩ := mem_biUnion.mp hq
    obtain ⟨k,hki,rfl⟩ := mem_image.mp hqi
    exact mem_biUnion.mpr ⟨k,mem_biUnion.mpr ⟨i,hi,hki⟩,
      original_cell_output_menu h original horiginal ha p i k hki⟩
  calc
    _ ≤ ((R.biUnion original).biUnion box).card := card_le_card hs
    _ ≤ ∑k∈R.biUnion original,(box k).card := card_biUnion_le
    _ = _ := by simp [box,neighborBox_card,mul_comm]

lemma union_cellShading_eq {n : ℕ} (R : Finset (Fin n)) (C : Fin n → Finset Index) (e : ℝ) :
    (⋃i∈R,wzCellShading e C i) = ⋃k∈(R.biUnion C : Set Index),wzDyadicCell e k := by
  ext x
  simp only [wzCellShading,Set.mem_iUnion,Finset.mem_coe,Finset.mem_biUnion]
  aesop

lemma volume_cell_union {e : ℝ} (he : 0 < e) (C : Finset Index) :
    MeasureTheory.volume (⋃k∈(C:Set Index),wzDyadicCell e k)=
      (C.card:ℝ≥0∞)*(ENNReal.ofReal e)^4 := by
  simpa only [wzCellShading] using volume_wzCellShading he (fun _ : Fin 1 => C) 0

/-- Joint ORIGINAL union-volume control for the actual new cubical shadings.
The fixed625 loss is independent of the number of tubes through an old cell. -/
theorem output_union_volume_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (p : Parent) :
    MeasureTheory.volume (⋃i∈R,wzCellShading (D.thickness/128) (cells D original a p) i) ≤
      625*MeasureTheory.volume (⋃i∈R,D.shading i) := by
  have hd:=h.1.2.1
  have hm : 0 < mesh D := half_pos hd
  have he : 0 < D.thickness/128 := by positivity
  have hold : (⋃i∈R,D.shading i)=⋃i∈R,wzCellShading (mesh D) original i := by
    simp_rw [horiginal]
  rw [hold,union_cellShading_eq,union_cellShading_eq,volume_cell_union he,volume_cell_union hm]
  have hc : ((R.biUnion (cells D original a p)).card:ℝ≥0∞) ≤
      625*(R.biUnion original).card := by exact_mod_cast output_support_card_le h original horiginal ha R p
  have hmesh : ENNReal.ofReal (D.thickness/128) ≤ ENNReal.ofReal (mesh D) := by
    apply ENNReal.ofReal_le_ofReal
    dsimp [mesh]
    linarith
  calc
    _ ≤ (625*(R.biUnion original).card)*(ENNReal.ofReal (mesh D))^4 :=
      mul_le_mul' hc (pow_le_pow_left' hmesh 4)
    _ = _ := by ring
end NativePaddedCellUnionBound
