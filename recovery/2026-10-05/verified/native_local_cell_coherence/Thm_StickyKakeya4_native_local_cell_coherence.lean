import Theorems.Thm_StickyKakeya4_native_local_parent_cells
import Theorems.Thm_StickyKakeya4_native_local_parent_physical_map
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000
noncomputable section
namespace NativeLocalCellCoherence
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentPhysicalData
open NativeContractedUnitParent NativeLocalParentGeometry NativeLocalParentCells
open NativeLocalParentPhysicalMap
open scoped BigOperators

/-- The genuine local front point differs from the common physical image
only by the original tube's graph residual, with the exact N/512 factor. -/
lemma frontPoint_coordinate_error {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (i : Fin n) (k : Index) (j : Fin 3) :
    frontPoint D a N p i k j.castSucc -
      physicalMap D a N p (cellCenter (mesh D) k) j.castSucc =
        -((N : ℝ) * ((cellCenter (mesh D) k) j.castSucc - intercept (D.line i) j -
          slope (D.line i) j * (cellCenter (mesh D) k) (3 : Fin 4))) / 512 := by
  simp only [frontPoint, NativeLocalParentPhysicalMap.physicalMap, baseMap, contractPoint,
    ActualSlopeSource.heightPoint_castSucc, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  dsimp [localIntercept, localSlope, shiftedIntercept, NativeOriginalPaddedCells.oldTime,
    ShearBinFibers.oldCenter, chartIndex, cellCenter]
  push_cast
  ring

/-- The common physical map preserves exactly the local front point's height. -/
lemma physicalCell_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (k : Index) :
    physicalMap D a N p (cellCenter (mesh D) k) (3 : Fin 4) =
      NativeOriginalPaddedCells.oldTime D a k / 128 := by
  change (1 / 32 : ℝ) *
    ((cellCenter (mesh D) k (3 : Fin 4) - (shift D a : ℝ) * mesh D) / 16) = _
  rw [NativeOriginalPaddedCells.oldTime, chart_center_time]
  ring

lemma frontPoint_height_eq_physicalCell {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (i : Fin n) (k : Index) :
    frontPoint D a N p i k (3 : Fin 4) =
      physicalMap D a N p (cellCenter (mesh D) k) (3 : Fin 4) := by
  rw [frontPoint_height, physicalCell_height]

lemma cellLabel_height_eq_physicalCell {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (i : Fin n) (k : Index) :
    cellLabel D a N p i k (3 : Fin 4) =
      wzDyadicCellIndex ((N : ℝ) * D.thickness / 128)
        (physicalMap D a N p (cellCenter (mesh D) k)) (3 : Fin 4) := by
  change ⌊frontPoint D a N p i k (3 : Fin 4) / ((N : ℝ) * D.thickness / 128)⌋ = _
  rw [frontPoint_height_eq_physicalCell]
  rfl

/-- Actual original shading membership supplies the residual estimate.
There is no residual certificate or replacement incidence set in this statement. -/
theorem frontPoint_near_physicalCell {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (p : Parent) (i : Fin n) (k : Index) (hk : k ∈ original i) (j : Fin 4) :
    |frontPoint D a N p i k j - physicalMap D a N p (cellCenter (mesh D) k) j| ≤
      (3 / 2 : ℝ) * ((N : ℝ) * D.thickness / 128) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [show (Fin.last 3 : Fin 4) = 3 by rfl, frontPoint_height_eq_physicalCell,
      sub_self, abs_zero]
    have hd := h.1.2.1
    positivity
  · have hh := (original_cell_bounds h original horiginal a ha
      ((mem_incidences original i k).mpr hk)).2 j
    rw [chart_center_residual, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hh
    have hr : |(cellCenter (mesh D) k) j.castSucc - intercept (D.line i) j -
        slope (D.line i) j * (cellCenter (mesh D) k) (3 : Fin 4)| ≤
          6 * D.thickness := by
      dsimp [mesh] at hh ⊢
      linarith
    rw [frontPoint_coordinate_error, abs_div, abs_neg, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg N), abs_of_pos (by norm_num : (0 : ℝ) < 512)]
    have hm := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg N)
    nlinarith

/-- A tube-independent menu around one common physical image: five possible
indices in each spatial coordinate and the exact common height index. -/
def neighborBox (e : ℝ) (x : E4) : Finset Index :=
  Fintype.piFinset (fun j => if j = (3 : Fin 4) then {⌊x j / e⌋}
    else Icc (⌊x j / e⌋ - 2) (⌊x j / e⌋ + 2))

lemma neighborBox_card (e : ℝ) (x : E4) : (neighborBox e x).card = 125 := by
  have hi (j : Fin 4) : (Icc (⌊x j / e⌋ - 2) (⌊x j / e⌋ + 2)).card = 5 := by
    have hh : ((Icc (⌊x j / e⌋ - 2) (⌊x j / e⌋ + 2)).card : ℤ) = 5 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simp only [neighborBox, Fintype.card_piFinset, Fin.prod_univ_four]
  simp [hi]

lemma cellIndex_mem_neighborBox {e : ℝ} (he : 0 < e) (x y : E4)
    (hxy : ∀ j, |x j - y j| ≤ (3 / 2 : ℝ) * e)
    (ht : x (3 : Fin 4) = y (3 : Fin 4)) :
    wzDyadicCellIndex e x ∈ neighborBox e y := by
  apply Fintype.mem_piFinset.mpr
  intro j
  by_cases hj : j = (3 : Fin 4)
  · subst j
    simp [wzDyadicCellIndex, ht]
  · simp only [if_neg hj]
    have ha := abs_le.mp (hxy j)
    have hlo : y j / e - 1 - 1 ≤ x j / e := by
      apply (le_div_iff₀ he).mpr
      field_simp [he.ne']
      nlinarith
    have hhi : x j / e ≤ y j / e + 1 + 1 := by
      apply (div_le_iff₀ he).mpr
      field_simp [he.ne']
      nlinarith
    have hl := Int.floor_mono hlo
    have hu := Int.floor_mono hhi
    rw [Int.floor_sub_one, Int.floor_sub_one] at hl
    rw [Int.floor_add_one, Int.floor_add_one] at hu
    change ⌊x j / e⌋ ∈ Icc (⌊y j / e⌋ - 2) (⌊y j / e⌋ + 2)
    exact mem_Icc.mpr ⟨by omega, by omega⟩

/-- Every original tube incident to k has its genuine local output label in
the same 125-element menu. This holds for any fixed p, hence for its backbone. -/
theorem original_cell_output_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) (k : Index) (hk : k ∈ original i) :
    cellLabel D a N p i k ∈ neighborBox ((N : ℝ) * D.thickness / 128)
      (physicalMap D a N p (cellCenter (mesh D) k)) := by
  exact cellIndex_mem_neighborBox (by have hd := h.1.2.1; positivity) _ _
    (frontPoint_near_physicalCell h original horiginal ha N p i k hk)
    (frontPoint_height_eq_physicalCell D a N p i k)

/-- Image multiplicity across ALL original tubes at a single old shading
cell. The old cell and original incidences stay fixed; no tube count is lost. -/
theorem same_original_cell_image_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (R : Finset (Fin n)) (k : Index) :
    ((R.filter (fun i => k ∈ original i)).image (fun i => cellLabel D a N p i k)).card ≤
      125 := by
  rw [← neighborBox_card ((N : ℝ) * D.thickness / 128)
    (physicalMap D a N p (cellCenter (mesh D) k))]
  apply card_le_card
  intro q hq
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hq
  exact original_cell_output_menu h original horiginal ha N hN p i k (mem_filter.mp hi).2

/-- The selected original parent inherits the same same-cell bound. -/
theorem parent_original_cell_image_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (k : Index) :
    (((backbone D a N p).filter (fun i => k ∈ original i)).image
      (fun i => cellLabel D a N p i k)).card ≤ 125 :=
  same_original_cell_image_card_le h original horiginal ha N hN p (backbone D a N p) k

/-- Joint source-union count for the genuine local cells. Each old cell pays
the fixed spatial menu once, independently of its original tube multiplicity. -/
theorem output_support_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (R : Finset (Fin n)) :
    (R.biUnion (cells D original a N p)).card ≤ 125 * (R.biUnion original).card := by
  let box := fun k => neighborBox ((N : ℝ) * D.thickness / 128)
    (physicalMap D a N p (cellCenter (mesh D) k))
  have hs : R.biUnion (cells D original a N p) ⊆ (R.biUnion original).biUnion box := by
    intro q hq
    obtain ⟨i, hi, hqi⟩ := mem_biUnion.mp hq
    obtain ⟨k, hki, rfl⟩ := mem_image.mp hqi
    exact mem_biUnion.mpr ⟨k, mem_biUnion.mpr ⟨i, hi, hki⟩,
      original_cell_output_menu h original horiginal ha N hN p i k hki⟩
  calc
    _ ≤ ((R.biUnion original).biUnion box).card := card_le_card hs
    _ ≤ ∑ k ∈ R.biUnion original, (box k).card := card_biUnion_le
    _ = _ := by simp [box, neighborBox_card, mul_comm]

/-- The local point label of a literal original incidence. The original
incidence remains `(tube, old cell)` throughout the compression argument. -/
def localCellLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (z : Fin n × Index) : Index :=
  cellLabel D a N p z.1 z.2

/-- Actual occupied local tube/cell pairs, as an image of original incidences. -/
def localPair {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (z : Fin n × Index) : Fin n × Index :=
  (z.1, localCellLabel D a N p z)

/-- Deduplicate only the old-cell/local-cell witness relation. No incidence
is added to E, and both point supports will be projections of this same E. -/
def pointShadow {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (E : Finset (Fin n × Index)) : Finset (Index × Index) :=
  E.image (fun z => (z.2, localCellLabel D a N p z))

/-- A fixed local tube/cell fiber counts distinct original cells because its
tube coordinate is fixed. No injectivity of the tube-dependent map is assumed. -/
lemma pairFiber_snd_injective {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (E : Finset (Fin n × Index)) (b : Fin n × Index) :
    Set.InjOn Prod.snd (↑(E.filter (fun z => localPair D a N p z = b)) :
      Set (Fin n × Index)) := by
  intro z hz w hw he
  apply Prod.ext
  · have hz' := congrArg Prod.fst (mem_filter.mp hz).2
    have hw' := congrArg Prod.fst (mem_filter.mp hw).2
    exact hz'.trans hw'.symm
  · exact he

lemma pairFiber_card_le_shadow_fiber {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (E : Finset (Fin n × Index)) (b : Fin n × Index) :
    (E.filter (fun z => localPair D a N p z = b)).card ≤
      ((pointShadow D a N p E).filter (fun s => s.2 = b.2)).card := by
  have hinj : Set.InjOn (fun z : Fin n × Index => (z.2, localCellLabel D a N p z))
      (↑(E.filter (fun z => localPair D a N p z = b)) : Set (Fin n × Index)) := by
    intro z hz w hw he
    exact pairFiber_snd_injective D a N p E b hz hw (congrArg Prod.fst he)
  rw [← card_image_of_injOn hinj]
  apply card_le_card
  intro s hs
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hs
  exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mp hz).1,
    congrArg Prod.snd (mem_filter.mp hz).2⟩

/-- The 125 bound survives arbitrary literal retention E of the original
incidences. It bounds the deduplicated witness relation over its old support. -/
theorem retained_shadow_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (E : Finset (Fin n × Index))
    (hE : E ⊆ incidences original) :
    (pointShadow D a N p E).card ≤ 125 * (E.image Prod.snd).card := by
  have hmap : (↑(pointShadow D a N p E) : Set (Index × Index)).MapsTo
      Prod.fst (E.image Prod.snd) := by
    intro s hs
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hs
    exact mem_image_of_mem _ hz
  have hfiber (k : Index) :
      ((pointShadow D a N p E).filter (fun s => s.1 = k)).card ≤ 125 := by
    have hinj : Set.InjOn Prod.snd
        (↑((pointShadow D a N p E).filter (fun s => s.1 = k)) : Set (Index × Index)) := by
      intro z hz w hw he
      exact Prod.ext ((mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm) he
    have hsub : (((pointShadow D a N p E).filter (fun s => s.1 = k)).image Prod.snd) ⊆
        ((univ.filter (fun i : Fin n => k ∈ original i)).image
          (fun i => cellLabel D a N p i k)) := by
      intro q hq
      obtain ⟨s, hs, rfl⟩ := mem_image.mp hq
      obtain ⟨hs, he⟩ := mem_filter.mp hs
      obtain ⟨⟨i, k'⟩, hz, rfl⟩ := mem_image.mp hs
      change k' = k at he
      subst k'
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _,
        (mem_incidences original i k).mp (hE hz)⟩, rfl⟩
    rw [← card_image_of_injOn hinj]
    exact (card_le_card hsub).trans
      (same_original_cell_image_card_le h original horiginal ha N hN p univ k)
  exact card_le_mul_card_image_of_maps_to hmap 125 (fun k _ => hfiber k)

/-- Heavy actual local tube/cell fibers compress the point shadow of the
SAME retained original E, despite the tube-dependent local cell labels.
L is an intermediate finite fiber condition; all geometry and the factor125
are derived from the actual original native input. -/
theorem retained_shadow_compression {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (E : Finset (Fin n × Index))
    (hE : E ⊆ incidences original) (L : ℝ)
    (hL : ∀ b ∈ E.image (localPair D a N p),
      L ≤ ((E.filter (fun z => localPair D a N p z = b)).card : ℝ)) :
    L * (E.image (localCellLabel D a N p)).card ≤
      (125 : ℝ) * (E.image Prod.snd).card := by
  have hmap : (↑(pointShadow D a N p E) : Set (Index × Index)).MapsTo
      Prod.snd (E.image (localCellLabel D a N p)) := by
    intro s hs
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hs
    exact mem_image_of_mem _ hz
  have hlower (q : Index) (hq : q ∈ E.image (localCellLabel D a N p)) :
      L ≤ (((pointShadow D a N p E).filter (fun s => s.2 = q)).card : ℝ) := by
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hq
    exact (hL (localPair D a N p z) (mem_image_of_mem _ hz)).trans
      (by exact_mod_cast pairFiber_card_le_shadow_fiber D a N p E (localPair D a N p z))
  calc
    _ = ∑ _q ∈ E.image (localCellLabel D a N p), L := by simp [mul_comm]
    _ ≤ ∑ q ∈ E.image (localCellLabel D a N p),
        (((pointShadow D a N p E).filter (fun s => s.2 = q)).card : ℝ) := sum_le_sum hlower
    _ = ((pointShadow D a N p E).card : ℝ) := by
      exact_mod_cast (card_eq_sum_card_fiberwise hmap).symm
    _ ≤ _ := by exact_mod_cast retained_shadow_card_le h original horiginal ha N hN p E hE

end NativeLocalCellCoherence
