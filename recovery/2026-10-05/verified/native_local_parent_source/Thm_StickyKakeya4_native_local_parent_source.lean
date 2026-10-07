import Theorems.Thm_StickyKakeya4_native_local_parent_scales
import Theorems.Thm_StickyKakeya4_native_local_parent_capacity
import Theorems.Thm_StickyKakeya4_native_local_cell_coherence
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeLocalParentSource
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeUnitParentNormalization
open scoped BigOperators ENNReal

/-- The full retained original parent, including original labels with empty
selected shading. Selecting incidences never changes this tube backbone. -/
def parentLabels {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (N : ℕ) (p : Parent) : Finset (Fin n) :=
  R.filter (fun i => parentLabel D a N i = p)

lemma mem_parentLabels {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (N : ℕ) (p : Parent) (i : Fin n) :
    i ∈ parentLabels D R a N p ↔ i ∈ R ∧ parentLabel D a N i = p := by
  simp only [parentLabels, mem_filter]

/-- Literal old cells retained by the SAME original incidence relation E. -/
def selectedCells {n : ℕ} (E : Finset (Fin n × Index)) (i : Fin n) : Finset Index :=
  (E.filter (fun z => z.1 = i)).image Prod.snd

lemma mem_selectedCells {n : ℕ} (E : Finset (Fin n × Index)) (i : Fin n) (k : Index) :
    k ∈ selectedCells E i ↔ (i,k) ∈ E := by
  simp only [selectedCells, mem_image, mem_filter]
  constructor
  · rintro ⟨⟨j,l⟩,⟨hz,hj⟩,hl⟩
    dsimp at hj hl
    subst j
    subst l
    exact hz
  · intro hz
    exact ⟨(i,k),⟨hz,rfl⟩,rfl⟩

lemma selectedCells_subset {n : ℕ} (original : Fin n → Finset Index)
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original) (i : Fin n) :
    selectedCells E i ⊆ original i := by
  intro k hk
  exact (mem_incidences original i k).mp (hE ((mem_selectedCells E i k).mp hk))

lemma selected_incidences {n : ℕ} (E : Finset (Fin n × Index)) :
    incidences (selectedCells E) = E := by
  ext z
  rcases z with ⟨i,k⟩
  exact (mem_incidences _ i k).trans (mem_selectedCells E i k)

/-- Actual front-meeting new dyadic cubes of the selected old cells. -/
def outputCells {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (a : ℝ) (N : ℕ) (p : Parent) : Fin n → Finset Index :=
  NativeLocalParentCells.cells D (selectedCells E) a N p

lemma mem_outputCells {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (a : ℝ) (N : ℕ) (p : Parent) (i : Fin n) (q : Index) :
    q ∈ outputCells D E a N p i ↔
      ∃k, (i,k) ∈ E ∧ NativeLocalParentCells.cellLabel D a N p i k = q := by
  simp only [outputCells, NativeLocalParentCells.cells, mem_image, mem_selectedCells]

lemma outputCells_subset {n : ℕ} (D : FiniteScaleSource n)
    (original : Fin n → Finset Index) (E : Finset (Fin n × Index))
    (hE : E ⊆ incidences original) (a : ℝ) (N : ℕ) (p : Parent) (i : Fin n) :
    outputCells D E a N p i ⊆ NativeLocalParentCells.cells D original a N p i :=
  image_subset_image (selectedCells_subset original E hE i)

lemma selected_shading_subset_tube {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) (hp : parentLabel D a N i = p) :
    wzCellShading ((N:ℝ)*D.thickness/128) (outputCells D E a N p) i ⊆
      markedUnitTube (NativeLocalParentGeometry.line D a N p i) ((N:ℝ)*D.thickness/64) := by
  apply Set.Subset.trans ?_ (NativeLocalParentCells.shading_subset_tube h original horiginal ha N hN p i hp)
  intro x hx
  simp only [wzCellShading, Set.mem_iUnion, mem_coe] at hx ⊢
  obtain ⟨q,hq,hx⟩ := hx
  exact ⟨q,outputCells_subset D original E hE a N p i hq,hx⟩

/-- Actual source cells, reindexed by exactly the full original parent. -/
def sourceCells {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (N : ℕ) (p : Parent)
    (i : Fin (parentLabels D R a N p).card) : Finset Index :=
  outputCells D E a N p (NativePaddedCellSource.originalLabel (parentLabels D R a N p) i)

lemma source_direction_separation {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (N : ℕ)
    (hN : 0 < N) (p : Parent) (i j : Fin (parentLabels D R a N p).card) (hne : i ≠ j) :
    (N:ℝ)*D.thickness/64 ≤
      dist (direction (NativeLocalParentGeometry.line D a N p
        (NativePaddedCellSource.originalLabel (parentLabels D R a N p) i)))
        (direction (NativeLocalParentGeometry.line D a N p
        (NativePaddedCellSource.originalLabel (parentLabels D R a N p) j))) := by
  have hi := (mem_parentLabels D R a N p _).mp
    (NativePaddedCellSource.originalLabel_mem (parentLabels D R a N p) i)
  have hj := (mem_parentLabels D R a N p _).mp
    (NativePaddedCellSource.originalLabel_mem (parentLabels D R a N p) j)
  have hs := NativeLocalParentGeometry.direction_separation h N hN p _ _ hi.2 hj.2
    (fun he => hne (NativePaddedCellSource.originalLabel_injective _ he))
  have hd := h.1.2.1
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  nlinarith

/-- Genuine normalized local-parent source. The index set is the FULL
original R-parent; E supplies only its selected shadings. No analytic
admissibility or density certificate is a constructor argument. -/
def source {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent) :
    FiniteScaleSource (parentLabels D R a (2^m) p).card :=
  directionSeparatedWZCellSourceAtScales (((2^m:ℕ):ℝ)*D.thickness/64)
    (((2^m:ℕ):ℝ)*D.thickness/128)
    (fun i => NativeLocalParentGeometry.line D a (2^m) p
      (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i))
    (sourceCells D R E a (2^m) p)
    (by have hd := h.1.2.1; positivity)
    (source_direction_separation h R (2^m) (by positivity) p)

lemma source_thickness {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent) :
    (source h R E a m p).thickness = ((2^m:ℕ):ℝ)*D.thickness/64 := rfl

lemma source_line {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (i : Fin (parentLabels D R a (2^m) p).card) :
    (source h R E a m p).line i = NativeLocalParentGeometry.line D a (2^m) p
      (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i) := rfl

lemma source_shading {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (i : Fin (parentLabels D R a (2^m) p).card) :
    (source h R E a m p).shading i =
      wzCellShading (((2^m:ℕ):ℝ)*D.thickness/128) (sourceCells D R E a (2^m) p) i := rfl

lemma source_weights_fibreMark {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (i : Fin (parentLabels D R a (2^m) p).card) :
    (source h R E a m p).weight i = 1 ∧
      (source h R E a m p).fibreMark i = mark ((source h R E a m p).line i) := ⟨rfl,rfl⟩

/-- All native geometric and cubical fields of the same actual source.
The literal-subset assumption on E is enough for genuine front support. -/
theorem source_geometric_fields {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (level m : ℕ) (hdy : D.thickness = (2:ℝ)⁻¹^level) (hm : m ≤ level) (p : Parent) :
    let S := source h R E a m p
    0 < S.thickness ∧ S.thickness ≤ 1 ∧ IsWZDyadicScale S.thickness ∧
      (∀i,IsValidLine (S.line i)) ∧ (∀i,S.line i ∈ fixedCompactClass) ∧
      (∀i,S.weight i = 1) ∧ (∀i,S.fibreMark i = mark (S.line i)) ∧
      (∀i,MeasurableSet (S.shading i)) ∧
      (∀i,IsWZComparableCubicalShading S.thickness (S.shading i)) ∧
      (∀i,S.shading i ⊆ markedUnitTube (S.line i) S.thickness) ∧
      (∀i j,i ≠ j → S.thickness ≤ dist (direction (S.line i)) (direction (S.line j))) ∧
      HasNormalizedWZGraphSlab S ∧ HasFixedWZGraphNormalization S := by
  let Q := parentLabels D R a (2^m) p
  let S := source h R E a m p
  have hd := h.1.2.1
  have hdp : 0 < ((2^m:ℕ):ℝ)*D.thickness/64 := by positivity
  have hmp : 0 < ((2^m:ℕ):ℝ)*D.thickness/128 := by positivity
  obtain ⟨htd,hmd⟩ := NativeLocalParentScales.local_scales_dyadic hdy hm
  have hp (i : Fin Q.card) : parentLabel D a (2^m)
      (NativePaddedCellSource.originalLabel Q i) = p :=
    ((mem_parentLabels D R a (2^m) p _).mp (NativePaddedCellSource.originalLabel_mem Q i)).2
  have hline (i : Fin Q.card) := NativeLocalParentGeometry.valid_slab D a (2^m) p _ (hp i)
  have hvalid : ∀i,IsValidLine (S.line i) := fun i => (hline i).1
  have hslab : HasNormalizedWZGraphSlab S := by
    refine ⟨fun i => (hline i).2.1,-(1/4:ℝ),(1/4:ℝ),by norm_num,?_,fun i => (hline i).2.2⟩
    exact Set.nonempty_Icc.mpr (by norm_num)
  refine ⟨hdp,?_,htd,hvalid,?_,fun _ => rfl,fun _ => rfl,?_,?_,?_,
    source_direction_separation h R (2^m) (by positivity) p,hslab,
    hasFixedWZGraphNormalization_of_normalizedSlab S hvalid hslab⟩
  · change ((2^m:ℕ):ℝ)*D.thickness/64 ≤ 1
    rw [NativeLocalParentScales.relative_scale hdy hm]
    have hh : (2:ℝ)⁻¹^(level-m) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  · intro i
    exact NativeLocalParentGeometry.mem_fixedCompactClass D a (2^m) p _ (hp i)
  · intro i
    exact measurableSet_wzCellShading _ (sourceCells D R E a (2^m) p) i
  · intro i
    refine ⟨((2^m:ℕ):ℝ)*D.thickness/128,hmp,?_,?_,hmd,?_⟩
    · change ((2^m:ℕ):ℝ)*D.thickness/128 ≤ ((2^m:ℕ):ℝ)*D.thickness/64
      linarith
    · change ((2^m:ℕ):ℝ)*D.thickness/64 ≤ 2*(((2^m:ℕ):ℝ)*D.thickness/128)
      linarith
    · exact isWZCubicalShading_wzCellShading _ (sourceCells D R E a (2^m) p) i
  · intro i
    exact selected_shading_subset_tube h original horiginal ha E hE (2^m) (by positivity) p _ (hp i)

/-- The original label readback is exactly Q, with its full cardinality. -/
lemma source_original_labels {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (m : ℕ) (p : Parent) :
    Set.range (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p)) =
      (parentLabels D R a (2^m) p : Set (Fin n)) :=
  NativePaddedCellSource.originalLabel_range _

/-- Reindexing output incidences changes no original tube label. -/
def originalPair {n : ℕ} (Q : Finset (Fin n)) (z : Fin Q.card × Index) : Fin n × Index :=
  (NativePaddedCellSource.originalLabel Q z.1,z.2)

lemma originalPair_injective {n : ℕ} (Q : Finset (Fin n)) :
    Function.Injective (originalPair Q) := by
  intro z w he
  have hfst := congrArg Prod.fst he
  have hsnd := congrArg Prod.snd he
  exact Prod.ext (NativePaddedCellSource.originalLabel_injective Q hfst) hsnd

/-- Exact occupied tube/cell pairs on the original full-parent labels. -/
theorem source_incidences_readback {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (N : ℕ) (p : Parent)
    (hQ : ∀z∈E,z.1 ∈ parentLabels D R a N p) :
    (incidences (sourceCells D R E a N p)).image (originalPair (parentLabels D R a N p)) =
      E.image (NativeLocalCellCoherence.localPair D a N p) := by
  let Q := parentLabels D R a N p
  ext z
  constructor
  · intro hz
    obtain ⟨⟨i,q⟩,hmem,rfl⟩ := mem_image.mp hz
    have hq := (mem_incidences (sourceCells D R E a N p) i q).mp hmem
    obtain ⟨k,hk,he⟩ := (mem_outputCells D E a N p _ q).mp hq
    exact mem_image.mpr ⟨(NativePaddedCellSource.originalLabel Q i,k),hk,
      Prod.ext rfl he⟩
  · intro hz
    obtain ⟨⟨i,k⟩,hmem,rfl⟩ := mem_image.mp hz
    have hi : i ∈ Set.range (NativePaddedCellSource.originalLabel Q) := by
      rw [NativePaddedCellSource.originalLabel_range Q]
      exact hQ (i,k) hmem
    obtain ⟨j,hj⟩ := hi
    refine mem_image.mpr ⟨(j,NativeLocalParentCells.cellLabel D a N p i k),?_,?_⟩
    · apply (mem_incidences _ _ _).mpr
      change NativeLocalParentCells.cellLabel D a N p i k ∈ outputCells D E a N p _
      rw [hj]
      exact (mem_outputCells D E a N p i _).mpr ⟨k,hmem,rfl⟩
    · exact Prod.ext hj rfl

lemma source_incidence_card {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (N : ℕ) (p : Parent)
    (hQ : ∀z∈E,z.1 ∈ parentLabels D R a N p) :
    (incidences (sourceCells D R E a N p)).card =
      (E.image (NativeLocalCellCoherence.localPair D a N p)).card := by
  rw [← source_incidences_readback D R E a N p hQ]
  exact (card_image_of_injective _ (originalPair_injective _)).symm

/-- Exact point support of the same source and same retained old relation. -/
theorem source_support_readback {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (N : ℕ) (p : Parent)
    (hQ : ∀z∈E,z.1 ∈ parentLabels D R a N p) :
    support (sourceCells D R E a N p) =
      E.image (NativeLocalCellCoherence.localCellLabel D a N p) := by
  have he := congrArg (fun F : Finset (Fin n × Index) => F.image Prod.snd)
    (source_incidences_readback D R E a N p hQ)
  rw [support_eq_image]
  simpa only [image_image, Function.comp_def, originalPair, NativeLocalCellCoherence.localPair] using he

/-- Geometric preimage capacity survives arbitrary literal cell selection. -/
lemma selected_cell_fiber_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) (q : Index) :
    ((selectedCells E i).filter (fun k => NativeLocalParentCells.cellLabel D a N p i k = q)).card ≤
      175616*N := by
  exact (card_le_card (filter_subset_filter _ (selectedCells_subset original E hE i))).trans
    (NativeLocalParentCapacity.output_cell_fiber_card_le h original horiginal ha N hN p i q)

lemma selected_card_le_output_card {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) :
    (selectedCells E i).card ≤ (175616*N)*(outputCells D E a N p i).card := by
  exact card_le_mul_card_image (selectedCells E i) (175616*N)
    (fun q _ => selected_cell_fiber_card_le h original horiginal ha E hE N hN p i q)

/-- The selected shading mass gains N^3 with an absolute normalization cost.
No assumption identifies selectedCells E with the whole original shading. -/
theorem selected_shading_mass_scale {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) :
    (N:ℝ)^3*(volume (wzCellShading (mesh D) (selectedCells E) i)).toReal ≤
      (175616*64^4:ℝ)*
        (volume (wzCellShading ((N:ℝ)*D.thickness/128) (outputCells D E a N p) i)).toReal := by
  have hd := h.1.2.1
  have hm : 0 < mesh D := half_pos hd
  have he : 0 < (N:ℝ)*D.thickness/128 := by positivity
  have hc : ((selectedCells E i).card:ℝ) ≤
      (175616*(N:ℝ))*(outputCells D E a N p i).card := by
    exact_mod_cast selected_card_le_output_card h original horiginal ha E hE N hN p i
  rw [volume_wzCellShading hm,volume_wzCellShading he]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hm.le,ENNReal.toReal_ofReal he.le]
  calc
    _ ≤ (N:ℝ)^3*((175616*(N:ℝ))*(outputCells D E a N p i).card*(mesh D)^4) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
    _ = _ := by dsimp [mesh]; ring

/-- Exact total mass readback, retaining the genuine local mesh factor. -/
theorem source_total_shading {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : ∀z∈E,z.1 ∈ parentLabels D R a (2^m) p) :
    wzTotalShadingVolume (source h R E a m p) =
      (E.image (NativeLocalCellCoherence.localPair D a (2^m) p)).card *
        (ENNReal.ofReal (((2^m:ℕ):ℝ)*D.thickness/128))^4 := by
  rw [total_shading_eq_incidence_volume (source h R E a m p)
    (by have hd := h.1.2.1; positivity) (sourceCells D R E a (2^m) p)
    (source_shading h R E a m p),source_incidence_card D R E a (2^m) p hQ]

/-- Exact union mass readback on the SAME retained E. -/
theorem source_union_volume {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : ∀z∈E,z.1 ∈ parentLabels D R a (2^m) p) :
    volume (sourceUnion (source h R E a m p)) =
      (E.image (NativeLocalCellCoherence.localCellLabel D a (2^m) p)).card *
        (ENNReal.ofReal (((2^m:ℕ):ℝ)*D.thickness/128))^4 := by
  rw [union_eq_support_volume (source h R E a m p)
    (by have hd := h.1.2.1; positivity) (sourceCells D R E a (2^m) p)
    (fun _ => rfl) (source_shading h R E a m p),source_support_readback D R E a (2^m) p hQ]

lemma source_multiplicity {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : ∀z∈E,z.1 ∈ parentLabels D R a (2^m) p) :
    NativeFiniteKakeyaCounts.multiplicity (source h R E a m p) =
      (E.image (NativeLocalCellCoherence.localPair D a (2^m) p)).card /
        ((E.image (NativeLocalCellCoherence.localCellLabel D a (2^m) p)).card:ℝ≥0∞) := by
  rw [multiplicity_eq_card_ratio (source h R E a m p)
    (by have hd := h.1.2.1; positivity) (sourceCells D R E a (2^m) p)
    (fun _ => rfl) (source_shading h R E a m p),source_incidence_card D R E a (2^m) p hQ,
    source_support_readback D R E a (2^m) p hQ]

lemma sum_originalLabel {n : ℕ} {M : Type*} [AddCommMonoid M]
    (Q : Finset (Fin n)) (f : Fin n → M) :
    (∑j : Fin Q.card,f (NativePaddedCellSource.originalLabel Q j)) = ∑i∈Q,f i := by
  have hh := Q.equivFin.symm.sum_comp (fun i : Q => f i.val)
  simpa only [NativePaddedCellSource.originalLabel,Finset.sum_coe_sort] using hh

lemma source_total_shading_eq_parent {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent) :
    wzTotalShadingVolume (source h R E a m p) =
      ∑i∈parentLabels D R a (2^m) p,
        volume (wzCellShading (((2^m:ℕ):ℝ)*D.thickness/128) (outputCells D E a (2^m) p) i) := by
  exact sum_originalLabel (M:=ℝ≥0∞) (parentLabels D R a (2^m) p)
    (fun i => volume (wzCellShading (((2^m:ℕ):ℝ)*D.thickness/128) (outputCells D E a (2^m) p) i))

/-- Selected ORIGINAL mass on the full Q backbone transfers to the actual
source with the correct N^3 gain. This directly consumes an average-parent
density bound; it never requires a per-tube lower density. -/
theorem selected_parent_mass_le_source {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (m : ℕ) (p : Parent) :
    ((2^m:ℕ):ℝ)^3 * (∑i∈parentLabels D R a (2^m) p,
      (volume (wzCellShading (mesh D) (selectedCells E) i)).toReal) ≤
        (175616*64^4:ℝ)*(wzTotalShadingVolume (source h R E a m p)).toReal := by
  have hm : 0 < ((2^m:ℕ):ℝ)*D.thickness/128 := by have hd := h.1.2.1; positivity
  rw [source_total_shading_eq_parent,ENNReal.toReal_sum,mul_sum,mul_sum]
  · apply sum_le_sum
    intro i _hi
    exact selected_shading_mass_scale h original horiginal ha E hE (2^m) (by positivity) p i
  · intro i _hi
    rw [volume_wzCellShading hm]
    finiteness

lemma source_center_height_zero {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (i : Fin (parentLabels D R a (2^m) p).card) :
    wzMarkedCenterHeight ((source h R E a m p).line i) = 0 := by
  rw [source_line,NativeLocalParentGeometry.line,NativeContractedUnitParent.contractLine_center_height,
    NativeLocalParentGeometry.baseLine,NativeGraphMarkedLine.center_height,zero_div]

lemma selected_cells_meet_front {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) (hp : parentLabel D a N i = p)
    (q : Index) (hq : q ∈ outputCells D E a N p i) :
    ∃t : Set.Icc (-(1/2:ℝ)) (1/2:ℝ),
      rawFrontParam (NativeLocalParentGeometry.line D a N p i,(t:ℝ)) ∈
        wzDyadicCell ((N:ℝ)*D.thickness/128) q :=
  NativeLocalParentCells.cells_meet_front h original horiginal ha N hN p i hp q
    (outputCells_subset D original E hE a N p i hq)

lemma selected_shading_mass_scale_enn {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) :
    (N:ℝ≥0∞)^3*volume (wzCellShading (mesh D) (selectedCells E) i) ≤
      (175616*64^4:ℝ≥0∞)*
        volume (wzCellShading ((N:ℝ)*D.thickness/128) (outputCells D E a N p) i) := by
  have hm : 0 < mesh D := half_pos h.1.2.1
  have he : 0 < (N:ℝ)*D.thickness/128 := by have hd := h.1.2.1; positivity
  have hvold : volume (wzCellShading (mesh D) (selectedCells E) i) ≠ ⊤ := by
    rw [volume_wzCellShading hm]
    finiteness
  have hvnew : volume (wzCellShading ((N:ℝ)*D.thickness/128) (outputCells D E a N p) i) ≠ ⊤ := by
    rw [volume_wzCellShading he]
    finiteness
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat] using
    selected_shading_mass_scale h original horiginal ha E hE N hN p i

lemma selected_parent_mass_le_source_enn {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (m : ℕ) (p : Parent) :
    ((2^m:ℕ):ℝ≥0∞)^3 * (∑i∈parentLabels D R a (2^m) p,
      volume (wzCellShading (mesh D) (selectedCells E) i)) ≤
        (175616*64^4:ℝ≥0∞)*wzTotalShadingVolume (source h R E a m p) := by
  rw [source_total_shading_eq_parent,mul_sum,mul_sum]
  exact sum_le_sum (fun i _hi =>
    selected_shading_mass_scale_enn h original horiginal ha E hE (2^m) (by positivity) p i)

lemma source_total_tubes_eq_parent {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent) :
    wzTotalTubeVolume (source h R E a m p) =
      ∑i∈parentLabels D R a (2^m) p,
        volume (markedUnitTube (NativeLocalParentGeometry.line D a (2^m) p i)
          (((2^m:ℕ):ℝ)*D.thickness/64)) := by
  exact sum_originalLabel (M:=ℝ≥0∞) (parentLabels D R a (2^m) p)
    (fun i => volume (markedUnitTube (NativeLocalParentGeometry.line D a (2^m) p i)
      (((2^m:ℕ):ℝ)*D.thickness/64)))

/-- Literal old selected cells on Q count exactly the selected old E.
Empty-shading labels in Q contribute zero and remain present. -/
lemma selected_parent_card {n : ℕ} (E : Finset (Fin n × Index))
    (Q : Finset (Fin n)) (hQ : ∀z∈E,z.1 ∈ Q) :
    (∑i∈Q,(selectedCells E i).card) = E.card := by
  calc
    _ = ∑i,(selectedCells E i).card := by
      apply sum_subset (subset_univ Q)
      intro i _hi hi
      have hempty : selectedCells E i = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro k hk
        exact hi (hQ (i,k) ((mem_selectedCells E i k).mp hk))
      rw [hempty,card_empty]
    _ = _ := by rw [←card_incidences,selected_incidences]

lemma selected_parent_shading_eq_card {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (E : Finset (Fin n × Index))
    (Q : Finset (Fin n)) (hQ : ∀z∈E,z.1 ∈ Q) :
    (∑i∈Q,volume (wzCellShading (mesh D) (selectedCells E) i)) =
      E.card*(ENNReal.ofReal (mesh D))^4 := by
  have hm : 0 < mesh D := half_pos hd
  simp_rw [volume_wzCellShading hm]
  rw [←sum_mul]
  congr 1
  exact_mod_cast selected_parent_card E Q hQ

lemma selected_parent_real_shading_eq_card {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (E : Finset (Fin n × Index))
    (Q : Finset (Fin n)) (hQ : ∀z∈E,z.1 ∈ Q) :
    (∑i∈Q,(volume (wzCellShading (mesh D) (selectedCells E) i)).toReal) =
      E.card*(mesh D)^4 := by
  have hm : 0 < mesh D := half_pos hd
  simp_rw [volume_wzCellShading hm,ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hm.le]
  rw [←sum_mul]
  congr 1
  exact_mod_cast selected_parent_card E Q hQ

end NativeLocalParentSource
