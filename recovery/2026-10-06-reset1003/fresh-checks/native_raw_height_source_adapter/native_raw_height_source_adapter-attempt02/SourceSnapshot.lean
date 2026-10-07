/- Literal original-grid-height tags and their exact adapter to the verified
remembered-source construction. The original incidence, original mark, and
intermediate row witness are retained throughout. -/
import Theorems.Thm_StickyKakeya4_native_remembered_source_construction

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeRawHeightSourceAdapter
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeRelativeParentLabels NativeRelativeCoarseReadback
open NativeLocalParentSource NativeCubicalIncidenceCounts NativeRememberedSourceMaps
open NativeTranslatedGrainHeightOverlap NativeRememberedOccurrenceReadback

/-- The first coordinate is the TRUE ORIGINAL grid height, before either
coarsening or translation. The second coordinate is the actual final pair. -/
def rawTaggedKey {n nA : ℕ} (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (z : (Fin nA × Index) × (Fin n × Index)) : ℤ × (Fin nA × Index) :=
  (z.2.2 (3:Fin 4),NativeLocalCellCoherence.localPair C 0 (2^c) pA z.1)

/-- The literal translated-height formula evaluated on an original grid
height. It uses the original source's mesh and original translation. -/
def rawTranslatedHeight {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (t : ℤ) : ℤ :=
  ⌊(mesh D*(((t-shift D a:ℤ):ℝ)+1/2))/(64/((2^m:ℕ):ℝ))⌋

lemma translatedHeight_eq_raw {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (k : Index) : translatedHeight D a m k=rawTranslatedHeight D a m (k (3:Fin 4)) := rfl

/-- Equality of true original heights suffices for the old-height geometry. -/
lemma translatedHeight_eq_of_original_height_eq {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) {k l : Index} (h : k (3:Fin 4)=l (3:Fin 4)) :
    translatedHeight D a m k=translatedHeight D a m l := by
  rw [translatedHeight_eq_raw,translatedHeight_eq_raw,h]

def translatedTag {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (v : ℤ × (Fin nA × Index)) : ℤ × (Fin nA × Index) :=
  (rawTranslatedHeight D a m v.1,v.2)

def translatedTags {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (B : Finset (ℤ × (Fin nA × Index))) : Finset (ℤ × (Fin nA × Index)) :=
  B.image (translatedTag D a m)

lemma taggedKey_eq_translatedTag {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (z : (Fin nA × Index) × (Fin n × Index)) :
    taggedKey D a m C c pA z=translatedTag D a m (rawTaggedKey C c pA z) := rfl

lemma translatedTag_finalTime {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (v : ℤ × (Fin nA × Index)) :
    finalTime (translatedTag D a m v)=finalTime v := rfl

/-- Only the height coordinate is changed; the finite final-pair image is exact. -/
theorem translatedTags_final_image {n nA : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (B : Finset (ℤ × (Fin nA × Index))) :
    (translatedTags D a m B).image Prod.snd=B.image Prod.snd := by
  simp only [translatedTags,image_image,Function.comp_def,translatedTag]

/-- The raw-to-translated map need not be injective globally. It is injective
on a selected set with one original height per final time, since its unchanged
final pair determines that time. -/
theorem translatedTag_injOn {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (B : Finset (ℤ × (Fin nA × Index)))
    (hcoherent : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) :
    Set.InjOn (translatedTag D a m) (↑B : Set (ℤ × (Fin nA × Index))) := by
  intro v hv w hw he
  have hp := congrArg (fun u : ℤ × (Fin nA × Index) => u.2) he
  change v.2=w.2 at hp
  exact Prod.ext (hcoherent v hv w hw
    (congrArg (fun u : Fin nA × Index => u.2 (3:Fin 4)) hp)) hp

theorem translatedTags_card {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (B : Finset (ℤ × (Fin nA × Index)))
    (hcoherent : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) :
    (translatedTags D a m B).card=B.card := by
  exact card_image_iff.mpr (translatedTag_injOn D a m B hcoherent)

/-- This is exactly the uniqueness premise required by rank_two_union. -/
theorem translatedTags_coherent {n nA : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (B : Finset (ℤ × (Fin nA × Index)))
    (hcoherent : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) :
    ∀v∈translatedTags D a m B,∀w∈translatedTags D a m B,
      finalTime v=finalTime w → v.1=w.1 := by
  intro v hv w hw he
  obtain ⟨v',hv',rfl⟩ := mem_image.mp hv
  obtain ⟨w',hw',rfl⟩ := mem_image.mp hw
  exact congrArg (rawTranslatedHeight D a m) (hcoherent v' hv' w' hw' he)

/-- Membership comes from actual occurrence witnesses, not an assumed bound
on any map fiber. -/
theorem translatedTags_subset {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) (hB : B⊆O.image (rawTaggedKey C c pA)) :
    translatedTags D a m B⊆O.image (taggedKey D a m C c pA) := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
  obtain ⟨z,hz,rfl⟩ := mem_image.mp (hB hw)
  exact mem_image.mpr ⟨z,hz,taggedKey_eq_translatedTag D a m C c pA z⟩

def rawSelectedOccurrences {n nA : ℕ} (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) := O.filter (fun z => rawTaggedKey C c pA z∈B)

def rawSelectedPairs {n nA : ℕ} (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) : Finset (Fin nA × Index) :=
  (rawSelectedOccurrences C c pA O B).image Prod.fst

theorem raw_selected_tagged_image {n nA : ℕ} (C : FiniteScaleSource nA)
    (c : ℕ) (pA : Parent) (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) (hB : B⊆O.image (rawTaggedKey C c pA)) :
    (rawSelectedOccurrences C c pA O B).image (rawTaggedKey C c pA)=B := by
  ext v
  constructor
  · intro hv
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp hz).2
  · intro hv
    obtain ⟨z,hz,rfl⟩ := mem_image.mp (hB hv)
    exact mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,hv⟩,rfl⟩

theorem raw_selected_final_image {n nA : ℕ} (C : FiniteScaleSource nA)
    (c : ℕ) (pA : Parent) (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) (hB : B⊆O.image (rawTaggedKey C c pA)) :
    (rawSelectedPairs C c pA O B).image (NativeLocalCellCoherence.localPair C 0 (2^c) pA)=
      B.image Prod.snd := by
  calc
    _ = ((rawSelectedOccurrences C c pA O B).image (rawTaggedKey C c pA)).image Prod.snd := by
      simp only [rawSelectedPairs,image_image,Function.comp_def,rawTaggedKey]
    _ = _ := congrArg (fun S : Finset (ℤ × (Fin nA × Index)) => S.image Prod.snd)
      (raw_selected_tagged_image C c pA O B hB)

/-- Translating a raw tag may admit extra intermediate witnesses. Their final
local pairs are nevertheless exactly the final pairs retained by raw selection. -/
theorem translated_selected_final_image {n nA : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) (hB : B⊆O.image (rawTaggedKey C c pA)) :
    (selectedPairs D a m C c pA O (translatedTags D a m B)).image
      (NativeLocalCellCoherence.localPair C 0 (2^c) pA)=B.image Prod.snd := by
  rw [selected_final_image D a m C c pA O (translatedTags D a m B)
    (translatedTags_subset D a m C c pA O B hB)]
  exact translatedTags_final_image D a m B

theorem translated_selected_final_card {n nA : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) (hB : B⊆O.image (rawTaggedKey C c pA))
    (hcoherent : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) :
    ((selectedPairs D a m C c pA O (translatedTags D a m B)).image
      (NativeLocalCellCoherence.localPair C 0 (2^c) pA)).card=B.card := by
  rw [translated_selected_final_image D a m C c pA O B hB]
  exact final_image_card B hcoherent

/-- Final pair membership is precisely literal output-cell membership. -/
lemma final_pair_mem_iff_outputCell {nA : ℕ} (C : FiniteScaleSource nA)
    (c : ℕ) (pA : Parent) (E : Finset (Fin nA × Index)) (i : Fin nA) (k : Index) :
    (i,k)∈E.image (NativeLocalCellCoherence.localPair C 0 (2^c) pA) ↔
      k∈outputCells C E 0 (2^c) pA i := by
  constructor
  · intro hz
    obtain ⟨⟨j,l⟩,hl,he⟩ := mem_image.mp hz
    have hji : j=i := congrArg Prod.fst he
    subst j
    exact (mem_outputCells C E 0 (2^c) pA i k).mpr ⟨l,hl,congrArg Prod.snd he⟩
  · intro hk
    obtain ⟨l,hl,he⟩ := (mem_outputCells C E 0 (2^c) pA i k).mp hk
    exact mem_image.mpr ⟨(i,l),hl,Prod.ext rfl he⟩

/-- The actual final rows, hence their physical cell support, are unchanged
by the raw-to-translated adapter. The fixed parent backbone is also unchanged. -/
theorem translated_selected_sourceCells_eq_raw {n nA : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (R : Finset (Fin nA)) (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) (hB : B⊆O.image (rawTaggedKey C c pA)) :
    sourceCells C R (selectedPairs D a m C c pA O (translatedTags D a m B)) 0 (2^c) pA=
      sourceCells C R (rawSelectedPairs C c pA O B) 0 (2^c) pA := by
  have he : (selectedPairs D a m C c pA O (translatedTags D a m B)).image
      (NativeLocalCellCoherence.localPair C 0 (2^c) pA)=
        (rawSelectedPairs C c pA O B).image (NativeLocalCellCoherence.localPair C 0 (2^c) pA) := by
    rw [translated_selected_final_image D a m C c pA O B hB,
      raw_selected_final_image C c pA O B hB]
  funext i
  ext k
  change k∈outputCells C _ 0 (2^c) pA _ ↔ k∈outputCells C _ 0 (2^c) pA _
  rw [←final_pair_mem_iff_outputCell,←final_pair_mem_iff_outputCell,he]

/-- Every final pair has a retained ORIGINAL-height witness from the same O,
even if translated selection chose a different intermediate representative. -/
theorem translated_selected_raw_witness {n nA : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) (hB : B⊆O.image (rawTaggedKey C c pA))
    (v : Fin nA × Index)
    (hv : v∈selectedPairs D a m C c pA O (translatedTags D a m B)) :
    ∃z∈O,rawTaggedKey C c pA z∈B ∧
      NativeLocalCellCoherence.localPair C 0 (2^c) pA z.1=
        NativeLocalCellCoherence.localPair C 0 (2^c) pA v := by
  have hi := mem_image_of_mem (NativeLocalCellCoherence.localPair C 0 (2^c) pA) hv
  rw [translated_selected_final_image D a m C c pA O B hB] at hi
  obtain ⟨u,hu,huv⟩ := mem_image.mp hi
  obtain ⟨z,hz,hzu⟩ := mem_image.mp (hB hu)
  refine ⟨z,hz,?_,?_⟩
  · rw [hzu]
    exact hu
  · exact (congrArg Prod.snd hzu).trans huv

/-- A literal occurrence is uniquely determined by its original incidence:
the old phase fixes its intermediate tube and doublePair fixes its shadow. -/
theorem occurrence_original_injective {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (backbone : Finset (Fin n))
    (a : ℝ) (m b : ℕ) (p : Parent)
    (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (Q : Finset Parent) (cells : Fin Q.card → Finset Index)
    (A : Finset (Fin n × Index)) :
    Set.InjOn Prod.snd (↑(occurrences h backbone a m b p hp Q cells A) :
      Set ((Fin Q.card × Index) × (Fin n × Index))) := by
  intro z hz w hw he
  obtain ⟨_hzRows,_hzA,hzPhase,hzCell⟩ := (mem_occurrences h backbone a m b p hp Q cells A z).mp hz
  obtain ⟨_hwRows,_hwA,hwPhase,hwCell⟩ := (mem_occurrences h backbone a m b p hp Q cells A w).mp hw
  apply Prod.ext _ he
  apply Prod.ext
  · apply NativeCoarseCellSource.parentIndex_injective Q
    rw [hzPhase,hwPhase,he]
  · exact hzCell.trans ((congrArg
      (fun u : Fin n × Index => (doublePair h backbone a m p hp (2^b) u).2) he).trans hwCell.symm)

/-- No multiplicity is introduced by retaining occurrences of the actual rows. -/
theorem actual_occurrences_card {n : ℕ} {D : FiniteScaleSource n} {eta etaRef a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (backbone : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (level m b : ℕ) (p : Parent)
    (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (hRef : IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h backbone Eref a m p) etaRef)
    (hT : ∀z∈T,z.1∈parentLabels D backbone a (2^m) p)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level) (hb : b≤level-m+6)
    (Q : Finset Parent) (A : Finset (Fin n × Index)) (hAT : A⊆T) :
    (occurrences h backbone a m b p hp Q (actualRows h backbone Eref T level m b p hRef Q) A).card=
      (NativeSameQSourceRestriction.restrict D a m b p Q A).card := by
  rw [←original_image h backbone Eref T level m b p hp hRef hT hdy hm hb Q A hAT]
  exact (card_image_iff.mpr (occurrence_original_injective h backbone a m b p hp Q _ A)).symm

/-- Exact existence and uniqueness over the unchanged original source. -/
theorem actual_occurrence_exists_unique {n : ℕ} {D : FiniteScaleSource n} {eta etaRef a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (backbone : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (level m b : ℕ) (p : Parent)
    (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (hRef : IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h backbone Eref a m p) etaRef)
    (hT : ∀z∈T,z.1∈parentLabels D backbone a (2^m) p)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level) (hb : b≤level-m+6)
    (Q : Finset Parent) (A : Finset (Fin n × Index)) (hAT : A⊆T)
    (z : Fin n × Index) (hz : z∈NativeSameQSourceRestriction.restrict D a m b p Q A) :
    ∃! v : (Fin Q.card × Index) × (Fin n × Index),
      v∈occurrences h backbone a m b p hp Q (actualRows h backbone Eref T level m b p hRef Q) A ∧ v.2=z := by
  have hzImage : z∈(occurrences h backbone a m b p hp Q
      (actualRows h backbone Eref T level m b p hRef Q) A).image Prod.snd := by
    rw [original_image h backbone Eref T level m b p hp hRef hT hdy hm hb Q A hAT]
    exact hz
  obtain ⟨v,hv,hvz⟩ := mem_image.mp hzImage
  refine ⟨v,⟨hv,hvz⟩,?_⟩
  intro w hw
  exact occurrence_original_injective h backbone a m b p hp Q _ A hw.1 hv (hw.2.trans hvz.symm)

/-- Weighted height selection is performed on ORIGINAL grid heights and only
then converted to the exact input of the established remembered-height union
bound. The sole numerical input here is the actual raw-height count per final
time, to be supplied by the original-incidence floor geometry. -/
theorem select_raw_height {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index))) {K : ℝ} (hK : 0≤K)
    (hCard : ∀j,
      ((((O.image (rawTaggedKey C c pA)).filter (fun v => finalTime v=j)).image Prod.fst).card:ℝ)≤K) :
    ∃B⊆O.image (rawTaggedKey C c pA),
      ((O.image (rawTaggedKey C c pA)).card:ℝ)≤
        K*((selectedPairs D a m C c pA O (translatedTags D a m B)).image
          (NativeLocalCellCoherence.localPair C 0 (2^c) pA)).card ∧
      (∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) ∧
      translatedTags D a m B⊆O.image (taggedKey D a m C c pA) ∧
      (∀v∈translatedTags D a m B,∀w∈translatedTags D a m B,
        finalTime v=finalTime w → v.1=w.1) ∧
      (selectedPairs D a m C c pA O (translatedTags D a m B)).image
        (NativeLocalCellCoherence.localPair C 0 (2^c) pA)=B.image Prod.snd := by
  let S := O.image (rawTaggedKey C c pA)
  have hNat (j : ℤ) : ((S.filter (fun v => finalTime v=j)).image Prod.fst).card≤⌊K⌋₊ :=
    (Nat.le_floor_iff hK).mpr (hCard j)
  obtain ⟨B,hBS,hret,_hImage,_hLocal,hCoherent⟩ :=
    NativeFiniteImageWeightedChoice.select_per_cell S (fun _ => 1) finalTime Prod.fst ⌊K⌋₊ hNat
  have hrNat : S.card≤⌊K⌋₊*B.card := by simpa [NativeMatrixHeightWholePoint.mass] using hret
  have hr : (S.card:ℝ)≤(⌊K⌋₊:ℝ)*(B.card:ℝ) := by exact_mod_cast hrNat
  refine ⟨B,hBS,?_,hCoherent,translatedTags_subset D a m C c pA O B hBS,
    translatedTags_coherent D a m B hCoherent,
    translated_selected_final_image D a m C c pA O B hBS⟩
  rw [translated_selected_final_card D a m C c pA O B hBS hCoherent]
  exact hr.trans (mul_le_mul_of_nonneg_right (Nat.floor_le hK) (Nat.cast_nonneg _))

end NativeRawHeightSourceAdapter
end
