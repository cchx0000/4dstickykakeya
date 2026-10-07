/- Actual remembered-cell witness preservation through the fixed
source Reference. This proves a label/readback fact only; later raw/translated
height coarsening and higher-fiber lower bounds are separate tasks. -/
import Theorems.Thm_StickyKakeya4_native_remembered_source_construction
import Theorems.Thm_StickyKakeya4_native_fixed_source_reference

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeRememberedReferenceTags
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeLocalParentSource NativeLocalCellCoherence
open NativeCubicalIncidenceCounts NativeTranslatedGrainHeightOverlap NativeGenericReferenceData
open NativeRememberedSourceMaps

/-- A total old-height tag on final native cell-time labels. Its value on
occupied bins is forced by the actual selected tagged relation B. -/
def oldHeight {nC : ℕ} (B : Finset (ℤ × (Fin nC × Index))) : ℤ → ℤ :=
  NativeMergedPointOffsets.pointOffset B finalTime Prod.fst

lemma oldHeight_readback {nC : ℕ} (B : Finset (ℤ × (Fin nC × Index)))
    (hcoherent : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (v : ℤ × (Fin nC × Index)) (hv : v∈B) : oldHeight B (finalTime v)=v.1 := by
  let : DecidableEq ℤ := Classical.decEq _
  obtain ⟨w,hw,ht,he⟩ := NativeMergedPointOffsets.pointOffset_witness B finalTime Prod.fst
    (finalTime v) (mem_image_of_mem _ hv)
  exact he.trans (hcoherent w hw v hv ht)

/-- Every new Reference edge lifts through the literal local-source cells
to an actual selected original occurrence. The selected OLD translated
height is read by the unchanged final cell index k(3), and is independent
of any other discarded antecedents of the intermediate pair. -/
theorem reference_edge_witness {n nC : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    {C : FiniteScaleSource nC} {etaC etaS tau seed e zeta : ℝ} {L g : ℕ}
    (hC : IsWangZakharovNativeFiniteInput C etaC) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nC × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nC × Index)))
    (hcoherent : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (hparent : ∀v∈selectedPairs D a m C c pA O B,
      v.1∈parentLabels C univ 0 (2^c) pA)
    (htau : 0<tau)
    (hS : IsWangZakharovNativeFiniteInput
      (source hC univ (selectedPairs D a m C c pA O B) 0 c pA) etaS)
    (ref : Reference hS tau htau seed e zeta L g)
    (x : Fin (parentLabels C univ 0 (2^c) pA).card × Index) (hx : x∈ref.E1) :
    ∃(v : Fin nC × Index) (z : Fin n × Index),
      (v,z)∈O ∧
      v.1=NativePaddedCellSource.originalLabel (parentLabels C univ 0 (2^c) pA) x.1 ∧
      localCellLabel C 0 (2^c) pA v=x.2 ∧
      (translatedHeight D a m z.2,originalPair (parentLabels C univ 0 (2^c) pA) x)∈B ∧
      translatedHeight D a m z.2=oldHeight B (x.2 (3:Fin 4)) := by
  let E := selectedPairs D a m C c pA O B
  let S := source hC univ E 0 c pA
  let cells := sourceCells C univ E 0 (2^c) pA
  have hmesh : mesh S=(((2^c:ℕ):ℝ)*C.thickness/128) := by
    change (((2^c:ℕ):ℝ)*C.thickness/64)/2= _
    ring
  have hOriginal : ref.original=cells := by
    apply NativeOriginalCellPresentationUnique.cells_eq_of_shading_eq
      (s:=mesh S) (half_pos hS.1.2.1)
    intro i
    have hr : S.shading i=wzCellShading (mesh S) cells i := by
      rw [hmesh]
      exact source_shading hC univ E 0 c pA i
    exact (ref.backbone.1 i).symm.trans hr
  have hxCells : x∈incidences cells := by
    rw [←hOriginal]
    exact (ref.core.1.trans (filter_subset _ _)) hx
  have himage : originalPair (parentLabels C univ 0 (2^c) pA) x∈
      E.image (localPair C 0 (2^c) pA) := by
    rw [←source_incidences_readback C univ E 0 (2^c) pA hparent]
    exact mem_image_of_mem _ hxCells
  obtain ⟨v,hv,hvx⟩ := mem_image.mp himage
  obtain ⟨z,hvz,hzB⟩ := selected_pair_witness D a m C c pA O B v hv
  have hzB' : (translatedHeight D a m z.2,originalPair (parentLabels C univ 0 (2^c) pA) x)∈B := by
    rwa [hvx] at hzB
  have hheight := oldHeight_readback B hcoherent _ hzB'
  refine ⟨v,z,hvz,congrArg Prod.fst hvx,congrArg Prod.snd hvx,hzB',?_⟩
  exact hheight.symm

end NativeRememberedReferenceTags
