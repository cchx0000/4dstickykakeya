/- UNVERIFIED literal same-reference row and occurrence readback.
The selected intermediate source keeps the original sparse T rows. Later
old-phase restrictions are made on the unchanged original witnesses. -/
import Theorems.Thm_StickyKakeya4_native_remembered_source_maps
import Theorems.Thm_StickyKakeya4_native_same_Q_source_restriction

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeRememberedOccurrenceReadback
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeLocalParentSource NativeRelativeCoarseReadback
open NativeRelativeParentLabels NativeRememberedSourceMaps NativeIntermediateParentPopulation
open NativeCoarseCellSource NativeCoarseDirectionThinning NativeCoarseSourceParentReadback
open NativeJointKeyDescent

section Actual
variable {n : ℕ} {D : FiniteScaleSource n} {eta etaRef a : ℝ}
  (h : IsWangZakharovNativeFiniteInput D eta) (backbone : Finset (Fin n))
  (Eref T : Finset (Fin n × Index)) (level m b : ℕ) (p : Parent)
  (hp : (parentLabels D backbone a (2^m) p).Nonempty)
  (hRef : IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h backbone Eref a m p) etaRef)

/-- These are the literal finite rows of the actual same-Q coarse source. -/
def actualRows (Q : Finset Parent) : Fin Q.card → Finset Index :=
  intermediateCells (D:=NativeLocalParentSource.source h backbone Eref a m p)
    0 (level-m+6) b Q (representative hRef univ 0 (2^b))
    (incidences (sourceCells D backbone T a (2^m) p))

/-- Exact finite row identity, stronger than equality of the shaded unions. -/
theorem actual_rows_readback
    (hT : ∀z∈T,z.1∈parentLabels D backbone a (2^m) p)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level) (hb : b≤level-m+6)
    (Q : Finset Parent) (i : Fin Q.card) :
    actualRows h backbone Eref T level m b p hRef Q i=
      (((T.image (doublePair h backbone a m p hp (2^b))).filter
        (fun z => z.1=parentIndex Q i)).image Prod.snd) := by
  have hc := NativeCurrentReferenceReadback.selected_relative_incidence_image
    h backbone Eref T a m p hp (2^b) (NativeCoarseDyadicShading.block (level-m+6) b) hT hRef
    (NativeCoarseDyadicShading.block_mesh (local_source_dyadic h backbone Eref a level m p hdy hm) hb)
  unfold actualRows intermediateCells NativeCoarseShadingCapacity.rows
  rw [hc]

/-- Every retained original witness in Q has a genuine intermediate row
occurrence, and there are no other original witnesses in the occurrence image. -/
theorem original_image
    (hT : ∀z∈T,z.1∈parentLabels D backbone a (2^m) p)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level) (hb : b≤level-m+6)
    (Q : Finset Parent) (A : Finset (Fin n × Index)) (hAT : A⊆T) :
    (occurrences h backbone a m b p hp Q (actualRows h backbone Eref T level m b p hRef Q) A).image Prod.snd=
      NativeSameQSourceRestriction.restrict D a m b p Q A := by
  ext z
  constructor
  · intro hz
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
    obtain ⟨_hvRows,hvA,hphase,_hcell⟩ := (mem_occurrences h backbone a m b p hp Q _ A v).mp hv
    apply mem_filter.mpr
    refine ⟨hvA,?_⟩
    rw [←hphase]
    exact parentIndex_mem Q v.1.1
  · intro hz
    obtain ⟨hzA,hzQ⟩ := mem_filter.mp hz
    have hrange : relativeLabel D a (2^m) p (2^b) z.1∈Set.range (parentIndex Q) := by
      rw [parentIndex_range]
      exact hzQ
    obtain ⟨i,hi⟩ := hrange
    let k := (doublePair h backbone a m p hp (2^b) z).2
    have hk : k∈actualRows h backbone Eref T level m b p hRef Q i := by
      rw [actual_rows_readback h backbone Eref T level m b p hp hRef hT hdy hm hb Q i]
      refine mem_image.mpr ⟨doublePair h backbone a m p hp (2^b) z,
        mem_filter.mpr ⟨mem_image_of_mem _ (hAT hzA),?_⟩,rfl⟩
      exact hi.symm
    refine mem_image.mpr ⟨((i,k),z),?_,rfl⟩
    apply (mem_occurrences h backbone a m b p hp Q _ A _).mpr
    exact ⟨(mem_incidences _ _ _).mpr hk,hzA,hi,rfl⟩

/-- An original w-phase occurrence is in the corresponding ACTUAL current
parent, whose intercept label is divided by512. This derives the current
parent condition from Q's actual representatives and dyadic ancestry. -/
theorem occurrence_current_parent
    (Q : Finset Parent)
    (hQ : Q⊆(univ : Finset (Fin (parentLabels D backbone a (2^m) p).card)).image
      (parentLabel (NativeLocalParentSource.source h backbone Eref a m p) 0 (2^b)))
    (hsep : ∀q∈Q,∀q'∈Q,q≠q' → 64/((2^b:ℕ):ℝ) ≤
      dist (direction ((NativeLocalParentSource.source h backbone Eref a m p).line
        (representative hRef univ 0 (2^b) q)))
      (direction ((NativeLocalParentSource.source h backbone Eref a m p).line
        (representative hRef univ 0 (2^b) q'))))
    (A : Finset (Fin n × Index)) (c : ℕ) (hc : c≤b) (qOld : Parent)
    (hphase : ∀z∈A,relativeLabel D a (2^m) p (2^c) z.1=qOld) :
    let C := NativeCoarseCellSource.source hRef 0 (level-m+6) b Q
      (representative hRef univ 0 (2^b)) (incidences (sourceCells D backbone T a (2^m) p)) hsep
    ∀z∈occurrences h backbone a m b p hp Q (actualRows h backbone Eref T level m b p hRef Q) A,
      parentLabel C 0 (2^c) z.1.1=zeroProjection qOld := by
  intro C z hz
  obtain ⟨_hzRows,hzA,hzPhase,_hzCell⟩ := (mem_occurrences h backbone a m b p hp Q _ A z).mp hz
  have hrep : ∀q∈Q,parentLabel (NativeLocalParentSource.source h backbone Eref a m p) 0 (2^b)
      (representative hRef univ 0 (2^b) q)=q :=
    fun q hq => (representative_spec hRef univ 0 (2^b) (hQ hq)).2
  rw [NativeIntermediateParentPopulation.parent_from_ancestor hRef 0 (level-m+6) b Q
    (representative hRef univ 0 (2^b)) (incidences (sourceCells D backbone T a (2^m) p))
    hsep hrep c hc z.1.1,hzPhase,relative_ancestor D a (2^m) p b c hc z.2.1,hphase z.2 hzA]

end Actual
end NativeRememberedOccurrenceReadback
