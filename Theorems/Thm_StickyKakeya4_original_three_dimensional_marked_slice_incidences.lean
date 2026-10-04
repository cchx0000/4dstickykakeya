import Theorems.Thm_StickyKakeya4_native_original_concentrated_pair_graph
import Theorems.Thm_StickyKakeya4_original_three_dimensional_expanded_slice_multiplicity
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalMarkedSliceIncidences
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalDirectionGrid OriginalThreeDimensionalHeavySliceGraph
open OriginalThreeDimensionalUnitSlabs OriginalThreeDimensionalSliceMaximizer
open OriginalThreeDimensionalExpandedSliceMultiplicity NativeOriginalConcentratedPairGraph

/-- The literal original pair/direction marks determine the slice labels. -/
def markedSlabs (P : Finset Point3) (G : Finset Pair3) (rho H : ℝ)
    (F : Pair3 → Finset DirectionLabel) : Finset SliceLabel :=
  G.biUnion (fun z => (F z).image (fun d => (d,chosenHeavySlabCode P rho H z d)))

/-- Retain only the actual marked pair/slice incidences. Merely belonging
to the same enlarged slice never creates a new graph edge. -/
def markedGraph (P : Finset Point3) (G : Finset Pair3) (rho H : ℝ)
    (F : Pair3 → Finset DirectionLabel) (s : SliceLabel) : Finset Pair3 :=
  G.filter (fun z => s.1∈F z ∧ chosenHeavySlabCode P rho H z s.1=s.2)

theorem original_marked_slice_graph_subset (P : Finset Point3) (G : Finset Pair3)
    (rho H : ℝ) (F : Pair3 → Finset DirectionLabel) (s : SliceLabel) :
    markedGraph P G rho H F s⊆G := Finset.filter_subset _ _

/-- Exact summation of the original marked incidences, including different
actual codes attached to the same direction on different pairs. -/
theorem original_marked_slice_incidence_sum (P : Finset Point3) (G : Finset Pair3)
    (rho H : ℝ) (F : Pair3 → Finset DirectionLabel) :
    (∑ s∈markedSlabs P G rho H F,((markedGraph P G rho H F s).card : ℝ))=
      ∑ z∈G,((F z).card : ℝ) := by
  let S := markedSlabs P G rho H F
  have hfiber (z : Pair3) (hz : z∈G) :
      S.filter (fun s => s.1∈F z ∧ chosenHeavySlabCode P rho H z s.1=s.2)=
        (F z).image (fun d => (d,chosenHeavySlabCode P rho H z d)) := by
    ext s
    constructor
    · intro hs
      obtain ⟨_hsS,hd,hk⟩ := Finset.mem_filter.mp hs
      exact Finset.mem_image.mpr ⟨s.1,hd,Prod.ext rfl hk⟩
    · intro hs
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image_of_mem _ hd⟩,hd,rfl⟩
  have hc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s:=S) (t:=G) (fun s z => s.1∈F z ∧ chosenHeavySlabCode P rho H z s.1=s.2)
  change (∑ s∈S,((markedGraph P G rho H F s).card : ℝ))=∑ z∈G,((F z).card : ℝ)
  have he (z : Pair3) (hz : z∈G) :
      (S.bipartiteBelow (fun s z => s.1∈F z ∧ chosenHeavySlabCode P rho H z s.1=s.2) z).card=(F z).card := by
    change (S.filter _).card=(F z).card
    rw [hfiber z hz]
    exact Finset.card_image_of_injective _ (fun d e hde => congrArg Prod.fst hde)
  have hh : (∑ s∈S,(markedGraph P G rho H F s).card)=∑ z∈G,(F z).card := by
    change (∑ s∈S,(G.bipartiteAbove (fun s z => s.1∈F z ∧ chosenHeavySlabCode P rho H z s.1=s.2) s).card)=_
    rw [hc]
    exact Finset.sum_congr rfl he
  exact_mod_cast hh

/-- Every marked original edge belongs to the correct original expanded
slice, and every used normal is an actual original grid label. -/
theorem original_marked_slice_geometry (P : Finset Point3) (G : Finset Pair3)
    (rho Delta H : ℝ) (F : Pair3 → Finset DirectionLabel) (hrho : 0 ≤ rho)
    (hwidth : 3*rho ≤ Delta)
    (hF : ∀ z∈G,F z⊆goodDirections P rho H z) :
    (∀ s∈markedSlabs P G rho H F,s.1∈normalGrid rho) ∧
    ∀ s,markedGraph P G rho H F s⊆
      (enlargedSlice P rho s.1 s.2 Delta).product (enlargedSlice P rho s.1 s.2 Delta) := by
  constructor
  · intro s hs
    obtain ⟨z,hz,hs⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hs
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hF z hz hd)).1).1
  · intro s z hz
    obtain ⟨hzG,hd,hk⟩ := Finset.mem_filter.mp hz
    have hs := chosen_heavy_slab_code_spec P rho H z s.1 (hF z hzG hd)
    rw [hk] at hs
    have hmem (x : Point3) (hx : x∈slabPoints P rho s.1 s.2) : x∈enlargedSlice P rho s.1 s.2 Delta :=
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
        (original_slab_in_unit_slab P rho s.1 s.2 hrho x hx).trans hwidth⟩
    exact Finset.mem_product.mpr ⟨hmem z.1 hs.2.2.1,hmem z.2 hs.2.2.2⟩

end OriginalThreeDimensionalMarkedSliceIncidences
