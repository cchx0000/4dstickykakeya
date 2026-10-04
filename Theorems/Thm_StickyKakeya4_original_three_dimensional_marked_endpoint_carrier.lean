import Theorems.Thm_StickyKakeya4_original_three_dimensional_marked_slice_witness
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace OriginalThreeDimensionalMarkedEndpointCarrier
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalDirectionGrid OriginalThreeDimensionalHeavySliceGraph
open OriginalThreeDimensionalSliceMaximizer NativeOriginalConcentratedPairGraph
open OriginalThreeDimensionalMarkedSliceIncidences OriginalThreeDimensionalSlicePotentialCut
open OriginalThreeDimensionalAveragedSliceEnergy OriginalThreeDimensionalExpandedSliceMultiplicity

def endpointCarrier (G : Finset Pair3) : Finset Point3 := G.image Prod.fst ∪ G.image Prod.snd

theorem original_graph_on_endpoint_carrier (G : Finset Pair3) :
    G⊆(endpointCarrier G).product (endpointCarrier G) := by
  intro z hz
  exact Finset.mem_product.mpr ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hz),
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hz)⟩

theorem original_endpoint_carrier_subset (G : Finset Pair3) (S : Finset Point3)
    (hG : G⊆S.product S) : endpointCarrier G⊆S := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_product.mp (hG hz)).1
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_product.mp (hG hz)).2

/-- Every retained endpoint remains in the actual RAW chosen slab, even
though its potential was measured against the larger original slice. -/
theorem original_marked_endpoints_raw_slab (P : Finset Point3) (G GP : Finset Pair3)
    (F : Pair3 → Finset DirectionLabel) (rho H : ℝ) (s : SliceLabel)
    (hF : ∀ z∈G,F z⊆goodDirections P rho H z)
    (hGP : GP⊆markedGraph P G rho H F s) :
    endpointCarrier GP⊆slabPoints P rho s.1 s.2 := by
  have hpair (z : Pair3) (hz : z∈GP) :
      z.1∈slabPoints P rho s.1 s.2 ∧ z.2∈slabPoints P rho s.1 s.2 := by
    obtain ⟨hzG,hd,hcode⟩ := Finset.mem_filter.mp (hGP hz)
    have hs := chosen_heavy_slab_code_spec P rho H z s.1 (hF z hzG hd)
    rw [hcode] at hs
    exact ⟨hs.2.2.1,hs.2.2.2⟩
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact (hpair z hz).1
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact (hpair z hz).2

/-- Passing to the actual endpoint carrier preserves the ORIGINAL ambient
potential bound. Its mass is never renormalized during this restriction. -/
theorem original_endpoint_full_potential (Q : Finset Point3) (GP : Finset Pair3)
    (Delta K : ℝ)
    (hGP : GP⊆(goodPoints Q Delta K).product (goodPoints Q Delta K)) :
    endpointCarrier GP⊆Q ∧
      ∀ p∈endpointCarrier GP,slicePotential Q Delta p ≤ K*Q.card := by
  have hs := original_endpoint_carrier_subset GP (goodPoints Q Delta K) hGP
  exact ⟨hs.trans (Finset.filter_subset _ _),fun p hp => (Finset.mem_filter.mp (hs hp)).2⟩

end OriginalThreeDimensionalMarkedEndpointCarrier
