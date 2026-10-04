import Theorems.Thm_StickyKakeya4_original_three_dimensional_bad_radius_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

noncomputable section
namespace OriginalThreeDimensionalGoodRadiusGraph
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalBadRadiusSelection

def goodPairs (P : Finset Point3) (delta zeta : ℝ) : Finset Pair3 :=
  P.product P\badPairs P delta zeta

def HasOriginalAllRadiusGraph (P : Finset Point3) (delta zeta error : ℝ) : Prop :=
  ∃ G : Finset Pair3,G⊆P.product P ∧ (1-error)*(P.card : ℝ)^2 ≤ G.card ∧
    ∀ z∈G,∀ R : ℝ,delta ≤ R → R ≤ 1 →
      ((physicalPairTube3 P R z).card : ℝ) ≤ delta^(-zeta)*R^2*P.card

/-- The literal complement of the actual all-radius bad graph has the
claimed original population and simultaneous physical tube bound. -/
theorem original_good_graph_from_small_bad (P : Finset Point3) (delta zeta error : ℝ)
    (hbad : ((badPairs P delta zeta).card : ℝ) ≤ error*(P.card : ℝ)^2) :
    HasOriginalAllRadiusGraph P delta zeta error := by
  have hsub : badPairs P delta zeta⊆P.product P := Finset.filter_subset _ _
  have hsum := Finset.card_sdiff_add_card_eq_card hsub
  have hsumR : ((goodPairs P delta zeta).card : ℝ)+(badPairs P delta zeta).card=
      (P.card : ℝ)*P.card := by
    have hh := congrArg (fun k : ℕ => (k:ℝ)) hsum
    simpa only [goodPairs,Finset.product_eq_sprod,Finset.card_product,Nat.cast_add,Nat.cast_mul] using hh
  refine ⟨goodPairs P delta zeta,Finset.sdiff_subset,?_,?_⟩
  · nlinarith only [hsumR,hbad]
  · intro z hz R hR hR1
    obtain ⟨hzP,hzBad⟩ := Finset.mem_sdiff.mp hz
    by_contra hh
    exact hzBad (Finset.mem_filter.mpr ⟨hzP,R,hR,hR1,lt_of_not_ge hh⟩)

end OriginalThreeDimensionalGoodRadiusGraph
