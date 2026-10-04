import Theorems.Thm_StickyKakeya4_original_three_dimensional_raw_owner_net
import Theorems.Thm_StickyKakeya4_original_three_dimensional_owner_query_tube
import Theorems.Thm_StickyKakeya4_original_balanced_owner_counts
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000

noncomputable section
namespace OriginalThreeDimensionalOwnerGraphRichness
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalVoronoiFibers
open OriginalThreeDimensionalOwnerQueryTube OriginalFiniteCellWeights OriginalBalancedOwnerCounts

def ownerGraph (G : Finset Pair3) (C : Finset Point3) (hC : C.Nonempty) : Finset Pair3 :=
  occupied G (pairCode (originalOwner C hC))

theorem original_owner_graph_subset (G : Finset Pair3) (C : Finset Point3) (hC : C.Nonempty) :
    ownerGraph G C hC⊆C.product C := by
  intro e he
  obtain ⟨z,_hz,rfl⟩ := Finset.mem_image.mp he
  exact Finset.mem_product.mpr ⟨original_owner_mem C hC z.1,original_owner_mem C hC z.2⟩

/-- The image of actual original rich points lies in the physical tube
through the actual endpoint owners, including the required Delta/r loss. -/
theorem original_owner_tube_image_subset (P S C : Finset Point3) (hC : C.Nonempty)
    (z : Pair3) (Delta r : ℝ) (hDelta : 0 < Delta) (hsmall : 32*Delta ≤ 1) (hr : 0 < r)
    (hSP : S⊆P) (hz : z∈S.product S) (hbox : ∀ p∈P,∀ j,|p j| ≤ 1)
    (hsep : r ≤ distance3 z.1 z.2)
    (hnear : ∀ x∈S,distance3 x (originalOwner C hC x) < Delta/4) :
    occupied (physicalPairTube3 S (32*Delta) z) (originalOwner C hC)⊆
      physicalPairTube3 C (200*Delta/r) (pairCode (originalOwner C hC) z) := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hxS,hxt⟩ := Finset.mem_filter.mp hx
  obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp hz
  refine Finset.mem_filter.mpr ⟨original_owner_mem C hC x,?_⟩
  exact original_three_owner_tube z.1 z.2 x (originalOwner C hC z.1) (originalOwner C hC z.2)
    (originalOwner C hC x) Delta r hDelta hsmall hr
    (hbox z.1 (hSP hz1)) (hbox z.2 (hSP hz2)) (hbox x (hSP hxS)) hsep
    (hnear z.1 hz1).le (hnear z.2 hz2).le (hnear x hxS).le hxt

/-- The actual balanced original owner fibers carry the original dense,
rich graph to a genuinely unweighted owner graph. Each output edge retains
an actual original witness; source populations are normalized by Q. -/
theorem original_dense_rich_owner_graph (P Q S C : Finset Point3) (hC : C.Nonempty)
    (G : Finset Pair3) (Delta r M A lam k : ℝ)
    (hDelta : 0 < Delta) (hsmall : 32*Delta ≤ 1) (hr : 0 < r) (hDeltar : Delta ≤ r)
    (hM : 0 < M) (hA : 0 ≤ A) (hlam : 0 < lam) (hk : 0 ≤ k)
    (hSP : S⊆P) (hSU : S⊆originalCarrier P C hC (Delta/4))
    (hUQ : originalCarrier P C hC (Delta/4)⊆Q)
    (hG : G⊆S.product S) (hbox : ∀ p∈P,∀ j,|p j| ≤ 1)
    (hnear : ∀ x∈S,distance3 x (originalOwner C hC x) < Delta/4)
    (hsep : ∀ z∈G,r ≤ distance3 z.1 z.2)
    (hmin : ∀ c∈C,M ≤ ((originalFiber P C hC (Delta/4) c).card : ℝ))
    (hmax : ∀ c∈C,((originalFiber P C hC (Delta/4) c).card : ℝ) ≤ A*M)
    (hdense : lam*(Q.card : ℝ)^2 ≤ G.card)
    (hrich : ∀ z∈G,k*Q.card ≤ ((physicalPairTube3 S (32*Delta) z).card : ℝ)) :
    ownerGraph G C hC⊆C.product C ∧ (ownerGraph G C hC).Nonempty ∧
      lam*(C.card : ℝ)^2 ≤ A^2*(ownerGraph G C hC).card ∧
      ∀ e∈ownerGraph G C hC,
        ∃ z∈G,pairCode (originalOwner C hC) z=e ∧
          r/2 ≤ distance3 e.1 e.2 ∧
          k*C.card ≤ A*(physicalPairTube3 C (200*Delta/r) e).card := by
  let U := originalCarrier P C hC (Delta/4)
  let f := originalOwner C hC
  have hGU : G⊆U.product U := by
    intro z hz
    obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp (hG hz)
    exact Finset.mem_product.mpr ⟨hSU hz1,hSU hz2⟩
  have hmap (x : Point3) (_hx : x∈U) : f x∈C := original_owner_mem C hC x
  have hmin' (c : Point3) (hc : c∈C) : M ≤ pointWeight U f c := hmin c hc
  have hmax' (c : Point3) (hc : c∈C) : pointWeight U f c ≤ A*M := hmax c hc
  have hcount := original_unweighted_owner_graph Q U C G f M A lam hM hA hlam.le
    hUQ hGU hmap hmin' hmax' hdense
  have hcn : (0:ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hGn : (ownerGraph G C hC).Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0:ℝ) < A^2*(ownerGraph G C hC).card :=
      (show 0 < lam*(C.card : ℝ)^2 by positivity).trans_le hcount
    have hc : (0:ℝ) < (ownerGraph G C hC).card := by
      by_contra hn
      have he : ((ownerGraph G C hC).card : ℝ)=0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
      rw [he,mul_zero] at hh
      exact (lt_irrefl _ hh)
    exact_mod_cast hc
  refine ⟨original_owner_graph_subset G C hC,hGn,hcount,?_⟩
  intro e he
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp (hG hz)
  have hownerSep := original_owner_pair_separation z.1 z.2 (f z.1) (f z.2) Delta r
    (hsep z hz) hDeltar (hnear z.1 hz1).le (hnear z.2 hz2).le
  refine ⟨z,hz,rfl,hownerSep,?_⟩
  let X := physicalPairTube3 S (32*Delta) z
  have hXU : X⊆U := (Finset.filter_subset _ _).trans hSU
  have hmass := original_owner_rich_image Q U X C f M A k hM hk hUQ hXU hmap hmin' hmax' (hrich z hz)
  have hsub := original_owner_tube_image_subset P S C hC z Delta r hDelta hsmall hr
    hSP (hG hz) hbox (hsep z hz) hnear
  exact hmass.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hsub)) hA)

end OriginalThreeDimensionalOwnerGraphRichness
