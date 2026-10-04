import Theorems.Thm_StickyKakeya4_original_three_dimensional_energy_regular_slice
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalEnergySliceWitness
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalAveragedSliceEnergy
open OriginalThreeDimensionalSlicePotentialCut OriginalThreeDimensionalEnergyRegularSlice
/-- The same original energy selection retains its selected ambient energy and
literal potential-cut identity, so later tube charges use that same source. -/
theorem exists_original_energy_regular_slice_witness {ι : Type*} (J : Finset ι)
    (Q : ι → Finset Point3) (G : ι → Finset Pair3) (Delta L E : ℝ)
    (hDelta : 0 < Delta) (hDelta1 : Delta ≤ 1) (hL : 0 < L) (hE : 0 < E)
    (hbox : ∀ k∈J,∀ p∈Q k,∀ j,|p j| ≤ 1)
    (hG : ∀ k∈J,G k⊆(Q k).product (Q k))
    (hpop : L ≤ ∑ k∈J,((G k).card : ℝ))
    (henergy : (∑ k∈J,sliceEnergy (Q k) Delta) ≤ E) :
    ∃ k∈J,∃ S : Finset Point3,
      S=goodPoints (Q k) Delta (4*E/L) ∧
      L*sliceEnergy (Q k) Delta ≤ E*(G k).card ∧
      L*sliceEnergy (Q k) Delta ≤ E*((Q k).card : ℝ)^2 ∧ S⊆Q k ∧
      3*((Q k).card : ℝ) ≤ 4*S.card ∧
      ((G k).card : ℝ) ≤ 2*((G k).filter (fun z => z.1∈S ∧ z.2∈S)).card ∧
      L*(S.card : ℝ)^2 ≤ 8*E*((G k).filter (fun z => z.1∈S ∧ z.2∈S)).card ∧
      ∀ p∈S,∀ r : ℝ,Delta ≤ r →
        ((S.filter (fun q => distance3 p q ≤ r)).card : ℝ) ≤ (8*E/L)*r*S.card := by
  obtain ⟨k,hk,hne,hratio,hdense,hselectedEnergy⟩ := exists_original_energy_regular_slice J Q G Delta L E
    hDelta hDelta1 hL hE hbox hG hpop henergy
  have hQ : (Q k).Nonempty := by
    obtain ⟨z,hz⟩ := hne
    exact ⟨z.1,(Finset.mem_product.mp (hG k hk hz)).1⟩
  let K := 4*E/L
  let S := goodPoints (Q k) Delta K
  have hK : 0 < K := by dsimp [K]; positivity
  have hcut := original_regular_slice_cut_retention (Q k) (G k) Delta L E hDelta hL hE hQ (hG k hk) hratio
  have hSQ : S⊆Q k := Finset.filter_subset _ _
  have hcard : (S.card : ℝ) ≤ (Q k).card := Nat.cast_le.mpr (Finset.card_le_card hSQ)
  have hreverse : ((Q k).card : ℝ) ≤ 2*S.card := by
    have hm : 3*((Q k).card : ℝ) ≤ 4*S.card := hcut.2
    linarith only [hm,Nat.cast_nonneg (α:=ℝ) (Q k).card]
  refine ⟨k,hk,S,rfl,hratio,hselectedEnergy,hSQ,hcut.2,hcut.1,?_,?_⟩
  · have hs := pow_le_pow_left₀ (Nat.cast_nonneg S.card) hcard 2
    have h1 := mul_le_mul_of_nonneg_left hs hL.le
    have h2 := mul_le_mul_of_nonneg_left hcut.1 (show 0 ≤ 4*E by positivity)
    change L*(S.card : ℝ)^2 ≤ 8*E*(retainedGraph (G k) (Q k) Delta K).card
    nlinarith only [h1,h2,hdense]
  · intro p hp r hr
    have hc := original_potential_cut_ball_count (Q k) Delta K hDelta p hp r hr
    have hrp := hDelta.trans_le hr
    have hh := mul_le_mul_of_nonneg_left hreverse (show 0 ≤ K*r by positivity)
    change ((S.filter (fun q => distance3 p q ≤ r)).card : ℝ) ≤ (8*E/L)*r*S.card
    have he : (K*r)*(2*S.card)=(8*E/L)*r*S.card := by dsimp [K]; ring
    exact hc.trans (hh.trans_eq he)

end OriginalThreeDimensionalEnergySliceWitness
