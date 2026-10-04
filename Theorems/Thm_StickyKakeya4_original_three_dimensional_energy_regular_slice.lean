import Theorems.Thm_StickyKakeya4_original_three_dimensional_slice_potential_cut
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalEnergyRegularSlice
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalAveragedSliceEnergy
open OriginalThreeDimensionalSlicePotentialCut

private theorem positive_weighted_ratio {ι : Type*} (J : Finset ι)
    (n u : ι → ℝ) (L E : ℝ) (hL : 0 < L) (hE : 0 < E)
    (hn : ∀ k∈J,0 ≤ n k) (hu : ∀ k∈J,0 ≤ u k)
    (hpop : L ≤ ∑ k∈J,n k) (henergy : (∑ k∈J,u k) ≤ E) :
    ∃ k∈J,0 < n k ∧ L*u k ≤ E*n k := by
  have hex : ∃ k∈J,0 < n k := by
    by_contra hf
    push Not at hf
    have he : (∑ k∈J,n k)=0 := Finset.sum_eq_zero (fun k hk => le_antisymm (hf k hk) (hn k hk))
    rw [he] at hpop
    exact (not_le_of_gt hL) hpop
  by_contra hf
  push Not at hf
  have hle (k : ι) (hk : k∈J) : E*n k ≤ L*u k := by
    by_cases hp : 0 < n k
    · exact (hf k hk hp).le
    · have he : n k=0 := le_antisymm (le_of_not_gt hp) (hn k hk)
      rw [he,mul_zero]
      exact mul_nonneg hL.le (hu k hk)
  obtain ⟨k,hk,hkp⟩ := hex
  have hs := Finset.sum_lt_sum hle ⟨k,hk,hf k hk hkp⟩
  simp only [← Finset.mul_sum] at hs
  have hlo := mul_le_mul_of_nonneg_left hpop hE.le
  have hhi := mul_le_mul_of_nonneg_left henergy hL.le
  nlinarith only [hs,hlo,hhi]

/-- The actual graph/energy totals select one original slice with both
energy control and dense original pairs. No dyadic mass uniformization
or independent desired density estimate is needed. -/
theorem exists_original_energy_regular_slice {ι : Type*} (J : Finset ι)
    (Q : ι → Finset Point3) (G : ι → Finset Pair3) (Delta L E : ℝ)
    (hDelta : 0 < Delta) (hDelta1 : Delta ≤ 1) (hL : 0 < L) (hE : 0 < E)
    (hbox : ∀ k∈J,∀ p∈Q k,∀ j,|p j| ≤ 1)
    (hG : ∀ k∈J,G k⊆(Q k).product (Q k))
    (hpop : L ≤ ∑ k∈J,((G k).card : ℝ))
    (henergy : (∑ k∈J,sliceEnergy (Q k) Delta) ≤ E) :
    ∃ k∈J,(G k).Nonempty ∧ L*sliceEnergy (Q k) Delta ≤ E*(G k).card ∧
      L*((Q k).card : ℝ)^2 ≤ 4*E*(G k).card ∧
      L*sliceEnergy (Q k) Delta ≤ E*((Q k).card : ℝ)^2 := by
  obtain ⟨k,hk,hkp,hratio⟩ := positive_weighted_ratio J
    (fun k => ((G k).card : ℝ)) (fun k => sliceEnergy (Q k) Delta) L E hL hE
    (fun _ _ => Nat.cast_nonneg _) (fun k _ => Finset.sum_nonneg (fun p _ => slice_potential_nonneg (Q k) Delta hDelta p))
    hpop henergy
  have hlow := original_slice_energy_lower (Q k) Delta hDelta hDelta1 (hbox k hk)
  have hc : ((G k).card : ℝ) ≤ ((Q k).card : ℝ)^2 := by
    have hh := (Finset.card_le_card (hG k hk)).trans_eq (Finset.card_product _ _)
    simpa only [pow_two,Nat.cast_mul] using (Nat.cast_le.mpr hh : ((G k).card : ℝ) ≤ ((Q k).card*(Q k).card : ℕ))
  refine ⟨k,hk,Finset.card_pos.mp (by exact_mod_cast hkp),hratio,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hlow hL.le
    nlinarith only [hh,hratio]
  · exact hratio.trans (mul_le_mul_of_nonneg_left hc hE.le)

/-- A cutoff chosen from the same graph/energy ratio keeps half the actual
ordered pairs and at least three quarters of the original slice points. -/
theorem original_regular_slice_cut_retention (Q : Finset Point3) (G : Finset Pair3)
    (Delta L E : ℝ) (hDelta : 0 < Delta) (hL : 0 < L) (hE : 0 < E)
    (hQ : Q.Nonempty) (hG : G⊆Q.product Q)
    (hratio : L*sliceEnergy Q Delta ≤ E*G.card) :
    (G.card : ℝ) ≤ 2*(retainedGraph G Q Delta (4*E/L)).card ∧
      3*(Q.card : ℝ) ≤ 4*(goodPoints Q Delta (4*E/L)).card := by
  let K := 4*E/L
  have hK : 0 < K := by dsimp [K]; positivity
  have hKL : K*L=4*E := by dsimp [K]; field_simp
  have hp : 0 < (Q.card : ℝ) := by exact_mod_cast hQ.card_pos
  have hcut := original_potential_cut_graph_loss Q G Delta K hDelta hK.le hG
  have hmass := original_potential_cut_mass_loss Q Delta K hDelta
  have hGcard : (G.card : ℝ) ≤ (Q.card : ℝ)^2 := by
    have hc := (Finset.card_le_card hG).trans_eq (Finset.card_product _ _)
    simpa only [pow_two,Nat.cast_mul] using (Nat.cast_le.mpr hc : (G.card : ℝ) ≤ (Q.card*Q.card : ℕ))
  constructor
  · have hh := mul_le_mul_of_nonneg_left hcut hL.le
    change (G.card : ℝ) ≤ 2*(retainedGraph G Q Delta K).card
    apply (mul_le_mul_iff_of_pos_left hE).mp
    have he1 : L*(K*G.card)=4*E*G.card := by
      calc
        _ = (K*L)*G.card := by ring
        _ = _ := by rw [hKL]
    have he2 : L*(K*(retainedGraph G Q Delta K).card+2*sliceEnergy Q Delta)=
        4*E*(retainedGraph G Q Delta K).card+2*(L*sliceEnergy Q Delta) := by
      calc
        _ = (K*L)*(retainedGraph G Q Delta K).card+2*(L*sliceEnergy Q Delta) := by ring
        _ = _ := by rw [hKL]
    rw [he1,he2] at hh
    nlinarith only [hh,hratio]
  · have hm := mul_le_mul_of_nonneg_right hmass hL.le
    have hh := mul_le_mul_of_nonneg_left hGcard hE.le
    have hpart := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun p => slicePotential Q Delta p ≤ K*Q.card) Q)
    have hpartR : ((Q\goodPoints Q Delta K).card : ℝ)+(goodPoints Q Delta K).card=Q.card := by exact_mod_cast hpart
    change 3*(Q.card : ℝ) ≤ 4*(goodPoints Q Delta K).card
    apply (mul_le_mul_iff_of_pos_right (mul_pos hE hp)).mp
    have he : (((Q\goodPoints Q Delta K).card : ℝ)*K*Q.card)*L=
        4*E*((Q\goodPoints Q Delta K).card : ℝ)*Q.card := by
      calc
        _ = (K*L)*((Q\goodPoints Q Delta K).card : ℝ)*Q.card := by ring
        _ = _ := by rw [hKL]
    rw [he] at hm
    have hb : ((Q\goodPoints Q Delta K).card : ℝ)=(Q.card : ℝ)-(goodPoints Q Delta K).card := by
      linarith only [hpartR]
    rw [hb] at hm
    nlinarith only [hm,hratio,hh]

/-- Actual aggregate incidence and energy bounds construct a retained
original slice core with dense original pairs and an all-radius one-Frostman
law. The chosen point set is not asserted to be Delta-separated. -/
theorem exists_original_energy_regular_slice_core {ι : Type*} (J : Finset ι)
    (Q : ι → Finset Point3) (G : ι → Finset Pair3) (Delta L E : ℝ)
    (hDelta : 0 < Delta) (hDelta1 : Delta ≤ 1) (hL : 0 < L) (hE : 0 < E)
    (hbox : ∀ k∈J,∀ p∈Q k,∀ j,|p j| ≤ 1)
    (hG : ∀ k∈J,G k⊆(Q k).product (Q k))
    (hpop : L ≤ ∑ k∈J,((G k).card : ℝ))
    (henergy : (∑ k∈J,sliceEnergy (Q k) Delta) ≤ E) :
    ∃ k∈J,∃ S : Finset Point3,S⊆Q k ∧
      3*((Q k).card : ℝ) ≤ 4*S.card ∧
      ((G k).card : ℝ) ≤ 2*((G k).filter (fun z => z.1∈S ∧ z.2∈S)).card ∧
      L*(S.card : ℝ)^2 ≤ 8*E*((G k).filter (fun z => z.1∈S ∧ z.2∈S)).card ∧
      ∀ p∈S,∀ r : ℝ,Delta ≤ r →
        ((S.filter (fun q => distance3 p q ≤ r)).card : ℝ) ≤ (8*E/L)*r*S.card := by
  obtain ⟨k,hk,hne,hratio,hdense,_henergy⟩ := exists_original_energy_regular_slice J Q G Delta L E
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
  refine ⟨k,hk,S,hSQ,hcut.2,hcut.1,?_,?_⟩
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

end OriginalThreeDimensionalEnergyRegularSlice
