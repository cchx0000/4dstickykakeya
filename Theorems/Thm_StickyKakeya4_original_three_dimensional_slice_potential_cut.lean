import Theorems.Thm_StickyKakeya4_original_three_dimensional_slice_energy_basic
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalSlicePotentialCut
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalAveragedSliceEnergy

def goodPoints (Q : Finset Point3) (Delta K : ℝ) : Finset Point3 :=
  Q.filter (fun p => slicePotential Q Delta p ≤ K*Q.card)

def retainedGraph (G : Finset Pair3) (Q : Finset Point3) (Delta K : ℝ) : Finset Pair3 :=
  G.filter (fun z => z.1∈goodPoints Q Delta K ∧ z.2∈goodPoints Q Delta K)

/-- Delete large ORIGINAL potentials once. The loss is charged to the
same unnormalized finite I1 energy. -/
theorem original_potential_cut_mass_loss (Q : Finset Point3) (Delta K : ℝ)
    (hDelta : 0 < Delta) :
    ((Q\goodPoints Q Delta K).card : ℝ)*K*Q.card ≤ sliceEnergy Q Delta := by
  let B := Q\goodPoints Q Delta K
  have hb (p : Point3) (hp : p∈B) : K*Q.card ≤ slicePotential Q Delta p := by
    obtain ⟨hpQ,hpS⟩ := Finset.mem_sdiff.mp hp
    by_contra hn
    exact hpS (Finset.mem_filter.mpr ⟨hpQ,(lt_of_not_ge hn).le⟩)
  have hlo := Finset.sum_le_sum hb
  have hhi : (∑ p∈B,slicePotential Q Delta p) ≤ sliceEnergy Q Delta :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun p _hp _hpB => slice_potential_nonneg Q Delta hDelta p)
  have hh := hlo.trans hhi
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_assoc] using hh

/-- Every retained original point has the required all-radius one-Frostman
bound, still measured against original Q mass. -/
theorem original_potential_cut_ball_count (Q : Finset Point3) (Delta K : ℝ)
    (hDelta : 0 < Delta) (p : Point3) (hp : p∈goodPoints Q Delta K)
    (r : ℝ) (hr : Delta ≤ r) :
    (((goodPoints Q Delta K).filter (fun q => distance3 p q ≤ r)).card : ℝ) ≤ K*r*Q.card := by
  have hsub : (goodPoints Q Delta K).filter (fun q => distance3 p q ≤ r)⊆
      Q.filter (fun q => distance3 p q ≤ r) := by
    intro q hq
    obtain ⟨hqS,hqr⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hqS).1,hqr⟩
  have hc := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (original_ball_count_from_slice_potential Q Delta r p hDelta hr)
  have hh := mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hp).2 (hDelta.le.trans hr)
  nlinarith only [hc,hh]

/-- A single original point deletion changes only the actual incident
ordered pairs, with the exact two-endpoint count. -/
theorem original_restricted_graph_pair_loss (Q S : Finset Point3) (G : Finset Pair3)
    (_hSQ : S⊆Q) (hG : G⊆Q.product Q) :
    (G.card : ℝ) ≤ ((G.filter (fun z => z.1∈S ∧ z.2∈S)).card : ℝ)+
      2*((Q\S).card : ℝ)*Q.card := by
  let B := G.filter (fun z => ¬(z.1∈S ∧ z.2∈S))
  have hb : B⊆((Q\S).product Q)∪(Q.product (Q\S)) := by
    intro z hz
    obtain ⟨hzG,hzbad⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp (hG hzG)
    by_cases h1 : z.1∈S
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hz1,Finset.mem_sdiff.mpr
        ⟨hz2,fun h2 => hzbad ⟨h1,h2⟩⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨hz1,h1⟩,hz2⟩)
  have hc : B.card ≤ (Q\S).card*Q.card+Q.card*(Q\S).card :=
    (Finset.card_le_card hb).trans ((Finset.card_union_le _ _).trans_eq (by simp only [Finset.product_eq_sprod,Finset.card_product]))
  have hpart := Finset.card_filter_add_card_filter_not (s:=G) (fun z => z.1∈S ∧ z.2∈S)
  have hpartR : ((G.filter (fun z => z.1∈S ∧ z.2∈S)).card : ℝ)+B.card=G.card := by exact_mod_cast hpart
  have hcR : (B.card : ℝ) ≤ ((Q\S).card : ℝ)*Q.card+(Q.card : ℝ)*(Q\S).card := by exact_mod_cast hc
  nlinarith only [hpartR,hcR]

/-- The original graph loss is paid directly by the same slice energy;
no uniformized pair population or resampled source is introduced. -/
theorem original_potential_cut_graph_loss (Q : Finset Point3) (G : Finset Pair3)
    (Delta K : ℝ) (hDelta : 0 < Delta) (hK : 0 ≤ K) (hG : G⊆Q.product Q) :
    K*G.card ≤ K*(retainedGraph G Q Delta K).card+2*sliceEnergy Q Delta := by
  have hmass := original_potential_cut_mass_loss Q Delta K hDelta
  have hpair := original_restricted_graph_pair_loss Q (goodPoints Q Delta K) G (Finset.filter_subset _ _) hG
  have hm := mul_le_mul_of_nonneg_left hpair hK
  change K*G.card ≤ K*((G.filter (fun z => z.1∈goodPoints Q Delta K ∧ z.2∈goodPoints Q Delta K)).card : ℝ)+2*sliceEnergy Q Delta
  nlinarith only [hm,hmass]

end OriginalThreeDimensionalSlicePotentialCut
