import Theorems.Thm_StickyKakeya4_native_original_unweighted_slice_frame
import Theorems.Thm_StickyKakeya4_original_three_dimensional_marked_pair_cap
import Theorems.Thm_StickyKakeya4_original_three_dimensional_marked_endpoint_carrier
import Theorems.Thm_StickyKakeya4_original_three_dimensional_physical_core_richness
import Theorems.Thm_StickyKakeya4_original_three_dimensional_native_reinforcement_budget
import Theorems.Thm_StickyKakeya4_original_three_dimensional_marked_planar_core
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000

noncomputable section
namespace OriginalThreeDimensionalMarkedUnweightedSlice
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalHeavySliceGraph OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalSliceMaximizer
open OriginalThreeDimensionalNonconcentratedRowMass NativeOriginalConcentratedPairGraph
open OriginalThreeDimensionalMarkedSliceIncidences OriginalThreeDimensionalMarkedPairCap
open OriginalThreeDimensionalMarkedSliceWitness OriginalThreeDimensionalMarkedEndpointCarrier
open OriginalThreeDimensionalPhysicalCoreRichness OriginalThreeDimensionalNativeReinforcementBudget
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalUnitNormals
open OriginalThreeDimensionalUnitSlabs OriginalThreeDimensionalRawOwnerNet
open OriginalThreeDimensionalMarkedPlanarCore OriginalThreeDimensionalSlicePotentialCut
open OriginalThreeDimensionalAveragedSliceEnergy OriginalThreeDimensionalRegularizedMarkedSlice
open OriginalThreeDimensionalExpandedSliceMultiplicity
open OriginalThreeDimensionalGridUniformity NativeOriginalUnweightedSliceFrame

/-- Original marked-slice witnesses and the fully constructed unweighted
planar output, retaining the exact original graph and source labels. -/
def OriginalMarkedUnweightedOutput (P : Finset Point3) (G : Finset Pair3)
    (delta rho r eta1 e1 e2 q zeta K : ℝ) (N : ℕ) : Prop :=
    let Delta := 54*rho/r
    let E := energyBudget P rho Delta K N
    let L := (1/(8*rho))*(G.card : ℝ)
    let F := boundedNonconcentratedRows P rho r eta1 e1 e2 q
    let H := rho^(1+eta1)*P.card
    ∃ s∈markedSlabs P G rho H F,∃ GP G' : Finset Pair3,∃ b : Frame3,
      let Q := enlargedSlice P rho s.1 s.2 Delta
      GP=(markedGraph P G rho H F s).filter
        (fun z => z.1∈goodPoints Q Delta (4*E/L) ∧ z.2∈goodPoints Q Delta (4*E/L)) ∧
      G'⊆GP ∧ GP.Nonempty ∧ (GP.card : ℝ) ≤ 4*G'.card ∧
      ((markedGraph P G rho H F s).card : ℝ) ≤ 8*G'.card ∧
      (∀ z∈G',z∈G ∧ s.1∈F z ∧ chosenHeavySlabCode P rho H z s.1=s.2) ∧
      (∀ x,frameCoordinate b 2 x=unitValue rho s.1 x) ∧
      OriginalUnweightedSliceOutput P Q (endpointCarrier GP) G' b Delta r K
        (4*E/L) (L/(32*E)) (delta^(-zeta/8)*Delta) (Delta^e1) (Delta^e2)

/-- Actual nonconcentrated marked rows produce a single original slice,
its potential-cut endpoint source, a reinforced original graph, and a
literal separated unweighted planar source. The cap comes directly from
the selected direction/code's concentration filter, with its Q mass. -/
theorem exists_original_marked_unweighted_slice
    (P : Finset Point3) (G : Finset Pair3)
    (delta rho r eta1 e1 e2 q zeta K : ℝ) (N : ℕ)
    (hd : 0 < delta) (hquery : delta ≤ rho) (hrho1 : rho ≤ 1) (hr : 0 < r)
    (hK : 1 ≤ K) (hP : P.Nonempty) (hG : G.Nonempty)
    (hbox : ∀ p∈P,∀ j,|p j| ≤ 1)
    (hseparated : ∀ p∈P,∀ v∈P,p≠v → delta ≤ distance3 p v)
    (huniform : OriginalGridUniform P delta K)
    (hsep : ∀ z∈G,r ≤ distance3 z.1 z.2)
    (hfrostman : ∀ p∈P,∀ R : ℝ,delta ≤ R → R ≤ 1 →
      ((P.filter (fun x => distance3 p x ≤ R)).card : ℝ) ≤ K*R^2*P.card)
    (hrows : ∀ z∈G,1 ≤ 8*rho*((boundedNonconcentratedRows P rho r eta1 e1 e2 q z).card : ℝ))
    (hrich : ∀ z∈G,∀ d∈boundedNonconcentratedRows P rho r eta1 e1 e2 q z,
      let Q := enlargedSlice P rho d (chosenHeavySlabCode P rho (rho^(1+eta1)*P.card) z d) (54*rho/r)
      delta^(-zeta/3)*rho*Q.card ≤ (physicalPairTube3 Q rho z).card)
    (hdeltaFine : delta ≤ (54*rho/r)/12)
    (hwidth : 48*rho ≤ 54*rho/r) (hsmall : 32*(54*rho/r) ≤ 1)
    (hDr : 54*rho/r ≤ r) (hcapwidth : (54*rho/r)^e1 ≤ 1)
    (hterminal : 1 ≤ 2*OriginalThreeDimensionalPairEnergy.dyadicRadius (54*rho/r) N)
    (hbudget : 960000*(energyBudget P rho (54*rho/r) K N/((1/(8*rho))*G.card))*
      ((54*rho/r)/rho)^2*delta^(5*zeta/12) ≤ 1) :
    OriginalMarkedUnweightedOutput P G delta rho r eta1 e1 e2 q zeta K N := by
  let Delta := 54*rho/r
  let E := energyBudget P rho Delta K N
  let L := (1/(8*rho))*(G.card : ℝ)
  let F := boundedNonconcentratedRows P rho r eta1 e1 e2 q
  let H := rho^(1+eta1)*P.card
  have hrho : 0 < rho := hd.trans_le hquery
  have hDelta : 0 < Delta := by dsimp [Delta]; positivity
  have hDelta1 : Delta ≤ 1 := by change 32*Delta ≤ 1 at hsmall; linarith only [hsmall,hDelta]
  have hL : 0 < L := by
    have hgc : (0:ℝ) < G.card := by exact_mod_cast hG.card_pos
    dsimp [L]
    positivity
  have hE : 0 < E := original_slice_energyBudget_pos P rho Delta K N hP hrho hDelta (zero_lt_one.trans_le hK)
  have hF : ∀ z∈G,F z⊆goodDirections P rho H z := by
    intro z _hz d hdF
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hdF).1).1
  have hrows' : ∀ z∈G,(1/(8*rho):ℝ) ≤ (F z).card := by
    intro z hz
    apply (div_le_iff₀ (show 0 < 8*rho by positivity)).mpr
    simpa only [mul_comm] using hrows z hz
  obtain ⟨s,hs,S,GP,hSident,hSelected,_hQEnergy,_hSQ,hGP,hGPeq,hmarks,
      _hpoints,hpairs,_hdense,_hprofile⟩ := exists_original_marked_slice_witness P G F
    delta rho Delta K H (1/(8*rho)) N hd hquery hrho1 (by linarith only [hwidth,hrho])
    hDelta1 hK hP hG (by positivity) hrows' hF hbox hterminal hfrostman
  let Q := enlargedSlice P rho s.1 s.2 Delta
  have hGPmark : GP⊆markedGraph P G rho H F s := by rw [hGPeq]; exact Finset.filter_subset _ _
  have hGPS : GP⊆S.product S := by
    intro z hz
    rw [hGPeq] at hz
    exact Finset.mem_product.mpr (Finset.mem_filter.mp hz).2
  have hGPgood : GP⊆(goodPoints Q Delta (4*E/L)).product (goodPoints Q Delta (4*E/L)) := by
    simpa only [hSident] using hGPS
  obtain ⟨hS0Q,hpotential⟩ := original_endpoint_full_potential Q GP Delta (4*E/L) hGPgood
  have hS0n : (endpointCarrier GP).Nonempty := by
    obtain ⟨z,hz⟩ := hGP
    exact ⟨z.1,(Finset.mem_product.mp (original_graph_on_endpoint_carrier GP hz)).1⟩
  have hQn : Q.Nonempty := hS0n.mono hS0Q
  have hQbox (x : Point3) (hx : x∈Q) : ∀ j,|x j| ≤ 1 := hbox x (Finset.mem_filter.mp hx).1
  obtain ⟨b,hb⟩ := exists_original_normal_frame (unitNormal rho s.1) (original_unit_normal_square rho s.1)
  have hcoord (x : Point3) : frameCoordinate b 2 x=unitValue rho s.1 x := by
    rw [hb,original_unit_normal_dot]
  let c := selectedOffset rho s
  have hframeQ : Q=frameSlice P b c Delta := by
    ext x
    simp only [Q,enlargedSlice,frameSlice,Finset.mem_filter,hcoord,c,selectedOffset]
  have hQslab (x : Point3) (hx : x∈Q) : |frameCoordinate b 2 x-c| ≤ Delta := by
    rw [hcoord]
    exact (Finset.mem_filter.mp hx).2
  have hraw0 := original_marked_endpoints_raw_slab P G GP F rho H s hF hGPmark
  have hraw (x : Point3) (hx : x∈endpointCarrier GP) : |frameCoordinate b 2 x-c| ≤ 3*rho := by
    rw [hcoord]
    exact original_slab_in_unit_slab P rho s.1 s.2 hrho.le x (hraw0 hx)
  have hrawGP (z : Pair3) (hz : z∈GP) :
      |frameCoordinate b 2 z.1-c| ≤ 3*rho ∧ |frameCoordinate b 2 z.2-c| ≤ 3*rho := by
    obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp (original_graph_on_endpoint_carrier GP hz)
    exact ⟨hraw z.1 hz1,hraw z.2 hz2⟩
  have hrichQ (z : Pair3) (hz : z∈GP) : delta^(-zeta/3)*rho*Q.card ≤ (physicalPairTube3 Q rho z).card := by
    obtain ⟨hzG,hdF,hcode⟩ := hmarks z hz
    have hh := hrich z hzG s.1 hdF
    dsimp only at hh
    change chosenHeavySlabCode P rho (rho^(1+eta1)*P.card) z s.1=s.2 at hcode
    rw [hcode] at hh
    exact hh
  have hreinforce := original_selected_ratio_reinforcement_budget Q Q
    (markedGraph P G rho H F s) GP delta rho Delta zeta E L hd hrho hDelta.le hE.le hL
    (Finset.Subset.refl _) hSelected hpairs hbudget
  have hm : 0 < delta^(-zeta/3)*rho*(Q.card : ℝ) := by
    have hqc : (0:ℝ) < Q.card := by exact_mod_cast hQn.card_pos
    positivity
  obtain ⟨G',hG'GP,hkeep,hpop⟩ := exists_original_physical_core_rich_graph Q (endpointCarrier GP) GP
    b c Delta rho r (delta^(-zeta/3)*rho*Q.card) (delta^(-zeta/8)*Delta*Q.card)
    hDelta hDelta1 hrho.le hr le_rfl hm hS0Q (original_graph_on_endpoint_carrier GP) hQbox hQslab
    hrawGP (fun z hz => hsep z (hmarks z hz).1) hrichQ hreinforce
  have hlower := original_slice_energy_lower Q Delta hDelta hDelta1 hQbox
  have hdensity : (L/(32*E))*(Q.card : ℝ)^2 ≤ G'.card := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 32*E by positivity)).mpr
    have h1 := mul_le_mul_of_nonneg_left hlower hL.le
    have h2 := mul_le_mul_of_nonneg_left hpairs hE.le
    have h3 := mul_le_mul_of_nonneg_left hkeep hE.le
    nlinarith only [h1,hSelected,h2,h3]
  have hG'S0 : G'⊆(endpointCarrier GP).product (endpointCarrier GP) :=
    hG'GP.trans (original_graph_on_endpoint_carrier GP)
  have hcap (z : Pair3) (hz : z∈G') :
      ((physicalPairTube3 Q (Delta^e1) z).card : ℝ) ≤ Delta^e2*Q.card :=
    original_marked_nonconcentrated_pair_cap P G rho r eta1 e1 e2 q s z (hGPmark (hG'GP hz))
  have houtput := exists_original_unweighted_slice_frame P Q (endpointCarrier GP) G' b c
    delta rho Delta r K (4*E/L) (L/(32*E)) (delta^(-zeta/8)*Delta) (Delta^e1) (Delta^e2)
    hframeQ hS0n (hS0Q.trans (Finset.filter_subset _ _)) hd hrho.le hDelta hr hdeltaFine hsmall hDr
    le_rfl hwidth (zero_le_one.trans hK) (by positivity) (by positivity) (by positivity)
    hcapwidth (by positivity) hseparated huniform hbox hraw hG'S0
    (fun z hz => hsep z (hmarks z (hG'GP hz)).1) hdensity hpotential hpop hcap
  refine ⟨s,hs,GP,G',b,?_,hG'GP,hGP,hkeep,?_,?_,hcoord,houtput⟩
  · simpa only [hSident] using hGPeq
  · linarith only [hpairs,hkeep]
  · intro z hz
    exact hmarks z (hG'GP hz)

end OriginalThreeDimensionalMarkedUnweightedSlice
