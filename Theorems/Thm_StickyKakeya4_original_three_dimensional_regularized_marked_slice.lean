import Theorems.Thm_StickyKakeya4_original_three_dimensional_marked_slice_incidences
import Theorems.Thm_StickyKakeya4_original_three_dimensional_averaged_slice_energy
import Theorems.Thm_StickyKakeya4_original_three_dimensional_energy_regular_slice
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalRegularizedMarkedSlice
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalDirectionGrid OriginalThreeDimensionalHeavySliceGraph
open OriginalThreeDimensionalUnitSlabs OriginalThreeDimensionalSliceMaximizer
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalPairEnergy
open OriginalThreeDimensionalExpandedSliceMultiplicity NativeOriginalConcentratedPairGraph
open OriginalThreeDimensionalAveragedSliceEnergy OriginalThreeDimensionalSlicePotentialCut
open OriginalThreeDimensionalEnergyRegularSlice OriginalThreeDimensionalMarkedSliceIncidences

def energyBudget (P : Finset Point3) (rho Delta K : ℝ) (N : ℕ) : ℝ :=
  2880000*Delta^2*((N:ℝ)+1)*K*(P.card : ℝ)^2/rho^3

/-- Original marked heavy-slice incidences and the original two-Frostman
law construct a genuine regular slice core. Neither the total slice energy,
selected graph density, nor the core Frostman estimate is assumed. Pair
labels are retained exactly, and no Delta-separation of the core is claimed. -/
theorem exists_original_regularized_marked_slice
    (P : Finset Point3) (G : Finset Pair3) (F : Pair3 → Finset DirectionLabel)
    (delta rho Delta K H degree : ℝ) (N : ℕ)
    (hd : 0 < delta) (hdrho : delta ≤ rho) (hrho1 : rho ≤ 1)
    (hwidth : 3*rho ≤ Delta) (hDelta1 : Delta ≤ 1) (hK : 1 ≤ K)
    (hP : P.Nonempty) (hG : G.Nonempty) (hdegree : 0 < degree)
    (hrows : ∀ z∈G,degree ≤ (F z).card)
    (hF : ∀ z∈G,F z⊆goodDirections P rho H z)
    (hbox : ∀ p∈P,∀ j,|p j| ≤ 1)
    (hterminal : 1 ≤ 2*dyadicRadius Delta N)
    (hfrostman : ∀ p∈P,∀ r : ℝ,delta ≤ r → r ≤ 1 →
      ((P.filter (fun q => distance3 p q ≤ r)).card : ℝ) ≤ K*r^2*P.card) :
    ∃ s∈markedSlabs P G rho H F,∃ S : Finset Point3,∃ GP : Finset Pair3,
      S⊆enlargedSlice P rho s.1 s.2 Delta ∧ GP.Nonempty ∧
      GP=(markedGraph P G rho H F s).filter (fun z => z.1∈S ∧ z.2∈S) ∧
      (∀ z∈GP,z∈G ∧ s.1∈F z ∧ chosenHeavySlabCode P rho H z s.1=s.2) ∧
      3*((enlargedSlice P rho s.1 s.2 Delta).card : ℝ) ≤ 4*S.card ∧
      ((markedGraph P G rho H F s).card : ℝ) ≤ 2*GP.card ∧
      (degree*G.card)*(S.card : ℝ)^2 ≤ 8*energyBudget P rho Delta K N*GP.card ∧
      ∀ p∈S,∀ r : ℝ,Delta ≤ r →
        ((S.filter (fun q => distance3 p q ≤ r)).card : ℝ) ≤
          (8*energyBudget P rho Delta K N/(degree*G.card))*r*S.card := by
  have hrho := hd.trans_le hdrho
  have hDelta : rho ≤ Delta := by linarith only [hwidth,hrho]
  have hDp := hrho.trans_le hDelta
  let J := markedSlabs P G rho H F
  let Q : SliceLabel → Finset Point3 := fun s => enlargedSlice P rho s.1 s.2 Delta
  let GG := markedGraph P G rho H F
  let L : ℝ := degree*G.card
  let E : ℝ := energyBudget P rho Delta K N
  have hpc : 0 < (P.card : ℝ) := by exact_mod_cast hP.card_pos
  have hgc : 0 < (G.card : ℝ) := by exact_mod_cast hG.card_pos
  have hL : 0 < L := mul_pos hdegree hgc
  have hE : 0 < E := by
    dsimp [E,energyBudget]
    have hn := Nat.cast_nonneg (α:=ℝ) N
    have hKp := zero_lt_one.trans_le hK
    positivity
  have hgeom := original_marked_slice_geometry P G rho Delta H F hrho.le hwidth hF
  have hsum : L ≤ ∑ s∈J,((GG s).card : ℝ) := by
    rw [original_marked_slice_incidence_sum]
    calc
      _ = ∑ _z∈G,degree := by simp [L,mul_comm]
      _ ≤ _ := Finset.sum_le_sum hrows
  have he := original_averaged_slice_energy P J delta rho Delta K N hd hdrho hrho1 hDelta
    hK hterminal hbox hgeom.1 hfrostman
  have henergy : (∑ s∈J,sliceEnergy (Q s) Delta) ≤ E := by
    apply (le_div_iff₀ (pow_pos hrho 3)).mpr
    change (∑ s∈J,sliceEnergy (Q s) Delta)*rho^3 ≤ _
    simpa only [mul_comm] using he
  have hQbox (s : SliceLabel) (_hs : s∈J) (p : Point3) (hp : p∈Q s) : ∀ j,|p j| ≤ 1 :=
    hbox p (Finset.mem_filter.mp hp).1
  obtain ⟨s,hs,S,hSQ,hkeep,hpairs,hdense,hprofile⟩ := exists_original_energy_regular_slice_core
    J Q GG Delta L E hDp hDelta1 hL hE hQbox (fun s _hs => hgeom.2 s) hsum henergy
  let GP := (GG s).filter (fun z => z.1∈S ∧ z.2∈S)
  have hGG : (GG s).Nonempty := by
    obtain ⟨z,hz,hds⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨d,hd,heq⟩ := Finset.mem_image.mp hds
    have h1 : d=s.1 := congrArg Prod.fst heq
    have h2 : chosenHeavySlabCode P rho H z d=s.2 := congrArg Prod.snd heq
    exact ⟨z,Finset.mem_filter.mpr ⟨hz,by simpa only [← h1] using hd,by simpa only [← h1] using h2⟩⟩
  have hGP : GP.Nonempty := by
    apply Finset.card_pos.mp
    have hh : 0 < ((GG s).card : ℝ) := by exact_mod_cast hGG.card_pos
    have hp : 0 < (GP.card : ℝ) := by nlinarith only [hh,hpairs]
    exact_mod_cast hp
  refine ⟨s,hs,S,GP,hSQ,hGP,rfl,?_,hkeep,hpairs,hdense,hprofile⟩
  intro z hz
  exact Finset.mem_filter.mp (Finset.mem_filter.mp hz).1

end OriginalThreeDimensionalRegularizedMarkedSlice
