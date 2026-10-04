import Theorems.Thm_StickyKakeya4_native_original_unweighted_slice_reduction
import Theorems.Thm_StickyKakeya4_original_unweighted_slice_power_data
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

noncomputable section
namespace NativeOriginalPlanarPowerSlice
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalHeavySliceGraph OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalSliceMaximizer OriginalThreeDimensionalSliceParameterChoice
open NativeOriginalConcentratedPairGraph OriginalThreeDimensionalGridUniformity
open OriginalPhysicalTubeScaleSelection NativeQuarterScaleParameters
open OriginalThreeDimensionalAveragedSliceEnergy OriginalThreeDimensionalRegularizedMarkedSlice
open NativeOriginalUnweightedSliceReduction OriginalThreeDimensionalOwnerCoefficientBudget
open OriginalThreeDimensionalMarkedUnweightedSlice OriginalThreeDimensionalMarkedEndpointCarrier
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalMarkedPlanarCore
open NativeOriginalUnweightedSliceFrame OriginalUnweightedSlicePowerData

/-- Uniform over EVERY smaller external source exponent, one internal
choice before the mesh constructs the actual separated planar owner
source with explicit graph density, point profile, rich gain and pair cap.
The original finite slab assumption and all original point/pair labels
remain literal; no planar radial conclusion or A3 gain is assumed. -/
theorem exists_native_original_planar_power_threshold
    (zeta A epsilon eps2 etaUpper : ℝ)
    (hzeta : 0 < zeta) (hzeta1 : zeta < 1) (hA : 0 < A)
    (hepsilon : 0 < epsilon) (hepsmall : epsilon ≤ zeta/100)
    (heps2 : 0 < eps2) (hupper : 0 < etaUpper) :
    ∃ e2 : ℝ,0 < e2 ∧ 200*e2 ≤ epsilon ∧
    ∃ eta : ℝ,0 < eta ∧ eta ≤ etaUpper ∧ eta ≤ zeta/1000 ∧ eta ≤ zeta*e2/10000 ∧
    ∃ delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/2 ∧
    ∀ etaSource : ℝ,0 < etaSource → etaSource ≤ eta →
    ∀ delta : ℝ,0 < delta → delta ≤ delta0 →
    ∀ (P : Finset Point3) (G : Finset Pair3) (rho : ℝ) (n : ℕ),
      P.Nonempty → delta ≤ rho → rho ≤ 1 → rho=dyadicRadius n → G⊆P.product P →
      (∀ p∈P,∀ j,|p j| ≤ 1) →
      (∀ p∈P,∀ x∈P,p≠x → delta ≤ distance3 p x) →
      OriginalGridUniform P delta (delta^(-etaSource)) →
      (∀ z∈G,delta^(2*etaSource) ≤ distance3 z.1 z.2) →
      delta^etaSource*(P.card : ℝ)^2 ≤ G.card →
      (∀ p∈P,∀ R : ℝ,delta ≤ R → R ≤ 1 →
        ((P.filter (fun x => distance3 p x ≤ R)).card : ℝ) ≤ delta^(-etaSource)*R^2*P.card) →
      (∀ z∈G,delta^(-(zeta-zeta/100))*rho^(2-zeta/100)*P.card ≤ A*(physicalPairTube3 P rho z).card) →
      (∀ b : Frame3,∀ c : ℝ,∀ k : ℤ×ℤ,
        ((P.filter (fun x => x∈rectangle b c (delta^epsilon/2) k)).card : ℝ) ≤ delta^eps2*P.card) →
      let r := delta^(2*eta)
      let Delta := 54*rho/r
      let q := delta^((51/50:ℝ)*epsilon)
      delta ≤ Delta/32 ∧ Delta/32 ≤ delta^(zeta/5) ∧
      Delta/32 ≤ 50*Delta/r ∧ 50*Delta/r ≤ q/32 ∧
      ∃ b : Frame3,∃ C : Finset Point3,∃ hC : C.Nonempty,∃ G' : Finset Pair3,
        C⊆P ∧ G'⊆G ∧ OwnerPowerData G' b C hC delta Delta r eta zeta q e2 := by
  obtain ⟨e2,he2,he2small,eta,heta,hetaUpper,_hetaSmall,hetaFine,hetaCap,dS,hdS,hdS1,hS⟩ :=
    exists_native_original_unweighted_slice_threshold zeta A epsilon eps2 etaUpper
      hzeta hzeta1 hA hepsilon hepsmall heps2 hupper
  obtain ⟨dC,hdC,_hdC1,hC⟩ := exists_original_owner_coefficient_cutoff eta heta
  obtain ⟨dB,hdB,_hdB1,hB⟩ := exists_small_power_cutoff
    (show 0 < zeta*e2/10 by positivity) (show 0 < 1/(32:ℝ)^e2 by positivity)
  refine ⟨e2,he2,he2small,eta,heta,hetaUpper,hetaFine,hetaCap,min dS (min dC dB),
    lt_min hdS (lt_min hdC hdB),(min_le_left _ _).trans hdS1,?_⟩
  intro etaSource _hetaSource hetaLe delta hd hsmall P G rho n hP hquery hrho1 hmesh hGP
    hbox hseparated huniform hsep hdense hfrostman hgain hrect
  have hsmallS := hsmall.trans (min_le_left _ _)
  have hsmallC := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallB := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd1 : delta < 1 := (hsmallS.trans hdS1).trans_lt (by norm_num)
  obtain ⟨huniformI,hfrostmanI,hdenseI,hsepI⟩ := original_source_to_fixed_internal_eta
    P G delta etaSource eta hd hd1.le hetaLe huniform hfrostman hdense hsep
  let r := delta^(2*eta)
  let Delta := 54*rho/r
  let q := delta^((51/50:ℝ)*epsilon)
  let e1 := sliceExponent delta Delta epsilon
  let D := 20/zeta
  let H := rho^(1+D*eta)*P.card
  let G2 := retainedPairs P G rho H
  let G4 := G2\concentratedPairGraph P G2 rho r (D*eta) e1 e2 (1/4)
  let E := energyBudget P rho Delta (delta^(-eta)) n
  let L := (1/(8*rho))*(G4.card : ℝ)
  have hrho : 0 < rho := hd.trans_le hquery
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := Real.rpow_le_one hd.le hd1.le (by positivity)
  have hDelta : 0 < Delta := by dsimp [Delta]; positivity
  obtain ⟨hG4G,hG4dense,hfine,hdecay,howner,hconstruction⟩ := hS delta hd hsmallS P G rho n
    hP hquery hrho1 hmesh hGP hbox hseparated huniformI hsepI hdenseI hfrostmanI hgain hrect
  change G4⊆G at hG4G
  change delta^(2*eta)*(P.card : ℝ)^2 ≤ G4.card at hG4dense
  change delta ≤ Delta/32 at hfine
  change Delta/32 ≤ delta^(zeta/5) at hdecay
  change 1600*Delta/r ≤ q at howner
  have hpc : (0:ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hgc : (0:ℝ) < G4.card := (show 0 < delta^(2*eta)*(P.card : ℝ)^2 by positivity).trans_le hG4dense
  have hE : 0 < E := original_slice_energyBudget_pos P rho Delta (delta^(-eta)) n hP hrho hDelta (by positivity)
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨henergy,hfiber,hconst⟩ := hC delta hd hsmallC P G4 rho n hP hrho
    (by simpa only [← hmesh] using hquery) hG4dense
  have hcapConst : (32:ℝ)^e2*delta^(zeta*e2/10) ≤ 1 := by
    have hh := (le_div_iff₀ (show 0 < (32:ℝ)^e2 by positivity)).mp (hB delta hd hsmallB)
    nlinarith only [hh]
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hDq : Delta ≤ q := by
    have hh := (div_le_iff₀ hr).mp howner
    have hh' := mul_le_mul_of_nonneg_left hr1 hq
    nlinarith only [hh,hh',hDelta]
  have hidentity := (original_slice_exponent_spec delta Delta epsilon hd hd1 hepsilon
    (by linarith only [hfine,hDelta]) hDq).2.2
  change Delta^e1=q at hidentity
  obtain ⟨s,_hs,GP,G',b,hGPeq,hG'GP,_hGP,_hkeep,_hpairs,_hmarks,_hcoord,hdata⟩ := hconstruction
  let Q := enlargedSlice P rho s.1 s.2 Delta
  change OriginalUnweightedSliceOutput P Q (endpointCarrier GP) G' b Delta r (delta^(-eta))
    (4*E/L) (L/(32*E)) (delta^(-zeta/8)*Delta) (Delta^e1) (Delta^e2) at hdata
  rw [hidentity] at hdata
  obtain ⟨C,hCn,hCS,hpower⟩ := original_constructed_slice_power_data P Q (endpointCarrier GP) G' b
    delta Delta r eta zeta q e2 E L hd hd1.le hDelta rfl hzeta he2 hetaFine hetaCap hE hL
    (by linarith only [hdecay]) howner henergy hfiber hconst hcapConst hdata
  have hGPG4 : GP⊆G4 := by
    intro z hz
    rw [hGPeq] at hz
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
  have hS0P := original_endpoint_carrier_subset GP P (hGPG4.trans (hG4G.trans hGP))
  have hWlower : Delta/32 ≤ 50*Delta/r := by
    apply (le_div_iff₀ hr).mpr
    have hh := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ Delta/32 by positivity)
    nlinarith only [hh,hDelta]
  have hWupper : 50*Delta/r ≤ q/32 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 32)).mpr
    calc
      _ = 1600*Delta/r := by ring
      _ ≤ _ := howner
  exact ⟨hfine,hdecay,hWlower,hWupper,b,C,hCn,G',hCS.trans hS0P,hG'GP.trans (hGPG4.trans hG4G),hpower⟩

end NativeOriginalPlanarPowerSlice
