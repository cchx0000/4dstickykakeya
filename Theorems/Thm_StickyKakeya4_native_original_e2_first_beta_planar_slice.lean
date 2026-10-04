import Theorems.Thm_StickyKakeya4_original_finite_beta_planar_data
import Theorems.Thm_StickyKakeya4_native_original_e2_first_planar_power_slice
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6200000

noncomputable section
namespace NativeOriginalE2FirstBetaPlanarSlice
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalGridUniformity
open OriginalPhysicalTubeScaleSelection NativeQuarterScaleParameters
open OriginalThreeDimensionalLiteralSlabCover NativeOriginalE2FirstPlanarPowerSlice
open OriginalFiniteBetaGrid OriginalFiniteBetaPlanarData

/-- The finite beta menu and actual e2 are fixed FIRST. The caller may
then evaluate arbitrary positive planar allowances at every fixed bin
and this e2, and supply their finite minimum as the internal-eta ceiling.
Every cutoff is recomputed after the final internal eta is fixed.
After that ceiling, one internal eta and mesh cutoff work for every smaller
external source exponent. The actual source, physical mesh and query
are unchanged throughout, with strict graph and rich-population slack. -/
theorem exists_native_original_e2_first_beta_planar_threshold
    (zeta A epsilon eps2 : ℝ)
    (hzeta : 0 < zeta) (hzeta1 : zeta < 1) (hA : 0 < A)
    (hepsilon : 0 < epsilon) (hepsmall : epsilon ≤ zeta/100) (heps2 : 0 < eps2) :
    ∃ N : ℕ,
      (∀ i : ℕ,i ≤ N → 0 < binGain zeta i ∧ binGain zeta i ≤ 10/19 ∧
        0 < binCapExponent zeta epsilon i ∧ binCapExponent zeta epsilon i ≤ binGain zeta i/8 ∧
        0 ≤ 1-binGain zeta i/2 ∧ 1-binGain zeta i/2 < 1) ∧
      ∃ e2 : ℝ,0 < e2 ∧ 200*e2 ≤ epsilon ∧
      ∀ etaUpper : ℝ,0 < etaUpper →
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
        let mu := Delta/32
        let W := 50*Delta/r
        let q := delta^((51/50:ℝ)*epsilon)
        delta ≤ mu ∧ mu ≤ delta^(zeta/5) ∧ mu ≤ W ∧ W ≤ q/32 ∧
        ∃ i : ℕ,i ≤ N ∧ binLower zeta i ≤ meshBeta delta mu ∧ meshBeta delta mu ≤ binUpper zeta i ∧
        ∃ b : Frame3,∃ C : Finset Point3,∃ hC : C.Nonempty,∃ G' : Finset Pair3,
          C⊆P ∧ G'⊆G ∧ OwnerBinData G' b C hC mu W (200*eta/zeta) zeta epsilon (zeta*e2/20) i := by
  obtain ⟨N,hgrid⟩ := exists_original_finite_beta_grid zeta hzeta hzeta1
  refine ⟨N,?_,?_⟩
  · intro i _hi
    obtain ⟨_hlo,_hloLower,hgain,hgainUpper,hcap,hcapGain⟩ := original_beta_bin_parameter_bounds
      zeta epsilon i hzeta hepsilon hepsmall
    exact ⟨hgain,hgainUpper,hcap,hcapGain,by linarith only [hgainUpper],by linarith only [hgain]⟩
  · obtain ⟨e2,he2,he2small,hPower⟩ := exists_native_original_e2_first_planar_power_threshold
      zeta A epsilon eps2 hzeta hzeta1 hA hepsilon hepsmall heps2
    refine ⟨e2,he2,he2small,?_⟩
    intro etaUpper hupper
    obtain ⟨eta,heta,hetaUpper,hetaFine,hetaCap,dS,hdS,hdS1,hS⟩ := hPower etaUpper hupper
    obtain ⟨dR,hdR,_hdR1,hR⟩ := exists_small_power_cutoff
      (show 0 < (51/1000:ℝ)*epsilon by positivity) (by norm_num : (0:ℝ) < 1/16)
    refine ⟨eta,heta,hetaUpper,hetaFine,hetaCap,min dS dR,
      lt_min hdS hdR,(min_le_left _ _).trans hdS1,?_⟩
    intro etaSource hetaSource hetaLe delta hd hsmall P G rho n hP hquery hrho1 hmesh hGP
      hbox hseparated huniform hsep hdense hfrostman hgain hrect
    have hsmallS := hsmall.trans (min_le_left _ _)
    have hsmallR := hsmall.trans (min_le_right _ _)
    have hd1 : delta < 1 := (hsmallS.trans hdS1).trans_lt (by norm_num)
    let r := delta^(2*eta)
    let Delta := 54*rho/r
    have hrho : 0 < rho := hd.trans_le hquery
    have hr : 0 < r := by dsimp [r]; positivity
    have hDelta : 0 < Delta := by dsimp [Delta]; positivity
    obtain ⟨hfine,hdecay,hWlo,hWhi,b,C,hC,G',hCP,hG'G,hdata⟩ :=
      hS etaSource hetaSource hetaLe delta hd hsmallS P G rho n hP hquery hrho1 hmesh hGP
        hbox hseparated huniform hsep hdense hfrostman hgain hrect
    change delta ≤ Delta/32 at hfine
    change Delta/32 ≤ delta^(zeta/5) at hdecay
    obtain ⟨_hmu,_hmu1,hbetaLo,hbetaHi,_hmuIdentity⟩ := original_mesh_beta_spec delta (Delta/32) zeta
      hd hd1 hzeta hfine hdecay
    obtain ⟨i,hi,hbinLo,hbinHi,_hbin1⟩ := hgrid (meshBeta delta (Delta/32)) hbetaLo hbetaHi
    have hbinData := original_owner_power_to_beta_bin G' b C hC delta Delta r eta zeta epsilon e2 i
      hd hd1 hDelta hr heta hzeta hepsilon he2 hfine hdecay hbinLo hbinHi
      (hR delta hd hsmallR) hdata
    exact ⟨hfine,hdecay,hWlo,hWhi,i,hi,hbinLo,hbinHi,b,C,hC,G',hCP,hG'G,hbinData⟩

end NativeOriginalE2FirstBetaPlanarSlice
