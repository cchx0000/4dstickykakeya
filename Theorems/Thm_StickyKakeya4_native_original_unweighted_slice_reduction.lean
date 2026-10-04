import Theorems.Thm_StickyKakeya4_original_three_dimensional_marked_unweighted_slice
import Theorems.Thm_StickyKakeya4_original_three_dimensional_owner_scale_cutoff
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

noncomputable section
open scoped BigOperators
namespace NativeOriginalUnweightedSliceReduction
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalHeavySliceGraph OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalSliceMaximizer OriginalThreeDimensionalSliceParameterChoice
open NativeOriginalConcentratedPairGraph NativeOriginalNonconcentratedSliceGraph
open OriginalThreeDimensionalConcentratedBudget OriginalThreeDimensionalLiteralSlabCover
open NativeOriginalBoundedNonconcentratedRows OriginalThreeDimensionalOwnerScaleCutoff
open OriginalThreeDimensionalNativeReinforcementBudget OriginalThreeDimensionalMarkedPairCap
open OriginalThreeDimensionalMarkedUnweightedSlice OriginalThreeDimensionalGridUniformity
open OriginalPhysicalTubeScaleSelection NativeQuarterScaleParameters
open OriginalThreeDimensionalAveragedSliceEnergy OriginalThreeDimensionalRegularizedMarkedSlice

/-- One fixed choice of internal parameters and mesh cutoff turns the
ORIGINAL bounded, separated, grid-uniform two-Frostman source and its
actual rich original graph into the constructed unweighted planar slice.
The literal finite-slab hypothesis pays concentration deletion internally;
all selected-slice masses, energies, fiber weights and pair caps are derived. -/
theorem exists_native_original_unweighted_slice_threshold
    (zeta A epsilon eps2 etaUpper : ℝ)
    (hzeta : 0 < zeta) (hzeta1 : zeta < 1) (hA : 0 < A)
    (hepsilon : 0 < epsilon) (hepsmall : epsilon ≤ zeta/100)
    (heps2 : 0 < eps2) (hupper : 0 < etaUpper) :
    ∃ e2 : ℝ,0 < e2 ∧ 200*e2 ≤ epsilon ∧
    ∃ eta : ℝ,0 < eta ∧ eta ≤ etaUpper ∧ eta ≤ zeta/100 ∧
      eta ≤ zeta/1000 ∧ eta ≤ zeta*e2/10000 ∧
    ∃ delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/2 ∧
    ∀ delta : ℝ,0 < delta → delta ≤ delta0 →
    ∀ (P : Finset Point3) (G : Finset Pair3) (rho : ℝ) (n : ℕ),
      P.Nonempty → delta ≤ rho → rho ≤ 1 → rho=dyadicRadius n → G⊆P.product P →
      (∀ p∈P,∀ j,|p j| ≤ 1) →
      (∀ p∈P,∀ x∈P,p≠x → delta ≤ distance3 p x) →
      OriginalGridUniform P delta (delta^(-eta)) →
      (∀ z∈G,delta^(2*eta) ≤ distance3 z.1 z.2) →
      delta^eta*(P.card : ℝ)^2 ≤ G.card →
      (∀ p∈P,∀ R : ℝ,delta ≤ R → R ≤ 1 →
        ((P.filter (fun x => distance3 p x ≤ R)).card : ℝ) ≤ delta^(-eta)*R^2*P.card) →
      (∀ z∈G,delta^(-(zeta-zeta/100))*rho^(2-zeta/100)*P.card ≤ A*(physicalPairTube3 P rho z).card) →
      (∀ b : OriginalThreeDimensionalLiteralSlabCover.Frame3,∀ c : ℝ,∀ k : ℤ×ℤ,
        ((P.filter (fun x => x∈OriginalThreeDimensionalLiteralSlabCover.rectangle b c (delta^epsilon/2) k)).card : ℝ) ≤
          delta^eps2*P.card) →
      let r := delta^(2*eta)
      let Delta := 54*rho/r
      let e1 := sliceExponent delta Delta epsilon
      let D := 20/zeta
      let H := rho^(1+D*eta)*P.card
      let G2 := retainedPairs P G rho H
      let G4 := G2\concentratedPairGraph P G2 rho r (D*eta) e1 e2 (1/4)
      G4⊆G ∧ delta^(2*eta)*(P.card : ℝ)^2 ≤ G4.card ∧
      delta ≤ Delta/32 ∧ Delta/32 ≤ delta^(zeta/5) ∧
      1600*Delta/r ≤ delta^((51/50:ℝ)*epsilon) ∧
      OriginalMarkedUnweightedOutput P G4 delta rho r (D*eta) e1 e2
        (delta^((51/50:ℝ)*epsilon)) zeta (delta^(-eta)) n := by
  let D := 20/zeta
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨e2,he2,he2small,etaPre,hetaPre,hetaBound,hgainPre,hscalePre,hwidthPre,hmassPre⟩ :=
    exists_original_concentrated_parameter_budget zeta epsilon eps2 D 4 (min etaUpper (zeta/1000))
      hzeta hzeta1 hepsilon hepsmall heps2 hD (by norm_num) (lt_min hupper (by positivity))
  let eta := min etaPre (zeta*e2/10000)
  have heta : 0 < eta := lt_min hetaPre (by positivity)
  have hetaLe : eta ≤ etaPre := min_le_left _ _
  have hetaCap : eta ≤ zeta*e2/10000 := min_le_right _ _
  have hetaUpper := (hetaLe.trans hetaBound).trans (min_le_left _ _)
  have hetaFine : eta ≤ zeta/1000 := (hetaLe.trans hetaBound).trans (min_le_right _ _)
  have hetaSmall : eta ≤ zeta/100 := by linarith only [hetaFine,hzeta]
  have hgainEta := hetaLe.trans hgainPre
  have hscaleEta : 2*eta+(51/50:ℝ)*epsilon < (zeta-zeta/100)/(4*(1-zeta/100)) := by
    linarith only [hetaLe,hscalePre]
  have hwidthEta : (4+10+D)*eta+(1+200/epsilon)*e2 ≤ (149/10000:ℝ)*epsilon := by
    have hh := mul_le_mul_of_nonneg_left hetaLe (show 0 ≤ 4+10+D by linarith only [hD])
    linarith only [hh,hwidthPre]
  have hmassEta : (10*4+119+14*D)*eta+14*((1+200/epsilon)*e2) ≤ eps2 := by
    have hh := mul_le_mul_of_nonneg_left hetaLe (show 0 ≤ 10*4+119+14*D by linarith only [hD])
    linarith only [hh,hmassPre]
  obtain ⟨dT,hdT,hdT1,hT⟩ := exists_original_nonconcentrated_slice_graph_cutoff
    zeta (zeta/100) A epsilon eps2 D 4 eta e2 49
    (by linarith only [hzeta]) (by linarith only [hzeta1]) hA hepsilon heps2 hD (by norm_num)
    heta he2 he2small (by norm_num) hgainEta hscaleEta hwidthEta hmassEta
  obtain ⟨dR,hdR,_hdR1,hR⟩ := exists_original_bounded_nonconcentrated_rows_cutoff zeta A epsilon eta e2 D
    hzeta hzeta1 hA hepsilon hepsmall heta hetaSmall he2
  obtain ⟨dB,hdB,_hdB1,hB⟩ := exists_original_native_reinforcement_cutoff zeta eta 2 heta
    (by linarith only [hetaSmall,hzeta])
  obtain ⟨dO,hdO,_hdO1,hO⟩ := exists_original_owner_scale_cutoff zeta A epsilon 1600
    hzeta hzeta1 hA hepsilon hepsmall (by norm_num)
  obtain ⟨dM,hdM,_hdM1,hM⟩ := exists_small_power_cutoff heta (by norm_num : (0:ℝ) < 1/218)
  refine ⟨e2,he2,he2small,eta,heta,hetaUpper,hetaSmall,hetaFine,hetaCap,min dT (min dR (min dB (min dO dM))),
    lt_min hdT (lt_min hdR (lt_min hdB (lt_min hdO hdM))),(min_le_left _ _).trans hdT1,?_⟩
  intro delta hd hsmall P G rho n hP hquery hrho1 hmesh hGP hbox hseparated huniform hsep hdense hfrostman hgain hrect
  have hsmallT := hsmall.trans (min_le_left _ _)
  have hsmallR := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallB := hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmallO := hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hsmallM := hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hd1 : delta < 1 := (hsmallT.trans hdT1).trans_lt (by norm_num)
  have hpc : (0:ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hGpos : (0:ℝ) < G.card := (show 0 < delta^eta*(P.card : ℝ)^2 by positivity).trans_le hdense
  have hGne : G.Nonempty := Finset.card_pos.mp (by exact_mod_cast hGpos)
  obtain ⟨z0,hz0⟩ := hGne
  let r := delta^(2*eta)
  let Delta := 54*rho/r
  let q := delta^((51/50:ℝ)*epsilon)
  let e1 := sliceExponent delta Delta epsilon
  let H := rho^(1+D*eta)*P.card
  let G2 := retainedPairs P G rho H
  let G4 := G2\concentratedPairGraph P G2 rho r (D*eta) e1 e2 (1/4)
  have hrho : 0 < rho := hd.trans_le hquery
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := Real.rpow_le_one hd.le hd1.le (by positivity)
  have hDelta : 0 < Delta := by dsimp [Delta]; positivity
  have hDrId : Delta*r=54*rho := by dsimp [Delta]; field_simp
  have hq1 : q ≤ 1 := Real.rpow_le_one hd.le hd1.le (by positivity)
  obtain ⟨hdeltaFine,hmuUpper,howner⟩ := hO delta hd hsmallO eta heta.le hetaSmall
    P z0 rho hP hquery hrho1 hbox hfrostman (hgain z0 hz0)
  change delta ≤ Delta/32 at hdeltaFine
  change Delta/32 ≤ delta^(zeta/5) at hmuUpper
  change 1600*Delta/r ≤ q at howner
  have hgeo := (div_le_iff₀ hr).mp howner
  have hqR := mul_le_mul_of_nonneg_right hq1 hr.le
  have hDsmall : 32*Delta ≤ 1 := by nlinarith only [hgeo,hqR,hr1,hDelta]
  have hDr : Delta ≤ r := by nlinarith only [hgeo,hqR,hDelta]
  have h48 : 48*rho ≤ Delta := by
    have hh := mul_le_mul_of_nonneg_left hr1 hDelta.le
    rw [hDrId,mul_one] at hh
    linarith only [hh,hrho]
  have hDq : Delta ≤ q := by
    have hh := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ q by dsimp [q]; positivity)
    nlinarith only [hgeo,hh,hDelta]
  obtain ⟨_he1,_he1small,hidentity⟩ := original_slice_exponent_spec delta Delta epsilon hd hd1 hepsilon
    (by linarith only [hdeltaFine,hDelta]) hDq
  change Delta^e1=q at hidentity
  have hrhoDecay : rho ≤ delta^(zeta/5) := by
    have hh := mul_le_mul_of_nonneg_left hr1 hDelta.le
    rw [hDrId,mul_one] at hh
    linarith only [hh,hmuUpper,hrho]
  have hslab (normal : Point3) (c : ℝ) (hn : (∑ j,normal j^2)=1) :
      ((P.filter (fun x => |(∑ j,normal j*x j)-c| ≤ delta^epsilon/2)).card : ℝ) ≤
        49*delta^eps2*P.card := by
    have hh := original_unit_slab_from_literal_rectangles P (delta^epsilon/2)
      (delta^eps2*P.card) hbox hrect normal hn c
    simpa only [mul_assoc] using hh
  obtain ⟨hG4G,hretention,_hmarks⟩ := hT delta hd hsmallT P G rho n hP hquery hrho1 hmesh hGP
    hbox hsep hfrostman hgain hslab
  have hheavy : rho^(D*eta) ≤ delta^(4*eta) := by
    have hh := Real.rpow_le_rpow hrho.le hrhoDecay (show 0 ≤ D*eta by dsimp [D]; positivity)
    have he : (delta^(zeta/5))^(D*eta)=delta^(4*eta) := by
      rw [← Real.rpow_mul hd.le]
      congr 1
      dsimp [D]
      field_simp
      ring
    exact hh.trans_eq he
  have hfour : delta^(4*eta) ≤ delta^(2*eta) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1.le (by linarith only [heta])
  have htwo : delta^(2*eta)=delta^eta*delta^eta := by rw [← Real.rpow_add hd]; congr 1; ring
  have hscalar : delta^(2*eta)+216*rho^(D*eta)+delta^(4*eta) ≤ delta^eta := by
    have hx := mul_le_mul_of_nonneg_right (hM delta hd hsmallM) (Real.rpow_nonneg hd.le eta)
    rw [← htwo] at hx
    nlinarith only [hx,hheavy,hfour]
  have hG4dense : delta^(2*eta)*(P.card : ℝ)^2 ≤ G4.card := by
    have hh := mul_le_mul_of_nonneg_right hscalar (sq_nonneg (P.card : ℝ))
    change (G.card : ℝ) ≤ G4.card+(216*rho^(D*eta)+delta^(4*eta))*(P.card : ℝ)^2 at hretention
    nlinarith only [hh,hdense,hretention]
  have hG4pos : (0:ℝ) < G4.card := (show 0 < delta^(2*eta)*(P.card : ℝ)^2 by positivity).trans_le hG4dense
  have hG4ne : G4.Nonempty := Finset.card_pos.mp (by exact_mod_cast hG4pos)
  have hrows := hR delta hd hsmallR P G rho hP hquery hrho1 hGP hbox hsep hfrostman hgain
  have hK : 1 ≤ delta^(-eta) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hd hd1.le (show -eta ≤ 0 by linarith only [heta])
  have hterminal : 1 ≤ 2*OriginalThreeDimensionalPairEnergy.dyadicRadius Delta n := by
    have hid : (2:ℝ)^n*dyadicRadius n=1 := by
      unfold dyadicRadius
      rw [← mul_pow]
      norm_num
    have hrd : rho ≤ Delta := by linarith only [h48,hrho]
    have hh := mul_le_mul_of_nonneg_left hrd (show 0 ≤ (2:ℝ)^n by positivity)
    rw [hmesh,hid] at hh
    change 1 ≤ 2*((2:ℝ)^n*Delta)
    linarith only [hh]
  have hbudget := hB delta hd hsmallB P G4 rho n hP hrho (by simpa only [← hmesh] using hquery) hG4dense
  refine ⟨hG4G,hG4dense,hdeltaFine,hmuUpper,howner,?_⟩
  apply exists_original_marked_unweighted_slice P G4 delta rho r (D*eta) e1 e2 q zeta (delta^(-eta)) n
    hd hquery hrho1 hr hK hP hG4ne hbox hseparated huniform
    (fun z hz => hsep z (hG4G hz)) hfrostman ?_ ?_
    (by linarith only [hdeltaFine,hDelta]) h48 hDsmall hDr ?_ hterminal hbudget
  · intro z hz
    exact (hrows z hz).2.2.2.1
  · intro z hz d hdF
    obtain ⟨_hk,_hh,_hp,_hq,_hcap,_hm,hgainQ⟩ := (hrows z hz).2.2.2.2 d hdF
    exact hgainQ
  · change Delta^e1 ≤ 1
    rw [hidentity]
    exact hq1

end NativeOriginalUnweightedSliceReduction
