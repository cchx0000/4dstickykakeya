import Theorems.Thm_StickyKakeya4_original_three_dimensional_chosen_slice_tube
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeOriginalBoundedNonconcentratedRows
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalHeavySliceGraph
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalSliceMaximizer
open OriginalThreeDimensionalNonconcentratedRowMass OriginalThreeDimensionalChosenSliceTube
open OriginalThreeDimensionalSliceParameterChoice OriginalThreeDimensionalNativeSliceScale
open NativeOriginalConcentratedPairGraph NativeQuarterScaleParameters

/-- At one source-independent cutoff, EVERY surviving original pair keeps
many actual chosen slab labels after a literal global mass cutoff. The
original rich tube is wholly inside its chosen enlarged slice, and gains
relative to the original slice mass. No regularized point core is substituted. -/
theorem exists_original_bounded_nonconcentrated_rows_cutoff
    (zeta A epsilon eta e2 D : ℝ)
    (hzeta : 0 < zeta) (hzeta1 : zeta < 1) (hA : 0 < A)
    (hepsilon : 0 < epsilon) (hepsmall : epsilon ≤ zeta/100)
    (heta : 0 < eta) (hetasmall : eta ≤ zeta/100) (he2 : 0 < e2) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1/2 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
      ∀ (P : Finset Point3) (G : Finset Pair3) (rho : ℝ),
        P.Nonempty → delta ≤ rho → rho ≤ 1 → G⊆P.product P →
        (∀ p∈P, ∀ j, |p j| ≤ 1) →
        (∀ z∈G, delta^(2*eta) ≤ distance3 z.1 z.2) →
        (∀ p∈P, ∀ R : ℝ, delta ≤ R → R ≤ 1 →
          ((P.filter (fun q => distance3 p q ≤ R)).card : ℝ) ≤ delta^(-eta)*R^2*P.card) →
        (∀ z∈G, delta^(-(zeta-zeta/100))*rho^(2-zeta/100)*P.card ≤
          A*(physicalPairTube3 P rho z).card) →
        let r := delta^(2*eta)
        let Delta := 54*rho/r
        let q := delta^((51/50:ℝ)*epsilon)
        let e1 := sliceExponent delta Delta epsilon
        let H := rho^(1+D*eta)*P.card
        let G2 := retainedPairs P G rho H
        let G4 := G2\concentratedPairGraph P G2 rho r (D*eta) e1 e2 (1/4)
        ∀ z∈G4,
          let k := chosenHeavySlabCode P rho H z
          let U := goodDirections P rho H z\concentratedDirections P rho r (D*eta) e1 e2 z
          let F := smallSliceDirections P U k rho Delta r q
          delta ≤ Delta ∧ Delta ≤ 1 ∧
          F⊆goodDirections P rho H z ∧ 1 ≤ 8*rho*(F.card : ℝ) ∧
          ∀ d∈F,
            k d∈P.image (slabCode rho d) ∧
            H ≤ ((slabPoints P rho d (k d)).card : ℝ) ∧
            z.1∈slabPoints P rho d (k d) ∧ z.2∈slabPoints P rho d (k d) ∧
            ((physicalPairTube3 (enlargedSlice P rho d (k d) Delta) q z).card : ℝ) ≤
              Delta^e2*(enlargedSlice P rho d (k d) Delta).card ∧
            ((enlargedSlice P rho d (k d) Delta).card : ℝ) ≤ delta^(-zeta/10)*rho*P.card ∧
            delta^(-zeta/3)*rho*(enlargedSlice P rho d (k d) Delta).card ≤
              (physicalPairTube3 (enlargedSlice P rho d (k d) Delta) rho z).card := by
  let a := (51/50:ℝ)*epsilon
  have ha : 0 < a := by dsimp [a]; positivity
  have hgamma : zeta/100 < 1 := by linarith only [hzeta1]
  have hgap : zeta/100 < zeta := by linarith only [hzeta]
  have hg : eta ≤ (zeta-zeta/100)/2 := by linarith only [hetasmall,hzeta]
  have hmargin : 2*eta+a < (zeta-zeta/100)/(4*(1-zeta/100)) := by
    apply (lt_div_iff₀ (show 0 < 4*(1-zeta/100) by linarith only [hgamma])).mpr
    have hcoef : 0 < 2*eta+a := by positivity
    have hle : (2*eta+a)*(4*(1-zeta/100)) ≤ (2*eta+a)*4 :=
      mul_le_mul_of_nonneg_left (by linarith only [hzeta]) hcoef.le
    dsimp [a] at hle ⊢
    linarith only [hle,hetasmall,hepsmall,hzeta]
  obtain ⟨dS,hdS,hdS1,hS⟩ := exists_original_slice_parameter_cutoff zeta (zeta/100) A
    epsilon eta hgap hgamma hA hepsilon heta hg hmargin
  obtain ⟨dM,hdM,_hdM1,hM⟩ := exists_original_slice_mass_power_cutoff zeta epsilon eta
    hzeta hepsilon hepsmall heta hetasmall
  obtain ⟨dT,hdT,_hdT1,hT⟩ := exists_small_power_cutoff
    (show 0 < a*e2 by positivity) (by norm_num : (0:ℝ) < 1/2)
  obtain ⟨dA,hdA,_hdA1,hAc⟩ := exists_small_power_cutoff
    (show 0 < zeta/2 by positivity) (one_div_pos.mpr hA)
  refine ⟨min dS (min dM (min dT dA)),
    lt_min hdS (lt_min hdM (lt_min hdT hdA)),(min_le_left _ _).trans hdS1,?_⟩
  intro delta hd hsmall P G rho hP hquery hrho1 hGP hbox hsep hfrostman hgain
  have hsmallS := hsmall.trans (min_le_left _ _)
  have hsmallM := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallT := hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmallA := hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hd1 : delta ≤ 1 := (hsmallS.trans hdS1).trans (by norm_num)
  let r := delta^(2*eta)
  let Delta := 54*rho/r
  let q := delta^a
  let e1 := sliceExponent delta Delta epsilon
  let H := rho^(1+D*eta)*P.card
  dsimp only
  intro z hz
  obtain ⟨hz2,hzC⟩ := Finset.mem_sdiff.mp hz
  have hzG : z∈G := (Finset.mem_filter.mp hz2).1
  have hrho : 0 < rho := hd.trans_le hquery
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := Real.rpow_le_one hd.le hd1 (by positivity : 0 ≤ 2*eta)
  have hDr : Delta*r=54*rho := by dsimp [Delta]; field_simp
  have hDelta : 0 < Delta := by dsimp [Delta]; positivity
  have hwidth : 3*rho ≤ Delta := by
    have hh := mul_le_mul_of_nonneg_left hr1 hDelta.le
    rw [hDr,mul_one] at hh
    linarith only [hh,hrho]
  obtain ⟨hqueryD,hDq,_he1,_he11,hqeq⟩ := hS delta hd hsmallS P z rho hP hquery hrho1
    hbox hfrostman (hgain z hzG)
  change Delta^e1=q at hqeq
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := Real.rpow_le_one hd.le hd1 ha.le
  have hD1 : Delta ≤ 1 := hDq.trans hq1
  have htheta : Delta^e2 ≤ 1/2 := by
    have hp := Real.rpow_le_rpow hDelta.le hDq he2.le
    have he : q^e2=delta^(a*e2) := by dsimp [q]; rw [← Real.rpow_mul hd.le]
    exact hp.trans ((le_of_eq he).trans (hT delta hd hsmallT))
  let k := chosenHeavySlabCode P rho H z
  let U := goodDirections P rho H z\concentratedDirections P rho r (D*eta) e1 e2 z
  obtain ⟨hdegree,hrows⟩ := retained_unconcentrated_direction_population P G rho r (D*eta) e1 e2 z hz2 hzC
  have hUg : U⊆goodDirections P rho H z := Finset.sdiff_subset
  have hband : U⊆pairBand rho z.1 z.2 := hUg.trans (Finset.filter_subset _ _)
  have hslabs (d : DirectionLabel) (hdU : d∈U) :
      z.1∈slabPoints P rho d (k d) ∧ z.2∈slabPoints P rho d (k d) :=
    ⟨(hrows d hdU).2.2.1,(hrows d hdU).2.2.2.1⟩
  have hnoncon (d : DirectionLabel) (hdU : d∈U) :
      ((physicalPairTube3 (enlargedSlice P rho d (k d) Delta) q z).card : ℝ) ≤
        Delta^e2*(enlargedSlice P rho d (k d) Delta).card := by
    have hn : ((physicalPairTube3 (enlargedSlice P rho d (k d) Delta) (Delta^e1) z).card : ℝ) ≤
        Delta^e2*(enlargedSlice P rho d (k d) Delta).card := (hrows d hdU).2.2.2.2
    rw [hqeq] at hn
    exact hn
  obtain ⟨hFU,hFdegree,hFmass⟩ := original_small_slice_row_population P z U k rho Delta r q (Delta^e2)
    hrho hrho1 hr hq hq1 hwidth hDr.ge htheta (hGP hzG) hbox (hsep z hzG) hband hslabs hnoncon hdegree
  have hmass := hM delta hd hsmallM rho hrho.le P
  have hcut : A*delta^(zeta/2) ≤ 1 := by
    have hh := (le_div_iff₀ hA).mp (hAc delta hd hsmallA)
    nlinarith only [hh]
  refine ⟨hqueryD,hD1,hFU.trans hUg,hFdegree,?_⟩
  intro d hdF
  have hdU : d∈U := hFU hdF
  obtain ⟨hk,hheavy,hp,hqP,_hn⟩ := hrows d hdU
  have hmassd := (hFmass d hdF).trans hmass
  refine ⟨hk,hheavy,hp,hqP,hnoncon d hdU,hmassd,?_⟩
  exact original_chosen_slice_relative_tube_gain P z delta rho r zeta A d (k d)
    hd hd1 hrho hrho1 hr hr1 hzeta hA hbox (hsep z hzG) ⟨hp,hqP⟩ (hgain z hzG) hcut hmassd

end NativeOriginalBoundedNonconcentratedRows
