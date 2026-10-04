import Theorems.Thm_StickyKakeya4_native_scheduled_quarter_geometry
import Theorems.Thm_StickyKakeya4_native_original_complete_budget
import Theorems.Thm_StickyKakeya4_native_uniform_abc_input
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3500000
noncomputable section
namespace NativeScheduledUniformABCInput
open Classical NativeScheduledQuarterGeometry NativeScheduledScaleSelection NativeOriginalCompleteBudget
open NativeOriginalGraphDensityCosts OriginalAngularSourcePopulation OriginalHeightLogBudget
open NativeQuarterScaleParameters FinitePlaneProjectionGrid FinitePlaneProjectionGraph
open NativePlanarABCInput FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening DyadicOriginalFiberSelection
/-- The native ABC envelope is instantiated by original source costs. The
 original cutoff precedes the scheduled scale, actual source sets, and all
 graph data. The original constructor's sets and graph remain unchanged. -/
theorem exists_scheduled_source_uniform_ABC
    {eta C0 tubeExp heightExp s u zeta : ℝ} (heta : 0 < eta) (hgap : eta < (1/8:ℝ))
    (hC : 1 ≤ C0) (htube : 0 ≤ tubeExp) (hheight : 0 ≤ heightExp)
    (hs : 0 < s) (hu : 0 ≤ u) (hzeta : 0 < zeta)
    (hloss : 10*budgetExponent eta tubeExp heightExp ≤ u/8) (n0 : ℕ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 < 1 ∧ ∀ delta : ℝ,
    0 < delta → delta ≤ delta0 →
    ∃ j n : ℕ, ∃ p : ℝ,
      let q := scheduledScale delta eta j
      let M := delta^(-eta)
      let rho := workingScale delta q C0
      let S0 := spatialNormalization C0 M
      delta ≤ q ∧ q ≤ 1 ∧ delta^(1/4:ℝ) ≤ q ∧ q ≤ M*delta^(1/4:ℝ) ∧
      0 < rho ∧ rho ≤ 1 ∧ delta ≤ rho^2 ∧ n0 ≤ n ∧ 0 < p ∧
      p/8=((2:ℝ)^n)⁻¹ ∧ rho/(2*S0) ≤ p ∧ p < rho/S0 ∧
      delta^(1/2:ℝ) ≤ p/8 ∧ p/8 ≤ delta^(1/4:ℝ) ∧
      ∀ Z : Finset ℝ, Z.Nonempty → Separated Z delta → (∀ z ∈ Z, |z| ≤ 1) →
      ∀ Phi : Finset ℝ, ∀ kappa : ℝ, Phi.Nonempty → Separated Phi q →
      ADBounds Phi q M kappa → (∀ phi ∈ Phi, |phi| ≤ 1) → zeta < kappa →
      let D := degree delta M kappa C0
      let U := ballCap delta q M kappa (2*C0)
      let alpha := delta^(witnessExponent tubeExp*eta)
      let beta := bcBeta alpha D U (Phi.card:ℝ) (levelCount Z:ℝ)
      let lambda := heightMass alpha D U (Phi.card:ℝ) (levelCount Z:ℝ)
        (delta^(heightExp*eta)) C0 M
      let KP := delta^(-(9*eta))
      let a := budgetExponent eta tubeExp heightExp
      let error := endpointError delta q C0 M
      ∃ resolution J : ℕ, mesh resolution ≤ p ∧ mesh resolution ≤ delta^s ∧
        2 ≤ 2^(J+1)*p ∧ kappa < 2 ∧
        ∀ data : Data (p/8) kappa
          (400*graphLoss J p 4 beta*graphMassLoss J p KP 4 beta/(beta*lambda))
          ((2:ℝ)^kappa*((2:ℝ)^kappa*M^2*(angularRatio q p)^kappa))
          (beta/graphMassLoss J p KP 4 beta) (delta^(4*s)/4)
          (graphMassLoss J p KP 4 beta/beta*delta^(u/4))
          ((graphMassLoss J p KP 4 beta/beta)*(4*error/p+8)^2),
        ∃ uniform : Data (p/8) (zeta/2) ((p/8)^(-64*a)) ((p/8)^(-64*a))
          ((p/8)^(64*a)) (2*(p/8)^(32*s)) ((p/8)^(u/4)) ((p/8)^(-64*a)),
          uniform.A=data.A ∧ uniform.B=data.B ∧ uniform.C=data.C ∧ uniform.G=data.G := by
  obtain ⟨dG,hdG,hdG1,hgeo⟩ := exists_scheduled_quarter_dyadic_cutoff heta hgap n0
  obtain ⟨dB,hdB,_,hbudget⟩ := exists_original_complete_budget heta hC htube hheight
  obtain ⟨dC,hdC,_,hconstant⟩ := exists_original_source_budget_cutoff heta hC
  obtain ⟨dW,hdW,_,hwidth⟩ := exists_small_power_cutoff (show 0 < 4*s by positivity)
    (by norm_num : (0:ℝ)<1/8)
  refine ⟨min (min dG dB) (min dC dW),lt_min (lt_min hdG hdB) (lt_min hdC hdW),
    lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) hdG1,?_⟩
  intro delta hd hd0
  have hdg : delta ≤ dG := hd0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hdb : delta ≤ dB := hd0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hdc : delta ≤ dC := hd0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdw : delta ≤ dW := hd0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd1 : delta ≤ 1 := (hdg.trans hdG1.le)
  have hCM := (hconstant delta hd hdc).1
  obtain ⟨j,n,p,hqδ,hq1,hqlo,hqhi,hr,hr1,hdr,hn,hp,heq,hhalf,hupper,hplo,hphi,hpack⟩ :=
    hgeo delta C0 hd hdg hC hCM
  let q := scheduledScale delta eta j
  have hhalf' : workingScale delta q C0/(2*spatialNormalization C0 (delta^(-eta))) ≤ p := by
    simpa only [workingScale,spatialNormalization,div_div,mul_comm] using hhalf
  refine ⟨j,n,p,hqδ,hq1,hqlo,hqhi,hr,hr1,hdr,hn,hp,heq,hhalf',hupper,hplo,hphi,?_⟩
  intro Z hZ hZsep hZbox Phi kappa hPhi hPhisep hAD hPhibox hbranch
  dsimp only
  have hk : 0 ≤ kappa := hzeta.le.trans hbranch.le
  have hk2 := OriginalAngularExponentRange.original_angular_exponent_lt_two Phi hPhi
    (hd.trans_le hqδ) hq1 (Real.rpow_pos_of_pos hd _) hPhisep hPhibox hAD hpack
  have hpbot : delta^(1/2:ℝ) ≤ p := by linarith only [hplo,hp]
  obtain ⟨resolution,J,hnp,hns,hJ,_,_,_,_,_,_,ha,hT,hKP0,hKP,hKB,
    hb,hbi,hl,hli,hM0,hM,hAR1,_,hAR,hE0,_,_,hE,hScales,_,_,_⟩ :=
    hbudget delta hd hdb Z hZ hZsep hZbox Phi q kappa hqδ hq1 hk hk2.le hPhi hAD hPhibox
      p hhalf' hupper.le hpbot s
  refine ⟨resolution,J,hnp,hns,hJ,hk2,?_⟩
  intro data
  apply NativeUniformABCInput.exists_uniform_ABC_input J hd hd1 ha.le hs.le hu hzeta
    hbranch hk2.le hplo hphi (hwidth delta hd hdw) hloss hT hKP0
    (by norm_num : (0:ℝ)<4) hb hl hKP hKB hScales hbi hli
    (by linarith only [hM0]) hM hAR1 hAR _ hE data
  simpa only [zero_mul] using (le_div_iff₀ hp).mp hE0
end NativeScheduledUniformABCInput
