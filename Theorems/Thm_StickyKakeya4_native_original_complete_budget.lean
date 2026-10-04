import Theorems.Thm_StickyKakeya4_native_original_graph_density_costs
import Theorems.Thm_StickyKakeya4_original_height_log_budget
import Theorems.Thm_StickyKakeya4_native_abc_original_loss_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3500000
noncomputable section
namespace NativeOriginalCompleteBudget
open Classical NativeOriginalGraphDensityCosts OriginalAngularSourcePopulation
open OriginalHeightLogBudget NativeQuarterScaleParameters FinitePlaneProjectionGrid
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening DyadicOriginalFiberSelection
/-- The original source tube-count exponent fixes the W witness coefficient. -/
def witnessExponent (tubeExp : ℝ) : ℝ := 29+4*tubeExp
/-- All costs are expressed in this explicit original source exponent. -/
def budgetExponent (eta tubeExp heightExp : ℝ) : ℝ := (49+4*tubeExp+heightExp)*eta
def sourceBudget (delta eta tubeExp heightExp : ℝ) : ℝ := delta^(-budgetExponent eta tubeExp heightExp)
def workingScale (delta q C0 : ℝ) : ℝ := q+C0*delta
def angularRatio (q projectionRho : ℝ) : ℝ := q/(2*(projectionRho/8))
def endpointError (delta q C0 M : ℝ) : ℝ :=
  19*C0*M*workingScale delta q C0/spatialNormalization C0 M
lemma original_exponent_order {eta tubeExp heightExp : ℝ}
    (heta : 0 < eta) (ht : 0 ≤ tubeExp) (hh : 0 ≤ heightExp) :
    0 ≤ witnessExponent tubeExp ∧ 0 < budgetExponent eta tubeExp heightExp ∧
    9*eta ≤ budgetExponent eta tubeExp heightExp ∧
    (witnessExponent tubeExp+16)*eta ≤ budgetExponent eta tubeExp heightExp ∧
    (witnessExponent tubeExp+heightExp+20)*eta=budgetExponent eta tubeExp heightExp := by
  unfold witnessExponent budgetExponent
  have ht' := mul_nonneg ht heta.le
  have hh' := mul_nonneg hh heta.le
  refine ⟨by linarith,by nlinarith,by nlinarith,by nlinarith,?_⟩
  ring
lemma original_power_le_budget {delta eta tubeExp heightExp b : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hb : b ≤ budgetExponent eta tubeExp heightExp) :
    delta^(-b) ≤ sourceBudget delta eta tubeExp heightExp := by
  exact Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hb)
lemma original_loss_cube_le_budget {delta eta tubeExp heightExp : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 < eta)
    (ht : 0 ≤ tubeExp) (hh : 0 ≤ heightExp) :
    (delta^(-eta))^3 ≤ sourceBudget delta eta tubeExp heightExp := by
  have horder := (original_exponent_order heta ht hh).2.2.1
  have heq : (delta^(-eta))^3=delta^(-(3*eta)) := by
    rw [← Real.rpow_mul_natCast hd.le]
    congr 1
    norm_num
    ring
  rw [heq]
  exact original_power_le_budget hd hd1 (by linarith)
/-- The actual common projection mesh controls the source angular and
 endpoint-error ratios; the spatial normalization is exactly 4*C0*M. -/
theorem actual_shared_mesh_ratios {delta q C0 M projectionRho : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hC : 1 ≤ C0) (hCM : C0 ≤ M) (hM : 38 ≤ M)
    (hhalf : workingScale delta q C0/(2*spatialNormalization C0 M) ≤ projectionRho)
    (hupper : projectionRho ≤ workingScale delta q C0/spatialNormalization C0 M) :
    0 < projectionRho ∧ projectionRho ≤ 1 ∧
    1 ≤ angularRatio q projectionRho ∧ angularRatio q projectionRho ≤ M^3 ∧
    0 ≤ endpointError delta q C0 M/projectionRho ∧
    endpointError delta q C0 M/projectionRho ≤ 38*C0*M ∧
    endpointError delta q C0 M/projectionRho ≤ M^3 := by
  have hC0 : 0 < C0 := by linarith only [hC]
  have hM0 : 0 < M := by linarith only [hM]
  have hq : 0 < q := hd.trans_le hdq
  have hR : 0 < workingScale delta q C0 := by unfold workingScale; positivity
  have hS : 0 < spatialNormalization C0 M := by unfold spatialNormalization; positivity
  have hp : 0 < projectionRho := (div_pos hR (by positivity : 0 < 2*spatialNormalization C0 M)).trans_le hhalf
  have hRhi : workingScale delta q C0 ≤ (1+C0)*q := by
    have hh := mul_le_mul_of_nonneg_left hdq hC0.le
    unfold workingScale
    nlinarith only [hh]
  have hSM : 1+C0 ≤ spatialNormalization C0 M := by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ M by linarith) hC0.le
    unfold spatialNormalization
    nlinarith only [hh,hC]
  have hpq : projectionRho ≤ q := by
    calc
      _ ≤ workingScale delta q C0/spatialNormalization C0 M := hupper
      _ ≤ ((1+C0)*q)/spatialNormalization C0 M := div_le_div_of_nonneg_right hRhi hS.le
      _ ≤ q := (div_le_iff₀ hS).mpr (by nlinarith only [mul_le_mul_of_nonneg_right hSM hq.le])
  have hhalf' : workingScale delta q C0 ≤ projectionRho*(2*spatialNormalization C0 M) :=
    (div_le_iff₀ (by positivity : 0 < 2*spatialNormalization C0 M)).mp hhalf
  have hqR : q ≤ workingScale delta q C0 := by unfold workingScale; nlinarith only [mul_nonneg hC0.le hd.le]
  have hratioEq : angularRatio q projectionRho=4*q/projectionRho := by unfold angularRatio; ring
  have hratio1 : 1 ≤ angularRatio q projectionRho := by
    rw [hratioEq]
    exact (le_div_iff₀ hp).mpr (by linarith only [hpq,hq])
  have hratio : angularRatio q projectionRho ≤ 32*C0*M := by
    rw [hratioEq]
    apply (div_le_iff₀ hp).mpr
    unfold spatialNormalization at hhalf'
    nlinarith only [hqR,hhalf']
  have h32 : 32*C0*M ≤ M^3 := by
    have h1 := mul_le_mul_of_nonneg_right hCM (show 0 ≤ 32*M by positivity)
    have h2 := mul_le_mul_of_nonneg_right (show 32 ≤ M by linarith) (sq_nonneg M)
    nlinarith only [h1,h2]
  have herr : endpointError delta q C0 M/projectionRho ≤ 38*C0*M := by
    apply (div_le_iff₀ hp).mpr
    unfold endpointError
    apply (div_le_iff₀ hS).mpr
    calc
      _ ≤ (19*C0*M)*(projectionRho*(2*spatialNormalization C0 M)) :=
        mul_le_mul_of_nonneg_left hhalf' (by positivity)
      _ = _ := by ring
  have h38 : 38*C0*M ≤ M^3 := by
    have h1 := mul_le_mul_of_nonneg_right hCM (show 0 ≤ 38*M by positivity)
    have h2 := mul_le_mul_of_nonneg_right hM (sq_nonneg M)
    nlinarith only [h1,h2]
  exact ⟨hp,hpq.trans hq1,hratio1,hratio.trans h32,
    div_nonneg (div_nonneg (by positivity) hS.le) hp.le,herr,herr.trans h38⟩
/-- A single cutoff is chosen before the original height/angle sets and
 projection radius. All coefficients are fixed by the source count exponents;
 the actual finite projection resolution and scale menu are constructed here.
 No desired spatial, graph-density or ABC envelope is an input. -/
theorem exists_original_complete_budget {eta C0 tubeExp heightExp : ℝ}
    (heta : 0 < eta) (hC : 1 ≤ C0) (htube : 0 ≤ tubeExp) (hheightExp : 0 ≤ heightExp) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ ∀ delta : ℝ,
    0 < delta → delta ≤ delta0 →
    ∀ Z : Finset ℝ, Z.Nonempty → Separated Z delta → (∀ z ∈ Z, |z| ≤ 1) →
    ∀ Phi : Finset ℝ, ∀ q kappa : ℝ, delta ≤ q → q ≤ 1 →
    0 ≤ kappa → kappa ≤ 2 → Phi.Nonempty →
    ADBounds Phi q (delta^(-eta)) kappa → (∀ phi ∈ Phi, |phi| ≤ 1) →
    ∀ projectionRho : ℝ,
    workingScale delta q C0/(2*spatialNormalization C0 (delta^(-eta))) ≤ projectionRho →
    projectionRho ≤ workingScale delta q C0/spatialNormalization C0 (delta^(-eta)) →
    delta^(1/2 : ℝ) ≤ projectionRho → ∀ s : ℝ,
    let M := delta^(-eta)
    let S0 := spatialNormalization C0 M
    let Lheight := (levelCount Z : ℝ)
    let D := degree delta M kappa C0
    let U := ballCap delta q M kappa (2*C0)
    let alpha := delta^(witnessExponent tubeExp*eta)
    let lambdaFine := delta^(heightExp*eta)
    let betaBC := bcBeta alpha D U (Phi.card : ℝ) Lheight
    let lambdaB := heightMass alpha D U (Phi.card : ℝ) Lheight lambdaFine C0 M
    let KP := delta^(-(9*eta))
    let T := sourceBudget delta eta tubeExp heightExp
    let error := endpointError delta q C0 M
    ∃ n J : ℕ,
      mesh n ≤ projectionRho ∧ mesh n ≤ delta^s ∧ 2 ≤ 2^(J+1)*projectionRho ∧
      0 < projectionRho ∧ projectionRho ≤ 1 ∧
      C0 ≤ M ∧ 5101248 ≤ M ∧ Lheight ≤ M ∧
      ((dyadicScales J projectionRho).card : ℝ) ≤ M ∧
      0 < budgetExponent eta tubeExp heightExp ∧ 6168 ≤ T ∧
      0 < KP ∧ KP ≤ T ∧ 4 ≤ T ∧
      0 < betaBC ∧ betaBC⁻¹ ≤ T ∧ 0 < lambdaB ∧ lambdaB⁻¹ ≤ T ∧
      1 ≤ M ∧ M ≤ T ∧
      1 ≤ angularRatio q projectionRho ∧ angularRatio q projectionRho ≤ M^3 ∧
      angularRatio q projectionRho ≤ T ∧
      0 ≤ error/projectionRho ∧ error/projectionRho ≤ 38*C0*M ∧
      error/projectionRho ≤ M^3 ∧ error/projectionRho ≤ T ∧
      ((dyadicScales J projectionRho).card : ℝ) ≤ T ∧
      4*menuBeta alpha D U (Phi.card : ℝ)*U^2*(Phi.card : ℝ)^2=alpha*D^2 ∧
      betaBC=alpha*D^2/(72*Lheight*U^2*(Phi.card : ℝ)^2) ∧
      lambdaB=betaBC*lambdaFine/(3*S0*M) := by
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_original_source_budget_cutoff heta hC
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall Z hZ hZsep hZbox Phi q kappa hdq hq1 hk hk2 hPhi hAD hbox projectionRho hhalf hupper hbottom s
  dsimp only
  have hd1 : delta ≤ 1 := hsmall.trans hd01
  obtain ⟨hCM,hMbig,hheight,hprojection⟩ := hcut delta hd hsmall
  have hLM := hheight Z hZ hZsep hZbox
  have hL : 0 < (levelCount Z : ℝ) := by unfold levelCount; positivity
  obtain ⟨hp,hp1,hAR1,hAR3,hE0,hE38,hE3⟩ :=
    actual_shared_mesh_ratios hd hdq hq1 hC hCM (by linarith : 38 ≤ delta^(-eta)) hhalf hupper
  obtain ⟨n,J,hnR,hns,hJ,hJlog⟩ := exists_projection_resolution_and_scales hp hp1 (Real.rpow_pos_of_pos hd s)
  have hNM := hprojection projectionRho ((dyadicScales J projectionRho).card : ℝ) hbottom hJlog
  have horder := original_exponent_order heta htube hheightExp
  obtain ⟨hbeta,hlambda,hmenu,hbetaInv,hlambdaInv⟩ :=
    original_source_coefficients Phi hd hdq hq1 hMbig hC hCM hL hLM
      horder.1 hheightExp hk hk2 hPhi hAD hbox
  have hMT : delta^(-eta) ≤ sourceBudget delta eta tubeExp heightExp :=
    original_power_le_budget hd hd1 (by linarith only [horder.2.2.1,heta])
  have hTbig : 6168 ≤ sourceBudget delta eta tubeExp heightExp := by linarith only [hMbig,hMT]
  have hKP : delta^(-(9*eta)) ≤ sourceBudget delta eta tubeExp heightExp :=
    original_power_le_budget hd hd1 horder.2.2.1
  have hcube := original_loss_cube_le_budget hd hd1 heta htube hheightExp
  have hbetaT : (bcBeta (delta^(witnessExponent tubeExp*eta))
      (degree delta (delta^(-eta)) kappa C0) (ballCap delta q (delta^(-eta)) kappa (2*C0))
      (Phi.card : ℝ) (levelCount Z : ℝ))⁻¹ ≤ sourceBudget delta eta tubeExp heightExp := by
    refine hbetaInv.trans ?_
    simpa only [neg_mul] using original_power_le_budget hd hd1 horder.2.2.2.1
  have hexp : -(witnessExponent tubeExp+heightExp+20)*eta = -budgetExponent eta tubeExp heightExp := by
    unfold witnessExponent budgetExponent
    ring
  rw [hexp] at hlambdaInv
  refine ⟨n,J,hnR,hns,hJ,hp,hp1,hCM,hMbig,hLM,hNM,horder.2.1,hTbig,
    Real.rpow_pos_of_pos hd _,hKP,by linarith only [hTbig],hbeta,hbetaT,hlambda,hlambdaInv,
    by linarith only [hMbig],hMT,hAR1,hAR3,hAR3.trans hcube,hE0,hE38,hE3,hE3.trans hcube,
    hNM.trans hMT,hmenu,bcBeta_eq _ _ _ _ _,rfl⟩
end NativeOriginalCompleteBudget
