import Theorems.Thm_StickyKakeya4_original_selected_angular_incidences
import Theorems.Thm_StickyKakeya4_native_scheduled_height_population
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3500000
noncomputable section
namespace NativeOriginalGraphDensityCosts
open Classical OriginalAngularSourcePopulation FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open NativeScheduledHeightPopulation DyadicOriginalFiberSelection OriginalCoarseHeightCurve
/-- The source W count fixes the menu density by equality. -/
def menuBeta (alpha D U N : ℝ) : ℝ := alpha*D^2/(4*U^2*N^2)
/-- Nine neighboring grain windows are the entire window loss. -/
def windowBeta (alpha D U N : ℝ) : ℝ := menuBeta alpha D U N/9
/-- Original section selection costs nothing; graph-aware height binning
 costs exactly twice its actual number of levels. -/
def bcBeta (alpha D U N L : ℝ) : ℝ := windowBeta alpha D U N/(2*L)
def spatialNormalization (C0 M : ℝ) : ℝ := 4*C0*M
/-- The scheduled overshoot and nearby dyadic lowering are already charged
 by the factor two in bcBeta. -/
def heightMass (alpha D U N L lambdaFine C0 M : ℝ) : ℝ :=
  bcBeta alpha D U N L*lambdaFine/(3*spatialNormalization C0 M*M)
lemma menuBeta_pos {alpha D U N : ℝ} (ha : 0 < alpha) (hD : 0 < D)
    (hU : 0 < U) (hN : 0 < N) : 0 < menuBeta alpha D U N := by unfold menuBeta; positivity
lemma windowBeta_pos {alpha D U N : ℝ} (ha : 0 < alpha) (hD : 0 < D)
    (hU : 0 < U) (hN : 0 < N) : 0 < windowBeta alpha D U N := by
  unfold windowBeta
  exact div_pos (menuBeta_pos ha hD hU hN) (by norm_num)
lemma bcBeta_pos {alpha D U N L : ℝ} (ha : 0 < alpha) (hD : 0 < D)
    (hU : 0 < U) (hN : 0 < N) (hL : 0 < L) : 0 < bcBeta alpha D U N L := by
  unfold bcBeta
  exact div_pos (windowBeta_pos ha hD hU hN) (by positivity)
lemma heightMass_pos {alpha D U N L lambdaFine C0 M : ℝ}
    (ha : 0 < alpha) (hD : 0 < D) (hU : 0 < U) (hN : 0 < N) (hL : 0 < L)
    (hl : 0 < lambdaFine) (hC : 0 < C0) (hM : 0 < M) :
    0 < heightMass alpha D U N L lambdaFine C0 M := by
  unfold heightMass spatialNormalization
  exact div_pos (mul_pos (bcBeta_pos ha hD hU hN hL) hl) (by positivity)
/-- The exact original menu scale condition, with no density parameter left
 to choose or assume. -/
theorem menu_scale_eq (alpha D : ℝ) {U N : ℝ} (hU : U ≠ 0) (hN : N ≠ 0) :
    4*menuBeta alpha D U N*U^2*N^2=alpha*D^2 := by unfold menuBeta; field_simp
lemma bcBeta_eq (alpha D U N L : ℝ) :
    bcBeta alpha D U N L=alpha*D^2/(72*L*U^2*N^2) := by
  unfold bcBeta windowBeta menuBeta
  ring
lemma heightMass_nearby_eq (alpha D U N L lambdaFine C0 M : ℝ) :
    heightMass alpha D U N L lambdaFine C0 M=
      windowBeta alpha D U N*lambdaFine/(6*L*spatialNormalization C0 M*M) := by
  unfold heightMass bcBeta
  ring
lemma bcBeta_inverse_eq {alpha D U N L : ℝ} (ha : alpha ≠ 0) (hD : D ≠ 0)
    (hU : U ≠ 0) (hN : N ≠ 0) (hL : L ≠ 0) :
    (bcBeta alpha D U N L)⁻¹=72*L*(U*N/D)^2/alpha := by
  rw [bcBeta_eq]
  field_simp
lemma heightMass_inverse_eq {alpha D U N L lambdaFine C0 M : ℝ}
    (ha : 0 < alpha) (hD : 0 < D) (hU : 0 < U) (hN : 0 < N) (hL : 0 < L)
    (hl : 0 < lambdaFine) (hC : 0 < C0) (hM : 0 < M) :
    (heightMass alpha D U N L lambdaFine C0 M)⁻¹=
      12*C0*M^2*(bcBeta alpha D U N L)⁻¹/lambdaFine := by
  have hb := bcBeta_pos ha hD hU hN hL
  unfold heightMass spatialNormalization
  field_simp
  norm_num
/-- Instantiate both angular AD constants by the literal original loss M.
 The common Phi population is supplied by its boxed coarse AD law. -/
theorem original_reference_ratio_six (Phi : Finset ℝ) {delta q M kappa C0 : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hM : 1 ≤ M) (hC0 : 0 ≤ C0) (hCM : C0 ≤ M)
    (hk : 0 ≤ kappa) (hk2 : kappa ≤ 2)
    (hAD : ADBounds Phi q M kappa) (hbox : ∀ phi ∈ Phi, |phi| ≤ 1) :
    ballCap delta q M kappa (2*C0)*(Phi.card : ℝ)/degree delta M kappa C0 ≤ 4096*M^6 := by
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hh := original_reference_population_ratio Phi hd hdq hq1 hM0 hM0.le hC0 hk hk2 hAD hbox
  have hbase : 1+C0 ≤ 2*M := by linarith only [hM,hCM]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+C0) hbase 3
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 512*M^2*M by positivity)
  calc
    _ ≤ 512*M^2*M*(1+C0)^3 := hh
    _ ≤ 512*M^2*M*(2*M)^3 := hm
    _ = _ := by ring
/-- The numerical coefficient is absorbed into one original loss power. -/
theorem original_reference_ratio_seven (Phi : Finset ℝ) {delta q M kappa C0 : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hM : 4096 ≤ M) (hC0 : 0 ≤ C0) (hCM : C0 ≤ M)
    (hk : 0 ≤ kappa) (hk2 : kappa ≤ 2)
    (hAD : ADBounds Phi q M kappa) (hbox : ∀ phi ∈ Phi, |phi| ≤ 1) :
    ballCap delta q M kappa (2*C0)*(Phi.card : ℝ)/degree delta M kappa C0 ≤ M^7 := by
  have hh := original_reference_ratio_six Phi hd hdq hq1 (by linarith) hC0 hCM hk hk2 hAD hbox
  have hm := mul_le_mul_of_nonneg_right hM (pow_nonneg (by linarith : 0 ≤ M) 6)
  exact hh.trans (by nlinarith only [hm])
/-- Algebraic accounting after the original AD supplier has proved its
 ratio bound. The public source theorem below discharges that bound. -/
theorem bcBeta_inverse_le {alpha D U N L M : ℝ}
    (ha : 0 < alpha) (hD : 0 < D) (hU : 0 < U) (hN : 0 < N) (hL : 0 < L)
    (hLM : L ≤ M) (hM : 72 ≤ M) (hratio : U*N/D ≤ M^7) :
    (bcBeta alpha D U N L)⁻¹ ≤ M^16/alpha := by
  have hM0 : 0 ≤ M := by linarith
  have hR0 : 0 ≤ U*N/D := by positivity
  have hp := pow_le_pow_left₀ hR0 hratio 2
  have hLp := mul_le_mul hLM hp (sq_nonneg _) hM0
  have hcoef := mul_le_mul_of_nonneg_left hLp (by norm_num : (0:ℝ)≤72)
  have hlast := mul_le_mul_of_nonneg_right hM (pow_nonneg hM0 15)
  rw [bcBeta_inverse_eq ha.ne' hD.ne' hU.ne' hN.ne' hL.ne']
  apply div_le_div_of_nonneg_right _ ha.le
  calc
    _ ≤ 72*(M*(M^7)^2) := by nlinarith only [hcoef]
    _ = 72*M^15 := by ring
    _ ≤ M^16 := by nlinarith only [hlast]
/-- For the actual macro-box normalization S0=4*C0*M, B mass costs at
 most four further M powers beyond graph and fine-height density. -/
theorem heightMass_inverse_le {alpha D U N L lambdaFine C0 M : ℝ}
    (ha : 0 < alpha) (hD : 0 < D) (hU : 0 < U) (hN : 0 < N) (hL : 0 < L)
    (hl : 0 < lambdaFine) (hC : 0 < C0) (hCM : C0 ≤ M)
    (hM : 12 ≤ M) (hbeta : (bcBeta alpha D U N L)⁻¹ ≤ M^16/alpha) :
    (heightMass alpha D U N L lambdaFine C0 M)⁻¹ ≤ M^20/(alpha*lambdaFine) := by
  have hM0 : 0 < M := by linarith
  have hcoef : 12*C0*M^2 ≤ M^4 := by
    have h1 := mul_le_mul_of_nonneg_right hCM (show 0 ≤ 12*M^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hM (pow_nonneg hM0.le 3)
    nlinarith only [h1,h2]
  have hb : 0 ≤ (bcBeta alpha D U N L)⁻¹ := (inv_pos.mpr (bcBeta_pos ha hD hU hN hL)).le
  have hp := mul_le_mul hcoef hbeta hb (pow_nonneg hM0.le 4)
  rw [heightMass_inverse_eq ha hD hU hN hL hl hC hM0]
  calc
    _ ≤ (M^4*(M^16/alpha))/lambdaFine := div_le_div_of_nonneg_right hp hl.le
    _ = _ := by ring
/-- Exact conversion back to original delta exponents. -/
lemma original_power_quotient (delta eta w : ℝ) (hd : 0 < delta) (n : ℕ) :
    (delta^(-eta))^n/delta^(w*eta)=delta^(-(w+(n:ℝ))*eta) := by
  rw [← Real.rpow_mul_natCast hd.le,← Real.rpow_sub hd]
  congr 1
  ring
lemma original_two_power_quotient (delta eta w h : ℝ) (hd : 0 < delta) (n : ℕ) :
    (delta^(-eta))^n/(delta^(w*eta)*delta^(h*eta))=delta^(-(w+h+(n:ℝ))*eta) := by
  rw [← Real.rpow_add hd,← Real.rpow_mul_natCast hd.le,← Real.rpow_sub hd]
  congr 1
  ring
/-- The explicit source coefficients and their exponent envelopes are
 conclusions of actual coarse AD, source constants and original count
 exponents. No angular population-ratio or final-density envelope is assumed. -/
theorem original_source_coefficients (Phi : Finset ℝ)
    {delta eta q kappa C0 L w h : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hM : 5101248 ≤ delta^(-eta)) (hC : 1 ≤ C0) (hCM : C0 ≤ delta^(-eta))
    (hL : 0 < L) (hLM : L ≤ delta^(-eta)) (_hw : 0 ≤ w) (_hh : 0 ≤ h)
    (hk : 0 ≤ kappa) (hk2 : kappa ≤ 2)
    (hPhi : Phi.Nonempty) (hAD : ADBounds Phi q (delta^(-eta)) kappa)
    (hbox : ∀ phi ∈ Phi, |phi| ≤ 1) :
    let M := delta^(-eta)
    let D := degree delta M kappa C0
    let U := ballCap delta q M kappa (2*C0)
    let alpha := delta^(w*eta)
    let lambdaFine := delta^(h*eta)
    0 < bcBeta alpha D U (Phi.card : ℝ) L ∧
    0 < heightMass alpha D U (Phi.card : ℝ) L lambdaFine C0 M ∧
    4*menuBeta alpha D U (Phi.card : ℝ)*U^2*(Phi.card : ℝ)^2=alpha*D^2 ∧
    (bcBeta alpha D U (Phi.card : ℝ) L)⁻¹ ≤ delta^(-(w+16)*eta) ∧
    (heightMass alpha D U (Phi.card : ℝ) L lambdaFine C0 M)⁻¹ ≤ delta^(-(w+h+20)*eta) := by
  dsimp only
  have hM0 : 0 < delta^(-eta) := Real.rpow_pos_of_pos hd _
  have hC0 : 0 < C0 := lt_of_lt_of_le (by norm_num) hC
  have hD := degree_pos (kappa := kappa) hd hM0 hC0.le
  have hU := ballCap_pos (kappa := kappa) hd (hd.trans_le hdq) hM0 (show 0 ≤ 2*C0 by positivity)
  have hN : 0 < (Phi.card : ℝ) := Nat.cast_pos.mpr hPhi.card_pos
  have ha : 0 < delta^(w*eta) := Real.rpow_pos_of_pos hd _
  have hl : 0 < delta^(h*eta) := Real.rpow_pos_of_pos hd _
  have hratio := original_reference_ratio_seven Phi hd hdq hq1 (by linarith : 4096 ≤ delta^(-eta)) hC0.le hCM hk hk2 hAD hbox
  have hb := bcBeta_inverse_le ha hD hU hN hL hLM (by linarith : 72 ≤ delta^(-eta)) hratio
  have hm := heightMass_inverse_le ha hD hU hN hL hl hC0 hCM (by linarith : 12 ≤ delta^(-eta)) hb
  exact ⟨bcBeta_pos ha hD hU hN hL,heightMass_pos ha hD hU hN hL hl hC0 hM0,
    menu_scale_eq _ _ hU.ne' hN.ne',
    by simpa only [original_power_quotient _ _ _ hd 16,Nat.cast_ofNat] using hb,
    by simpa only [original_two_power_quotient _ _ _ _ hd 20,Nat.cast_ofNat] using hm⟩
/-- Exact window coefficient used by the native nine-window constructor. -/
lemma windowBeta_eq (alpha D U N : ℝ) :
    windowBeta alpha D U N=alpha*D^2/(36*U^2*N^2) := by
  unfold windowBeta menuBeta
  ring
/-- Convert the literal original coarse-graph inequality returned by
 exists_actual_BC_graph to its chosen final coefficient. -/
theorem chosen_BC_graph_density {alpha D U N L a b c e : ℝ} (hL : 0 < L)
    (hgraph : windowBeta alpha D U N*a*b*c ≤ 2*L*e) :
    bcBeta alpha D U N L*a*b*c ≤ e := by
  have hh : (windowBeta alpha D U N*a*b*c)/(2*L) ≤ e :=
    (div_le_iff₀ (by positivity : 0 < 2*L)).mpr (by nlinarith only [hgraph])
  unfold bcBeta
  convert hh using 1
  ring
/-- The mass coefficient is realized by the actual graph-selected sigma
 labels at the shared nearby mesh. It is not an assumed B lower bound. -/
theorem chosen_actual_B_mass (Z : Finset ℝ) (j : ℕ)
    {delta eta sigma rho r mu alpha D U N L lambdaFine C0 : ℝ}
    (hd : 0 < delta) (hsigma : delta ≤ sigma) (hrho : 0 < rho) (hr : 0 < r)
    (ha : 0 < alpha) (hD : 0 < D) (hU : 0 < U) (hN : 0 < N) (hL : 0 < L)
    (hl : 0 ≤ lambdaFine) (hC : 0 < C0)
    (hover : sigma ≤ delta^(-eta)*r)
    (hhalf : (r/(rho*spatialNormalization C0 (delta^(-eta))))/2 ≤ mu)
    (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → delta ≤ |z-z'|)
    (hheight : lambdaFine*rho ≤ (Z.card : ℝ)*delta)
    (hretention : windowBeta alpha D U N*(Z.card : ℝ) ≤ L*((bin Z (coarseHeight sigma) j).card : ℝ)) :
    heightMass alpha D U N L lambdaFine C0 (delta^(-eta)) ≤
      mu*(((bin Z (coarseHeight sigma) j).image (coarseHeight sigma)).card : ℝ) := by
  have hM : 0 < delta^(-eta) := Real.rpow_pos_of_pos hd _
  have hS : 0 < spatialNormalization C0 (delta^(-eta)) := by unfold spatialNormalization; positivity
  have hm := selected_height_mass Z j hd hsigma hrho hS hr
    (windowBeta_pos ha hD hU hN).le hl hL hover hsep hheight hretention
  have hh := NativeDyadicMeshSelection.original_mass_at_nearby_mesh hhalf (Nat.cast_nonneg _) hm
  have heq : (windowBeta alpha D U N*lambdaFine/(3*L*spatialNormalization C0 (delta^(-eta))*delta^(-eta)))/2=
      heightMass alpha D U N L lambdaFine C0 (delta^(-eta)) := by
    rw [heightMass_nearby_eq]
    ring
  rwa [heq] at hh
end NativeOriginalGraphDensityCosts
