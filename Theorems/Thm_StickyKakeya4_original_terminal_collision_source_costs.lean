import Theorems.Thm_StickyKakeya4_original_scalar_collision_mass
import Theorems.Thm_StickyKakeya4_native_original_graph_density_costs
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalTerminalCollisionSourceCosts
open Classical OriginalScalarCollisionMass NativeOriginalGraphDensityCosts OriginalAngularSourcePopulation
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus FiniteVoronoiRealADCoarsening
/-- The literal source reference-angle error controls the scalar terminal
 image loss, including its fine realization error. -/
theorem scalar_label_loss_square {delta q rho C0 M : ℝ}
    (hq : 0 < q) (hdq : delta ≤ q) (hRho : rho ≤ q+C0*delta)
    (hC0 : 0 ≤ C0) (hCM : C0 ≤ M) (hM : 6 ≤ M) :
    2*rho/q+2 ≤ M^2 := by
  have hc := mul_le_mul_of_nonneg_left hdq hC0
  have hr : rho ≤ (1+C0)*q := by nlinarith only [hRho,hc]
  have hdiv : 2*rho/q ≤ 2*(1+C0) := (div_le_iff₀ hq).mpr (by nlinarith only [hr])
  have hM1 : 1 ≤ M := by linarith only [hM]
  nlinarith only [hdiv,hCM,hM,hM1]
lemma source_loss_power (delta eta : ℝ) (hd : 0 < delta) (n : ℕ) :
    (delta^(-eta))^n=delta^(-(n:ℝ)*eta) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hd.le]
  congr 1
  ring
/-- The original incidence source exponent supplies the scalar collision
 coefficient with a fixed exponent. The C, terminal-image and angular
 ratios are evaluated from their real source formulas rather than assumed. -/
theorem original_collision_alpha_source_lower (Phi : Finset ℝ)
    {delta eta q rho C0 kappa t : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hM : 5101248 ≤ delta^(-eta)) (hC0 : 1 ≤ C0) (hCM : C0 ≤ delta^(-eta))
    (hRho0 : 0 ≤ rho) (hRho : rho ≤ q+C0*delta)
    (hk : 0 ≤ kappa) (hk2 : kappa ≤ 2) (hPhi : Phi.Nonempty)
    (hAD : ADBounds Phi q (delta^(-eta)) kappa) (hbox : ∀ phi ∈ Phi, |phi| ≤ 1) :
    delta^((29+4*t)*eta) ≤
      collisionAlpha (delta^(t*eta)) ((delta^(-eta))^4) (2*rho/q+2)
        (degree delta (delta^(-eta)) kappa C0) (ballCap delta q (delta^(-eta)) kappa (2*C0)) Phi.card := by
  let M := delta^(-eta)
  let D := degree delta M kappa C0
  let U := ballCap delta q M kappa (2*C0)
  let H0 := 2*rho/q+2
  have hMp : 0 < M := Real.rpow_pos_of_pos hd _
  have hM0 := hMp.le
  have hC00 : 0 ≤ C0 := by linarith only [hC0]
  have hq : 0 < q := hd.trans_le hdq
  have hD : 0 < D := degree_pos hd hMp hC00
  have hU : 0 < U := ballCap_pos hd hq hMp (by positivity)
  have hN : (0:ℝ)<Phi.card := Nat.cast_pos.mpr hPhi.card_pos
  have hH0 : 0 < H0 := by dsimp [H0]; positivity
  have hH : H0 ≤ M^2 := scalar_label_loss_square hq hdq hRho hC00 hCM (by dsimp [M]; linarith only [hM])
  have hR : U*(Phi.card:ℝ)/D ≤ M^7 := original_reference_ratio_seven Phi hd hdq hq1
    (by dsimp [M]; linarith only [hM]) hC00 hCM hk hk2 hAD hbox
  have hdenom : (M^4)^5*H0*(U*(Phi.card:ℝ)/D) ≤ M^29 := by
    calc
      _ ≤ (M^4)^5*M^2*M^7 := by gcongr
      _ = _ := by ring
  have hdenom0 : 0 < (M^4)^5*H0*(U*(Phi.card:ℝ)/D) := by positivity
  have hnumer : (delta^(t*eta))^4=delta^(4*t*eta) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hd.le]
    congr 1
    norm_num
    ring
  have hid : delta^((29+4*t)*eta)=(delta^(t*eta))^4/M^29 := by
    rw [hnumer,source_loss_power delta eta hd 29,← Real.rpow_sub hd]
    congr 1
    norm_num
    ring
  rw [hid]
  exact div_le_div_of_nonneg_left (by positivity) hdenom0 hdenom
/-- The actual scalar-collision W population has the source power used by
 the rich-core constructor. Only ORIGINAL point incidence and average
 height incidence counts occur among the population hypotheses. -/
theorem scalar_collision_mass_at_source_power {P T : Type*} [DecidableEq P] [DecidableEq T]
    (I : Finset (P × T)) (height : P → ℝ) (tubeU : T → ℝ) (Z Phi : Finset ℝ)
    (hI : I.Nonempty) (hPhi : Phi.Nonempty)
    {delta eta q rho C0 kappa t : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hM : 5101248 ≤ delta^(-eta)) (hC0 : 1 ≤ C0) (hCM : C0 ≤ delta^(-eta))
    (hRho0 : 0 ≤ rho) (hRho : rho ≤ q+C0*delta)
    (hk : 0 ≤ kappa) (hk2 : kappa ≤ 2)
    (hAD : ADBounds Phi q (delta^(-eta)) kappa) (hbox : ∀ phi ∈ Phi, |phi| ≤ 1)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdegree : degree delta (delta^(-eta)) kappa C0*(TwoTubePathCollisionCount.points I).card ≤ (I.card:ℝ))
    (hheightMass : delta^(t*eta)*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card ≤ (vertices I height).card)
    (hcover : ∀ v ∈ TwoTubePathCollisionCount.tubes I, ∃ a ∈ Phi, |tubeU v-a| ≤ rho) :
    let C := (delta^(-eta))^4
    let D := degree delta (delta^(-eta)) kappa C0
    let U := ballCap delta q (delta^(-eta)) kappa (2*C0)
    delta^((29+4*t)*eta)*(C^5*D^2*U*(Z.card:ℝ)^2)*(vertices I height).card ≤
      ((witnesses I height (scalarTerminalCell q tubeU)).card:ℝ) := by
  have hMp : 0 < delta^(-eta) := Real.rpow_pos_of_pos hd _
  have hC00 : 0 ≤ C0 := by linarith only [hC0]
  have hD := degree_pos (kappa := kappa) hd hMp hC00
  have hU := ballCap_pos (kappa := kappa) hd (hd.trans_le hdq) hMp (show 0 ≤ 2*C0 by positivity)
  have ha := original_collision_alpha_source_lower Phi hd hdq hq1 hM hC0 hCM hRho0 hRho hk hk2 hPhi hAD hbox (t := t)
  have hm := scalar_original_collision_mass I height tubeU Z Phi hI hPhi (hd.trans_le hdq) hRho0
    (show 0 < (delta^(-eta))^4 by positivity) hD hU (Real.rpow_pos_of_pos hd (t*eta)).le
    hheight hdegree hheightMass hcover
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha (by positivity)) (Nat.cast_nonneg _)).trans hm
end OriginalTerminalCollisionSourceCosts
