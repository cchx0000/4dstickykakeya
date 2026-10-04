import Theorems.Thm_StickyKakeya4_original_terminal_collision_source_costs
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace OriginalRetainedIncidenceDegree
open Classical OriginalScalarCollisionMass OriginalTerminalCollisionSourceCosts
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus
/-- Aggregate original point degree survives an incidence refinement with
 its actual retained mass loss; no postselection pointwise degree is assumed. -/
theorem retained_original_aggregate_degree {P T : Type*} [DecidableEq P] [DecidableEq T]
    (I I0 : Finset (P × T)) {D F : ℝ} (hD : 0 ≤ D) (hF : 0 < F)
    (hsub : I ⊆ I0) (hdegree : D*(TwoTubePathCollisionCount.points I0).card ≤ (I0.card:ℝ))
    (hret : (I0.card:ℝ) ≤ F*(I.card:ℝ)) :
    (D/F)*(TwoTubePathCollisionCount.points I).card ≤ (I.card:ℝ) := by
  have hp : ((TwoTubePathCollisionCount.points I).card:ℝ) ≤
      ((TwoTubePathCollisionCount.points I0).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.image_subset_image hsub)
  have hh := (mul_le_mul_of_nonneg_left hp hD).trans (hdegree.trans hret)
  have hdiv : (D*(TwoTubePathCollisionCount.points I).card)/F ≤ (I.card:ℝ) :=
    (div_le_iff₀ hF).mpr (by nlinarith only [hh])
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hdiv
/-- The normalized collision coefficient pays the CUBE of any aggregate
 degree retention loss. The output uses the original reference D and U. -/
theorem scalar_collision_mass_with_degree_retention
    {P T H : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq H]
    (I : Finset (P × T)) (height : P → H) (u : T → ℝ) (Z : Finset H) (Phi : Finset ℝ)
    (hI : I.Nonempty) (hPhi : Phi.Nonempty)
    {q error C D U lambda gamma : ℝ} (hq : 0 < q) (he : 0 ≤ error)
    (hC : 0 < C) (hD : 0 < D) (hU : 0 < U) (hlambda : 0 ≤ lambda) (hg : 0 < gamma)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdegree : (gamma*D)*(TwoTubePathCollisionCount.points I).card ≤ (I.card:ℝ))
    (hheightMass : lambda*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card ≤ (vertices I height).card)
    (hcover : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ∃ a ∈ Phi, |u t-a| ≤ error) :
    (gamma^3*collisionAlpha lambda C (2*error/q+2) D U Phi.card)*
      (C^5*D^2*U*(Z.card:ℝ)^2)*(vertices I height).card ≤
      ((witnesses I height (scalarTerminalCell q u)).card:ℝ) := by
  have hh := scalar_original_collision_mass I height u Z Phi hI hPhi hq he hC
    (mul_pos hg hD) hU hlambda hheight hdegree hheightMass hcover
  convert hh using 1
  unfold collisionAlpha
  field_simp
/-- The retained-degree loss is charged explicitly in the original power
 exponent. This identity changes no original height or angular parameter. -/
theorem collision_source_exponent_with_degree_retention {delta eta g t : ℝ} (hd : 0 < delta) :
    (delta^(g*eta))^3*delta^((29+4*t)*eta)=delta^((29+3*g+4*t)*eta) := by
  rw [← Real.rpow_mul_natCast hd.le,← Real.rpow_add hd]
  congr 1
  norm_num
  ring
/-- Actual original source AD formulas remain the reference coefficients
 after refinement, with the retained aggregate-degree exponent charged. -/
theorem scalar_collision_source_power_after_refinement
    {P T : Type*} [DecidableEq P] [DecidableEq T]
    (I : Finset (P × T)) (height : P → ℝ) (tubeU : T → ℝ) (Z Phi : Finset ℝ)
    (hI : I.Nonempty) (hPhi : Phi.Nonempty)
    {delta eta q rho C0 kappa t g : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hM : 5101248 ≤ delta^(-eta)) (hC0 : 1 ≤ C0) (hCM : C0 ≤ delta^(-eta))
    (hRho0 : 0 ≤ rho) (hRho : rho ≤ q+C0*delta)
    (hk : 0 ≤ kappa) (hk2 : kappa ≤ 2)
    (hAD : FiniteVoronoiRealADCoarsening.ADBounds Phi q (delta^(-eta)) kappa)
    (hbox : ∀ phi ∈ Phi, |phi| ≤ 1)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdegree : (delta^(g*eta)*OriginalAngularSourcePopulation.degree delta (delta^(-eta)) kappa C0)*
      (TwoTubePathCollisionCount.points I).card ≤ (I.card:ℝ))
    (hheightMass : delta^(t*eta)*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card ≤ (vertices I height).card)
    (hcover : ∀ v ∈ TwoTubePathCollisionCount.tubes I, ∃ a ∈ Phi, |tubeU v-a| ≤ rho) :
    let C := (delta^(-eta))^4
    let D := OriginalAngularSourcePopulation.degree delta (delta^(-eta)) kappa C0
    let U := OriginalAngularSourcePopulation.ballCap delta q (delta^(-eta)) kappa (2*C0)
    delta^((29+3*g+4*t)*eta)*(C^5*D^2*U*(Z.card:ℝ)^2)*(vertices I height).card ≤
      ((witnesses I height (scalarTerminalCell q tubeU)).card:ℝ) := by
  have hMp : 0 < delta^(-eta) := Real.rpow_pos_of_pos hd _
  have hC00 : 0 ≤ C0 := by linarith only [hC0]
  have hD := OriginalAngularSourcePopulation.degree_pos (kappa := kappa) hd hMp hC00
  have hU := OriginalAngularSourcePopulation.ballCap_pos (kappa := kappa) hd (hd.trans_le hdq) hMp
    (show 0 ≤ 2*C0 by positivity)
  have ha := original_collision_alpha_source_lower Phi hd hdq hq1 hM hC0 hCM hRho0 hRho
    hk hk2 hPhi hAD hbox (t := t)
  have hm := scalar_collision_mass_with_degree_retention I height tubeU Z Phi hI hPhi
    (hd.trans_le hdq) hRho0 (show 0 < (delta^(-eta))^4 by positivity) hD hU
    (Real.rpow_pos_of_pos hd (t*eta)).le (Real.rpow_pos_of_pos hd (g*eta))
    hheight hdegree hheightMass hcover
  have ha' := mul_le_mul_of_nonneg_left ha (show 0 ≤ (delta^(g*eta))^3 by positivity)
  rw [collision_source_exponent_with_degree_retention hd] at ha'
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha' (by positivity)) (Nat.cast_nonneg _)).trans hm
end OriginalRetainedIncidenceDegree
