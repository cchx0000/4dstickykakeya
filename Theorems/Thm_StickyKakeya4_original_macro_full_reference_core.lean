import Theorems.Thm_StickyKakeya4_original_macro_printed_w
import Theorems.Thm_StickyKakeya4_finite_voronoi_real_ad_coarsening
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
noncomputable section
namespace OriginalMacroFullReferenceCore
open Classical Finset TwoTubePathCollisionCount OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open OriginalMacroDirectionCells OriginalScalarCollisionMass FiniteVoronoiRealADCoarsening
variable {P T H K : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq H] [DecidableEq K]
omit [DecidableEq P] in
/-- The original full-direction population is compared to the selected
 ORIGINAL common alphabet using its already constructed lower AD bound. -/
theorem full_terminal_relative_image (I : Finset (P × T)) (u : T → ℝ) (v : T → ℝ × ℝ)
    (Phi : Finset ℝ) {q kappa Kdir Kphi : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hKd : 0 ≤ Kdir) (hKp : 0 < Kphi)
    (hPhi : Phi.Nonempty) (hAD : ADBounds Phi q Kphi kappa)
    (hsource : q^kappa*((directionCells (tubes I) (q/8) u v).card:ℝ) ≤ Kdir) :
    ((directionCells (tubes I) (q/8) u v).card:ℝ) ≤ Kdir*Kphi*(Phi.card:ℝ) := by
  obtain ⟨a,ha⟩ := hPhi
  have hlo := (scaled_bounds_of_ADBounds hq hKp hAD a ha 1 hq1 le_rfl).1
  have hcard : ((FiniteVoronoiPopulation.carrierBall Phi a 1).card:ℝ) ≤ (Phi.card:ℝ) :=
    Nat.cast_le.mpr (card_le_card (filter_subset _ _))
  have hmass : 1 ≤ Kphi*q^kappa*(Phi.card:ℝ) := by
    have hh := hlo.trans (mul_le_mul_of_nonneg_left hcard (by positivity))
    simpa only [Real.one_rpow] using hh
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hq kappa)).mp
  calc
    _ ≤ Kdir := hsource
    _ ≤ Kdir*(Kphi*q^kappa*(Phi.card:ℝ)) := by nlinarith only [hmass,hKd]
    _ = _ := by ring
/-- Original incidence counting generates W mass for any actual terminal
 image, including the genuine three-coordinate direction cells. -/
theorem full_original_collision_mass (I : Finset (P × T)) (height : P → H)
    (cell : T → K) (Z : Finset H) (Phi : Finset ℝ)
    (hI : I.Nonempty) (hPhi : Phi.Nonempty) {C D U lambda imageLoss : ℝ}
    (hC : 0 < C) (hD : 0 < D) (hU : 0 < U) (hlambda : 0 ≤ lambda)
    (hL : 0 < imageLoss)
    (hheight : ∀ p ∈ points I, height p ∈ Z)
    (hdegree : D*(points I).card ≤ (I.card:ℝ))
    (hheightMass : lambda*(Z.card:ℝ)*(tubes I).card ≤ (vertices I height).card)
    (himage : (((tubes I).image cell).card:ℝ) ≤ imageLoss*(Phi.card:ℝ)) :
    collisionAlpha lambda C imageLoss D U Phi.card *
      (C^5*D^2*U*(Z.card:ℝ)^2)*(vertices I height).card ≤
      ((witnesses I height cell).card:ℝ) := by
  have hN : (0:ℝ) < Phi.card := Nat.cast_pos.mpr hPhi.card_pos
  have hmass := original_incidence_population_collision_mass I height cell Z
    hI hheight hD.le hlambda hdegree hheightMass
  have hh : D^3*lambda^4*(Z.card:ℝ)^2*(vertices I height).card ≤
      imageLoss*(Phi.card:ℝ)*(witnesses I height cell).card :=
    hmass.trans (mul_le_mul_of_nonneg_right himage (Nat.cast_nonneg _))
  have hid : collisionAlpha lambda C imageLoss D U Phi.card *
      (C^5*D^2*U*(Z.card:ℝ)^2)*(vertices I height).card =
      (D^3*lambda^4*(Z.card:ℝ)^2*(vertices I height).card)/(imageLoss*(Phi.card:ℝ)) := by
    unfold collisionAlpha
    field_simp
  rw [hid]
  exact (div_le_iff₀ (mul_pos hL hN)).mpr (by simpa only [mul_comm] using hh)
def menuCoefficient (lambda C imageLoss D U N : ℝ) : ℝ :=
  collisionAlpha lambda C imageLoss D U N*D^2/(4*U^2*N^2)
/-- This is the actual persistent W core from original source counts. Its
 terminal cells imply the full printed direction condition, and its menus
 retain the same original Phi. No W mass or reduced menu density is assumed. -/
theorem exists_full_direction_reference_core (I : Finset (P × T)) (height : P → ℝ)
    (u : T → ℝ) (v : T → ℝ × ℝ) (Z Phi : Finset ℝ)
    (hI : I.Nonempty) (hPhi : Phi.Nonempty) {q error C D U lambda Kdir Kphi kappa : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hqr : q/8 ≤ error)
    (hC : 0 < C) (hD : 0 < D) (hU : 0 < U) (hlambda : 0 ≤ lambda)
    (hKd : 0 < Kdir) (hKp : 0 < Kphi) (hAD : ADBounds Phi q Kphi kappa)
    (hnear : ∀ t ∈ tubes I, ∃ a ∈ Phi, |u t-a| ≤ error)
    (hheight : ∀ p ∈ points I, height p ∈ Z)
    (hpoints : ∀ t z, ((pointsAt I height t z).card:ℝ) ≤ C)
    (hdegree : ∀ p ∈ points I, D ≤ ((tubesAt I p).card:ℝ))
    (hheightMass : lambda*(Z.card:ℝ)*(tubes I).card ≤ (vertices I height).card)
    (hball : ∀ p a, (((tubesAt I p).filter (fun t => |u t-a| ≤ error)).card:ℝ) ≤ U)
    (hsource : q^kappa*((directionCells (tubes I) (q/8) u v).card:ℝ) ≤ Kdir) :
    ∃ S ⊆ vertices I height, S.Nonempty ∧
      ((witnesses I height (directionCell (q/8) u v)).card:ℝ) ≤
        2*((RichWitnessCore.retained (witnesses I height (directionCell (q/8) u v))
          (fun w => endpoint height w.1) (fun w => endpoint height w.2) S).card:ℝ) ∧
      ∀ s ∈ S, menuCoefficient lambda C (Kdir*Kphi) D U Phi.card*
          (Z.card:ℝ)^2*(Phi.card:ℝ)^2 ≤
          ((coarseMenus I height (directionCell (q/8) u v)
            (OriginalReferenceAngleSelection.angle I u Phi hPhi error hnear) S s).card:ℝ) ∧
        coarseMenus I height (directionCell (q/8) u v)
          (OriginalReferenceAngleSelection.angle I u Phi hPhi error hnear) S s ⊆
          (Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi) := by
  have hN : (0:ℝ) < Phi.card := Nat.cast_pos.mpr hPhi.card_pos
  have himage := full_terminal_relative_image I u v Phi hq hq1 hKd.le hKp hPhi hAD hsource
  have hmass := full_original_collision_mass I height (directionCell (q/8) u v) Z Phi hI hPhi
    hC hD hU hlambda (mul_pos hKd hKp) hheight (original_point_degrees_total I hdegree)
    hheightMass himage
  have hscale : 4*menuCoefficient lambda C (Kdir*Kphi) D U Phi.card*U^2*(Phi.card:ℝ)^2 ≤
      collisionAlpha lambda C (Kdir*Kphi) D U Phi.card*D^2 := by
    have he : 4*menuCoefficient lambda C (Kdir*Kphi) D U Phi.card*U^2*(Phi.card:ℝ)^2 =
        collisionAlpha lambda C (Kdir*Kphi) D U Phi.card*D^2 := by
      unfold menuCoefficient
      field_simp
    exact he.le
  exact OriginalReferenceAngleSelection.exists_full_reference_rich_core I height
    (directionCell (q/8) u v) u Z Phi hI hPhi error hnear hC hU
    (by unfold collisionAlpha; positivity) hheight hpoints
    (OriginalMacroPrintedW.original_full_terminal_fiber_cap I u v hq hqr hball) hball hmass hscale
end OriginalMacroFullReferenceCore
