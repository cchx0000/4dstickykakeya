import Theorems.Thm_StickyKakeya4_finite_voronoi_real_ad_coarsening
import Theorems.Thm_StickyKakeya4_original_w_core_dynamics
import Mathlib.Tactic
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalAngularAlphabetTranslation
open Classical FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
def shifted (Phi : Finset ℝ) (anchor : ℝ) := Phi.image (fun phi => phi-anchor)
lemma subtract_injective (anchor : ℝ) : Function.Injective (fun phi : ℝ => phi-anchor) := by intro x y h; linarith
lemma shifted_card (Phi : Finset ℝ) (anchor : ℝ) : (shifted Phi anchor).card=Phi.card :=
  Finset.card_image_of_injective Phi (subtract_injective anchor)
lemma shifted_ball (Phi : Finset ℝ) (anchor center radius : ℝ) :
    carrierBall (shifted Phi anchor) (center-anchor) radius=(carrierBall Phi center radius).image (fun phi => phi-anchor) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxPhi,hxd⟩ := (mem_carrierBall _ _ _ _).mp hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hxPhi
    have hd : dist p center ≤ radius := by simpa only [Real.dist_eq,sub_sub_sub_cancel_right] using hxd
    exact Finset.mem_image.mpr ⟨p,(mem_carrierBall _ _ _ _).mpr ⟨hp,hd⟩,rfl⟩
  · intro hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hpPhi,hpd⟩ := (mem_carrierBall _ _ _ _).mp hp
    apply (mem_carrierBall _ _ _ _).mpr
    exact ⟨Finset.mem_image_of_mem _ hpPhi,by simpa only [Real.dist_eq,sub_sub_sub_cancel_right] using hpd⟩
lemma shifted_ball_card (Phi : Finset ℝ) (anchor center radius : ℝ) :
    (carrierBall (shifted Phi anchor) (center-anchor) radius).card=(carrierBall Phi center radius).card := by
  rw [shifted_ball]
  exact Finset.card_image_of_injective _ (subtract_injective anchor)
theorem shifted_ADBounds (Phi : Finset ℝ) (anchor : ℝ) {mesh K kappa : ℝ}
    (hAD : ADBounds Phi mesh K kappa) : ADBounds (shifted Phi anchor) mesh K kappa := by
  intro c hc r hmr hr
  obtain ⟨phi,hphi,rfl⟩ := Finset.mem_image.mp hc
  rw [shifted_ball_card]
  exact hAD phi hphi r hmr hr
theorem shifted_separated (Phi : Finset ℝ) (anchor : ℝ) {mesh : ℝ}
    (hsep : Separated Phi mesh) : Separated (shifted Phi anchor) mesh := by
  intro x hx y hy hxy
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
  have hpq : p ≠ q := by intro h; subst q; exact hxy rfl
  simpa only [Real.dist_eq,sub_sub_sub_cancel_right] using hsep p hp q hq hpq
theorem shifted_box (Phi : Finset ℝ) (anchor : ℝ) (ha : anchor ∈ Phi)
    (hbox : ∀ phi ∈ Phi, |phi| ≤ 1) : ∀ c ∈ shifted Phi anchor, |c| ≤ 2 := by
  intro c hc
  obtain ⟨phi,hphi,rfl⟩ := Finset.mem_image.mp hc
  exact (abs_sub phi anchor).trans (by linarith [hbox phi hphi,hbox anchor ha])
theorem shifted_mesh (Phi : Finset ℝ) (anchor mesh : ℝ) (ha : anchor ∈ Phi)
    (hmesh : ∀ phi ∈ Phi, ∃ k : ℤ, phi=mesh*(k:ℝ)) : ∀ c ∈ shifted Phi anchor, ∃ k : ℤ, c=mesh*(k:ℝ) := by
  obtain ⟨j,hj⟩ := hmesh anchor ha
  intro c hc
  obtain ⟨phi,hphi,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨k,hk⟩ := hmesh phi hphi
  refine ⟨k-j,?_⟩
  rw [hk,hj,Int.cast_sub]
  ring
theorem shifted_card_lower (Phi : Finset ℝ) (hPhi : Phi.Nonempty) (anchor : ℝ)
    {mesh K kappa : ℝ} (hm : mesh ≤ 1) (hAD : ADBounds Phi mesh K kappa) :
    (1/mesh)^kappa/K ≤ ((shifted Phi anchor).card : ℝ) := by
  obtain ⟨p,hp⟩ := hPhi
  rw [shifted_card]
  exact (hAD p hp 1 hm le_rfl).1.trans (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _)))
variable {P T A : Type*} [DecidableEq T] [DecidableEq A]
theorem original_angles_subset (I : Finset (P × T)) (angle : T → A) (Phi : Finset A)
    (hPhi : ∀ p t, (p,t) ∈ I → angle t ∈ Phi) : OriginalWCoreDynamics.angles I angle ⊆ Phi := by
  intro a ha
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨pt,hpt,hptt⟩ := Finset.mem_image.mp ht
  exact hptt ▸ hPhi pt.1 pt.2 hpt
end OriginalAngularAlphabetTranslation
