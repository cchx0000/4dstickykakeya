import Theorems.Thm_StickyKakeya4_native_joint_uniform_coarse_relations
import Theorems.Thm_StickyKakeya4_native_uniform_multiplicity_restriction
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
import Theorems.Thm_StickyKakeya4_native_coarse_fine_multiplicity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

noncomputable section
namespace NativeUniformRetentionTransfer
open Classical Finset
open NativeJointUniformCoarseRelations NativeWeightedPointPopulations

/-- A bounded menu of target labels in each source fiber controls the whole image. -/
lemma image_card_le_mul_of_fiber_images {X A B : Type*}
    [DecidableEq A] [DecidableEq B]
    (E : Finset X) (f : X → A) (g : X → B) (K : ℕ)
    (hmenu : ∀b∈E.image g,((E.filter (fun x => g x=b)).image f).card ≤ K) :
    (E.image f).card ≤ K*(E.image g).card := by
  have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
    E f g (K:ℝ) (fun b hb => Nat.cast_le.mpr (hmenu b hb))
  exact_mod_cast hh

/-- Uniform fine-label fibers control every actual subset in cross-multiplied form. -/
lemma uniform_subset_card_cross {X B : Type*} [DecidableEq X] [DecidableEq B]
    (E F : Finset X) (hFE : F⊆E) (g : X → B) (Q : ℕ)
    (hU : HasUniformFibers E Q g) :
    F.card*(E.image g).card ≤ Q^2*E.card*(F.image g).card := by
  have hpoint : ∀a∈E.image g,∀b∈E.image g,
      projectedWeight (fun _ : X => 1) g E a ≤
        Q^2*projectedWeight (fun _ : X => 1) g E b := by
    intro a ha b hb
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hb
    rw [←degree_eq_projectedWeight,←degree_eq_projectedWeight,
      unit_degree_eq_fiber,unit_degree_eq_fiber]
    exact hU x hx y hy
  simpa [SelfUniform.mass] using
    NativeUniformMultiplicityRestriction.subset_weighted_mass_cross
      (fun _ : X => 1) g E F hFE (Q^2) hpoint

/-- Finite menus in both directions transfer retained fine-label mass to
retained coarse labels. No uniformity of the coarse labels is assumed. -/
theorem finite_menu_retention_cross {X A B : Type*}
    [DecidableEq X] [DecidableEq A] [DecidableEq B]
    (E F : Finset X) (hFE : F⊆E) (f : X → A) (g : X → B)
    (Q A0 B0 : ℕ) (hU : HasUniformFibers E Q g)
    (hfg : ∀a∈E.image f,((E.filter (fun x => f x=a)).image g).card ≤ A0)
    (hgf : ∀b∈E.image g,((E.filter (fun x => g x=b)).image f).card ≤ B0) :
    F.card*(E.image f).card ≤ A0*B0*Q^2*E.card*(F.image f).card := by
  have hE := image_card_le_mul_of_fiber_images E f g B0 hgf
  have hF : (F.image g).card ≤ A0*(F.image f).card := by
    apply image_card_le_mul_of_fiber_images F g f A0
    intro a ha
    have hsub : F.filter (fun x => f x=a) ⊆ E.filter (fun x => f x=a) :=
      filter_subset_filter _ hFE
    exact (card_le_card (image_subset_image hsub)).trans
      (hfg a (image_subset_image hFE ha))
  calc
    F.card*(E.image f).card ≤ F.card*(B0*(E.image g).card) := Nat.mul_le_mul_left _ hE
    _ = B0*(F.card*(E.image g).card) := by ring
    _ ≤ B0*(Q^2*E.card*(F.image g).card) :=
      Nat.mul_le_mul_left _ (uniform_subset_card_cross E F hFE g Q hU)
    _ ≤ B0*(Q^2*E.card*(A0*(F.image f).card)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hF)
    _ = A0*B0*Q^2*E.card*(F.image f).card := by ring

/-- Cancel the nonempty source cardinality to transfer a real retention fraction. -/
theorem retained_image_card {X A B : Type*}
    [DecidableEq X] [DecidableEq A] [DecidableEq B]
    (E F : Finset X) (hFE : F⊆E) (hEn : E.Nonempty)
    (f : X → A) (g : X → B) (Q A0 B0 : ℕ)
    (hU : HasUniformFibers E Q g)
    (hfg : ∀a∈E.image f,((E.filter (fun x => f x=a)).image g).card ≤ A0)
    (hgf : ∀b∈E.image g,((E.filter (fun x => g x=b)).image f).card ≤ B0)
    (theta : ℝ) (hret : theta*(E.card:ℝ) ≤ F.card) :
    theta*(E.image f).card ≤ (A0:ℝ)*B0*(Q:ℝ)^2*(F.image f).card := by
  have hcross : (F.card:ℝ)*(E.image f).card ≤
      (A0:ℝ)*B0*(Q:ℝ)^2*E.card*(F.image f).card := by
    exact_mod_cast finite_menu_retention_cross E F hFE f g Q A0 B0 hU hfg hgf
  have hEpos : (0:ℝ) < E.card := by exact_mod_cast card_pos.mpr hEn
  apply (mul_le_mul_iff_right₀ hEpos).mp
  calc
    (E.card:ℝ)*(theta*(E.image f).card) = (theta*E.card)*(E.image f).card := by ring
    _ ≤ (F.card:ℝ)*(E.image f).card :=
      mul_le_mul_of_nonneg_right hret (Nat.cast_nonneg _)
    _ ≤ (A0:ℝ)*B0*(Q:ℝ)^2*E.card*(F.image f).card := hcross
    _ = (E.card:ℝ)*((A0:ℝ)*B0*(Q:ℝ)^2*(F.image f).card) := by ring

/-- The retained pair image has smaller point support, so its multiplicity
retains the same paid fraction. All positive menu costs follow from retention. -/
theorem retained_image_multiplicity {X P Z B : Type*}
    [DecidableEq X] [DecidableEq P] [DecidableEq Z] [DecidableEq B]
    (E F : Finset X) (hFE : F⊆E) (hEn : E.Nonempty)
    (f : X → P×Z) (g : X → B) (Q A0 B0 : ℕ)
    (hU : HasUniformFibers E Q g)
    (hfg : ∀a∈E.image f,((E.filter (fun x => f x=a)).image g).card ≤ A0)
    (hgf : ∀b∈E.image g,((E.filter (fun x => g x=b)).image f).card ≤ B0)
    (theta : ℝ) (htheta : 0 < theta) (hret : theta*(E.card:ℝ) ≤ F.card) :
    (theta/((A0:ℝ)*B0*(Q:ℝ)^2))*
        NativeIncidenceMultiplicityTower.multiplicity (E.image f) ≤
      NativeIncidenceMultiplicityTower.multiplicity (F.image f) := by
  have hcard := retained_image_card E F hFE hEn f g Q A0 B0 hU hfg hgf theta hret
  have hEpos : (0:ℝ) < (E.image f).card := by
    exact_mod_cast card_pos.mpr (hEn.image f)
  have hcost : 0 < (A0:ℝ)*B0*(Q:ℝ)^2 := by
    have hh : 0 < (A0:ℝ)*B0*(Q:ℝ)^2*(F.image f).card :=
      (mul_pos htheta hEpos).trans_le hcard
    exact (mul_pos_iff.mp hh).resolve_right (fun h => (not_lt_of_ge (Nat.cast_nonneg _)) h.2) |>.1
  apply NativeCoarseFineMultiplicity.retained_incidence_multiplicity
    (E.image f) (F.image f) (image_subset_image hFE) (div_nonneg htheta.le hcost.le)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hcost).mpr
  simpa only [mul_comm] using hcard

end NativeUniformRetentionTransfer
