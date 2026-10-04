import Theorems.Thm_StickyKakeya4_original_macro_direction_source
import Theorems.Thm_StickyKakeya4_original_selected_angular_incidences
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalSelectedFullDirection
open Classical Finset OriginalSelectedAngularIncidences
variable {P T : Type*} [DecidableEq P] [DecidableEq T]
/-- The SAME fine-angle selection used for the degree bounds retains a
 joint full-direction realization. Its original normal equation is at the
 actual scalar slope u; substituting the selected original phi costs A*C0.
 No second angular selection or new incidence density is assumed. -/
theorem selected_joint_direction_realization (E : Finset P) (fine : P → Finset ℝ)
    (source : P → ℝ → T) (I : Finset (P × T)) (height : P → ℝ)
    (offset : P → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (u : T → ℝ) (v : T → ℝ × ℝ)
    {delta C0 DirErr A : ℝ} (hd : 0 ≤ delta) (hC : 0 ≤ C0) (hD : 0 ≤ DirErr) (hA : 0 ≤ A)
    (hsource : ∀ p ∈ E, ∀ phi ∈ fine p, (p,source p phi) ∈ I ∧ |u (source p phi)-phi| ≤ C0*delta)
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (u t)‖ ≤ DirErr*delta)
    (hF : ∀ p ∈ E, ‖F (height p)‖ ≤ A) :
    ∀ p t, (p,t) ∈ incidences E fine source → ∃ phi ∈ fine p,
      |u t-phi| ≤ (C0+DirErr+A*C0)*delta ∧
      ‖v t-offset p-F (height p) phi‖ ≤ (C0+DirErr+A*C0)*delta := by
  intro p t hpt
  obtain ⟨hp,ht⟩ := (mem_incidences E fine source p t).mp hpt
  obtain ⟨phi,hphi,rfl⟩ := mem_image.mp ht
  obtain ⟨hpt0,hu⟩ := hsource p hp phi hphi
  have hv := hdir p (source p phi) hpt0
  have hvar : ‖F (height p) (u (source p phi)-phi)‖ ≤ A*(C0*delta) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hF p hp) hu (norm_nonneg _) hA)
  have hid : v (source p phi)-offset p-F (height p) phi=
      (v (source p phi)-offset p-F (height p) (u (source p phi)))+
        F (height p) (u (source p phi)-phi) := by
    rw [map_sub]
    abel
  refine ⟨phi,hphi,?_,?_⟩
  · nlinarith only [hu,mul_nonneg hD hd,mul_nonneg (mul_nonneg hA hC) hd]
  · rw [hid]
    have hh := (norm_add_le _ _).trans (add_le_add hv hvar)
    nlinarith only [hh,mul_nonneg hC hd]
/-- The original common-angle realization error fits the honest working
 scale rho=2q. The two required source inequalities remain explicit; no
 unscheduled field law or unchanged reference-error constant is inferred. -/
theorem coarse_reference_error_at_double_scale {delta q C0 : ℝ}
    (hq : 0 ≤ q) (hC : 0 ≤ C0) (hdq : delta ≤ q^2) (hCq : C0*q ≤ 1) :
    C0*delta+q ≤ 2*q := by
  have hd := mul_le_mul_of_nonneg_left hdq hC
  have hh := mul_le_mul_of_nonneg_right hCq hq
  nlinarith only [hd,hh]
end OriginalSelectedFullDirection
