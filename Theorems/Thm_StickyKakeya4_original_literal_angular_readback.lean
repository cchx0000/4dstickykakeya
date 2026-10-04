import Theorems.Thm_StickyKakeya4_original_literal_common_alphabet
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalLiteralAngularReadback
open Classical Finset NativeScalarCoverAD FiniteVoronoiPopulation
/-- The literal scalar cover law itself supplies the exponent range.
 No metric separation of the original source alphabet is assumed. -/
theorem cover_exponent_lt_two (Phi : Finset ℝ) (hPhi : Phi.Nonempty) {q K kappa : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hK : 1 ≤ K) (hsmall : K*q ≤ 1/8)
    (H : CoverADBounds Phi q K kappa) (hbox : ∀ phi ∈ Phi, |phi| ≤ 1) : kappa < 2 := by
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  obtain ⟨a,ha⟩ := hPhi
  have hlo := (H a ha 1 hq1 le_rfl).1
  have hsub : coverCount Phi q a 1 ≤ ((Phi.image (cell q)).card:ℝ) := by
    rw [OriginalScalarLiteralCoverCount.cover_count_readback]
    exact_mod_cast card_le_card (image_subset_image (filter_subset _ _) (f := cell q))
  have hgrid : ((Phi.image (cell q)).card:ℝ) ≤ 2/q+2 := by
    exact NativeTangentGridCoarsening.scalar_interval_grid_card Phi id (c := -1) hq
      (by norm_num : (0:ℝ)≤2) (fun phi hphi => by
        have hh := abs_le.mp (hbox phi hphi)
        exact ⟨hh.1,by change phi ≤ -1+2; linarith only [hh.2]⟩)
  have hratio : 1 ≤ 1/q := (le_div_iff₀ hq).mpr (by simpa using hq1)
  have hbound : (1/q)^kappa ≤ K*(4/q) := by
    have hh := (div_le_iff₀ hK0).mp (hlo.trans (hsub.trans hgrid))
    have hc : 2/q+2 ≤ 4/q := by
      rw [show 2/q=2*(1/q) by ring,show 4/q=4*(1/q) by ring]
      linarith only [hratio]
    exact hh.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hc hK0.le)
  by_contra h
  have hk : 2 ≤ kappa := le_of_not_gt h
  have hp : (1/q)^2 ≤ (1/q)^kappa := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hratio hk
  have hh := mul_le_mul_of_nonneg_right (hp.trans hbound) (sq_nonneg q)
  have hleft : (1/q)^2*q^2=1 := by field_simp
  have hright : (K*(4/q))*q^2=4*K*q := by field_simp
  rw [hleft,hright] at hh
  linarith only [hh,hsmall]
/-- The actual common net preserves the old scalar realization error
 exactly at q plus the original fine-scale tube error. -/
theorem original_tube_reference_error {P T : Type*} (E : Finset P) (fine : P → Finset ℝ)
    (C : Finset ℝ) (I : Finset (P × T)) (u : T → ℝ) {q delta C0 : ℝ}
    (hI : ∀ e ∈ I, e.1 ∈ E)
    (hrealize : ∀ e ∈ I, ∃ phi ∈ fine e.1, |u e.2-phi| ≤ C0*delta)
    (hcover : ∀ p ∈ E, ∀ phi ∈ fine p, ∃ c ∈ C, dist phi c < q) :
    ∀ e ∈ I, ∃ c ∈ C, |u e.2-c| ≤ q+C0*delta := by
  intro e he
  obtain ⟨phi,hphi,hup⟩ := hrealize e he
  obtain ⟨c,hc,hpc⟩ := hcover e.1 (hI e he) phi hphi
  refine ⟨c,hc,?_⟩
  have hh := abs_sub_le (u e.2) phi c
  rw [Real.dist_eq] at hpc
  linarith only [hh,hup,hpc]
end OriginalLiteralAngularReadback
