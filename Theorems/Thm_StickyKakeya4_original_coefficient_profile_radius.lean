import Theorems.Thm_StickyKakeya4_original_coefficient_density_profile
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
noncomputable section
open Classical

namespace OriginalCoefficientProfileRadius
open OriginalCoefficientRadius OriginalCoefficientDensityProfile GKZOriginalGapEnergy

/-- When the ORIGINAL profile is actually available at the selected radius,
it gives the stronger radius bound required before homogeneous amplification.
A profile below its stated cutoff is never used. -/
theorem original_available_profile_radius (D S : Finset ℝ)
    {delta cutoff kappa B K u : ℝ} (hdelta : 0 < delta) (hkappa : 0 ≤ kappa)
    (hS : S.Nonempty) (hSD : S⊆D) (hB : radius D delta ≤ B)
    (hmax : ∀ T : Finset ℝ, T⊆D →
      (T.card:ℝ)/(radius T delta)^kappa ≤ (S.card:ℝ)/(radius S delta)^kappa)
    (hcutoff : cutoff ≤ radius S delta) (hr1 : radius S delta ≤ 1)
    (hprofile : ScalarFrostman D cutoff K u) :
    1 ≤ K*B^kappa*(radius S delta)^(u-kappa) := by
  obtain ⟨c,hc⟩ := hS
  have hR := hdelta.trans_le (mesh_le_radius S delta)
  have hBp := (hdelta.trans_le (mesh_le_radius D delta)).trans_le hB
  have hN : (0:ℝ) < D.card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨c,hSD hc⟩)
  have hsub : S⊆D.filter (fun x => |x-c| ≤ radius S delta) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hSD hx,pair_le_radius S delta hx hc⟩
  have hcap : (S.card:ℝ) ≤ K*(radius S delta)^u*D.card :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (hprofile c (radius S delta) hcutoff hr1)
  have hmass := original_retained_mass D S hdelta hkappa hB hmax
  have hm := mul_le_mul_of_nonneg_left hcap (Real.rpow_nonneg hBp.le kappa)
  have hsmall : (radius S delta)^kappa ≤ K*B^kappa*(radius S delta)^u := by
    apply (mul_le_mul_iff_left₀ hN).mp
    nlinarith only [hmass,hm]
  have hid : (radius S delta)^kappa*(radius S delta)^(u-kappa)=(radius S delta)^u := by
    rw [← Real.rpow_add hR]
    have he : kappa+(u-kappa)=u := by ring
    rw [he]
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hR kappa)).mp
  calc
    _ ≤ K*B^kappa*(radius S delta)^u := by simpa only [one_mul] using hsmall
    _ = K*B^kappa*((radius S delta)^kappa*(radius S delta)^(u-kappa)) :=
      congrArg (fun z : ℝ => K*B^kappa*z) hid.symm
    _ = _ := by ring

/-- A full original profile reaches the selected radius automatically,
since the selected radius was defined to be at least the original mesh. -/
theorem original_full_profile_radius (D S : Finset ℝ)
    {delta kappa B K u : ℝ} (hdelta : 0 < delta) (hkappa : 0 ≤ kappa)
    (hS : S.Nonempty) (hSD : S⊆D) (hB : radius D delta ≤ B)
    (hmax : ∀ T : Finset ℝ, T⊆D →
      (T.card:ℝ)/(radius T delta)^kappa ≤ (S.card:ℝ)/(radius S delta)^kappa)
    (hr1 : radius S delta ≤ 1) (hprofile : ScalarFrostman D delta K u) :
    1 ≤ K*B^kappa*(radius S delta)^(u-kappa) := by
  exact original_available_profile_radius D S hdelta hkappa hS hSD hB hmax
    (mesh_le_radius S delta) hr1 hprofile

end OriginalCoefficientProfileRadius
