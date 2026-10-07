import Theorems.Thm_StickyKakeya4_native_alignment_tau_range

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeAlignmentParentWidth
open NativeAlignmentTauRange

/-- Any FIXED geometric factor is paid before the planar input. The
strong conclusion is factor*rho<=tau, not merely factor*deltaY<=tau. -/
theorem exists_factor_gap_cutoff (chi factor : ℝ) (hchi : 0 < chi) (hfactor : 0 < factor) :
    ∃delta0 : ℝ,0 < delta0 ∧
      ∀deltaY rho tau : ℝ,0 < deltaY → deltaY ≤ delta0 → deltaY ≤ rho →
        deltaY^(-chi) ≤ tau/rho → factor*rho ≤ tau ∧ factor*deltaY ≤ tau := by
  refine ⟨(factor⁻¹)^(chi⁻¹),Real.rpow_pos_of_pos (inv_pos.mpr hfactor) _,?_⟩
  intro deltaY rho tau hd hsmall hdr hgap
  have hp : deltaY^chi ≤ factor⁻¹ :=
    (Real.rpow_le_rpow hd.le hsmall hchi.le).trans_eq
      (Real.rpow_inv_rpow (inv_nonneg.mpr hfactor.le) hchi.ne')
  have hf : factor ≤ deltaY^(-chi) := by
    rw [Real.rpow_neg hd.le,←one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hd chi)).mpr
    have hh := mul_le_mul_of_nonneg_left hp hfactor.le
    simpa only [mul_inv_cancel₀ hfactor.ne'] using hh
  have ht := (le_div_iff₀ (hd.trans_le hdr)).mp (hf.trans hgap)
  exact ⟨ht,(mul_le_mul_of_nonneg_left hdr hfactor.le).trans ht⟩

/-- Shrinking the physical parent by64 leaves the actual planar tau
untouched. The512 gap makes its dyadic depth legal even at the fine end. -/
theorem parent_dyadic_depth (u j : ℕ) (tau : ℝ)
    (htau : tau=((2:ℝ)⁻¹^u/512)*(2:ℝ)^j)
    (hlower : 512*((2:ℝ)⁻¹^u/512) ≤ tau) (hupper : tau ≤ 1) :
    9 ≤ j ∧ tau/64=((2:ℝ)⁻¹^u/512)*(2:ℝ)^(j-6) ∧
      ∃b : ℕ,12 ≤ b ∧ b ≤ u+12 ∧ tau/64=64/((2^b:ℕ):ℝ) := by
  have hd : 0 < (2:ℝ)⁻¹^u/512 := by positivity
  have hp : (512:ℝ) ≤ (2:ℝ)^j := by
    rw [htau] at hlower
    exact (mul_le_mul_iff_right₀ hd).mp (by simpa only [mul_comm] using hlower)
  have hj : 9 ≤ j :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp (by exact_mod_cast hp)
  have he : tau/64=((2:ℝ)⁻¹^u/512)*(2:ℝ)^(j-6) := by
    rw [htau,show j=(j-6)+6 by omega,pow_add]
    norm_num
    ring
  have hlo : (2:ℝ)⁻¹^u/64 ≤ tau/64 := by
    have hh := div_le_div_of_nonneg_right hlower (by norm_num : (0:ℝ) ≤ 64)
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (512:ℝ)≠0)] using hh
  have hhi : tau/64 ≤ 1/64 := div_le_div_of_nonneg_right hupper (by norm_num)
  obtain ⟨_hj,_hjup,_hb,hbu,hbe⟩ :=
    phase_depth u (j-6) (tau/64) he hlo (hhi.trans (by norm_num))
  let b := u+15-(j-6)
  have hprod : (tau/64)*(2:ℝ)^b=64 := by
    rw [hbe,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  have hb : 12 ≤ b := by
    have hh := mul_le_mul_of_nonneg_right hhi (by positivity : (0:ℝ) ≤ (2:ℝ)^b)
    rw [hprod] at hh
    have hpow : (2:ℝ)^12 ≤ (2:ℝ)^b := by norm_num; linarith only [hh]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp (by exact_mod_cast hpow)
  exact ⟨hj,he,b,hb,hbu,hbe⟩

/-- Complete pre-source cutoff for the proposed64 parent factor. It
keeps8rho<=parentWidth, DeltaOut<=parentWidth, and exact phase readback. -/
theorem exists_actual_parent_cutoff (chi : ℝ) (hchi : 0 < chi) :
    ∃delta0 : ℝ,0 < delta0 ∧ ∀(u j : ℕ) (rho tau : ℝ),
      (2:ℝ)⁻¹^u/512 ≤ delta0 → (2:ℝ)⁻¹^u/512 ≤ rho →
      ((2:ℝ)⁻¹^u/512)^(-chi) ≤ tau/rho → tau ≤ 1 →
      tau=((2:ℝ)⁻¹^u/512)*(2:ℝ)^j →
      8*rho ≤ tau/64 ∧ (2:ℝ)⁻¹^u/64 ≤ tau/64 ∧ tau/64 ≤ 1/64 ∧
      9 ≤ j ∧ tau/64=((2:ℝ)⁻¹^u/512)*(2:ℝ)^(j-6) ∧
      ∃b : ℕ,12 ≤ b ∧ b ≤ u+12 ∧ tau/64=64/((2^b:ℕ):ℝ) := by
  obtain ⟨delta0,hd0,H⟩ := exists_factor_gap_cutoff chi 512 hchi (by norm_num)
  refine ⟨delta0,hd0,?_⟩
  intro u j rho tau hsmall hdr hgap hupper htau
  have hg := H ((2:ℝ)⁻¹^u/512) rho tau (by positivity) hsmall hdr hgap
  have hparent := parent_dyadic_depth u j tau htau hg.2 hupper
  refine ⟨?_,?_,div_le_div_of_nonneg_right hupper (by norm_num),hparent⟩
  · linarith only [hg.1]
  · linarith only [hg.2]

end NativeAlignmentParentWidth
