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

/-- The main fixed parent factor is4096. The exact dyadic width remains
inside the existing interior reader, so no top interpolation is required. -/
theorem parent_4096_depth (u j : ℕ) (tau : ℝ)
    (htau : tau=((2:ℝ)⁻¹^u/512)*(2:ℝ)^j)
    (hlower : 32768*((2:ℝ)⁻¹^u/512) ≤ tau) (hupper : tau ≤ 1) :
    15 ≤ j ∧ j ≤ u+9 ∧ tau/4096=((2:ℝ)⁻¹^u/512)*(2:ℝ)^(j-12) ∧
      ∃s : ℕ,9 ≤ s ∧ s ≤ u+3 ∧ tau/4096=(64/((2^s:ℕ):ℝ))/512 := by
  have hd : 0 < (2:ℝ)⁻¹^u/512 := by positivity
  have hp : (32768:ℝ) ≤ (2:ℝ)^j := by
    rw [htau] at hlower
    exact (mul_le_mul_iff_right₀ hd).mp (by simpa only [mul_comm] using hlower)
  have hj : 15 ≤ j :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp (by exact_mod_cast hp)
  have hOriginalLower : (2:ℝ)⁻¹^u/64 ≤ tau := by nlinarith only [hlower,hd]
  have hjup := (phase_depth u j tau htau hOriginalLower hupper).2.1
  have he : tau/4096=((2:ℝ)⁻¹^u/512)*(2:ℝ)^(j-12) := by
    have hpow : (2:ℝ)^j=(2:ℝ)^(j-12)*4096 := by
      calc
        _ = (2:ℝ)^((j-12)+12) := by congr 1; omega
        _ = _ := by rw [pow_add]; norm_num
    rw [htau,hpow]
    ring
  have hlo : (2:ℝ)⁻¹^u/64 ≤ tau/4096 := by linarith only [hlower]
  have hhi : tau/4096 ≤ 1/4096 := div_le_div_of_nonneg_right hupper (by norm_num)
  obtain ⟨s,_hs,hsu,hsread,_hphase⟩ :=
    interior_depth u (j-12) (tau/4096) he hlo (hhi.trans (by norm_num))
  have hprod : (tau/4096)*(2:ℝ)^s=1/8 := by
    rw [hsread,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
    norm_num
  have hs : 9 ≤ s := by
    have hh := mul_le_mul_of_nonneg_right hhi (by positivity : (0:ℝ) ≤ (2:ℝ)^s)
    rw [hprod] at hh
    have hpow : (2:ℝ)^9 ≤ (2:ℝ)^s := by norm_num; linarith only [hh]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp (by exact_mod_cast hpow)
  exact ⟨hj,hjup,he,s,hs,hsu,hsread⟩

/-- The cutoff is chosen from chi before u or the input source. The
unchanged planar tau uses a4096-smaller actual parent, with room for the
existing8rho tube scale and every already proved interior query guard. -/
theorem exists_actual_parent_cutoff (chi : ℝ) (hchi : 0 < chi) :
    ∃delta0 : ℝ,0 < delta0 ∧ ∀(u j : ℕ) (rho tau : ℝ),
      (2:ℝ)⁻¹^u/512 ≤ delta0 → (2:ℝ)⁻¹^u/512 ≤ rho →
      ((2:ℝ)⁻¹^u/512)^(-chi) ≤ tau/rho → tau ≤ 1 →
      tau=((2:ℝ)⁻¹^u/512)*(2:ℝ)^j →
      8*rho ≤ tau/4096 ∧ (2:ℝ)⁻¹^u/64 ≤ tau/4096 ∧ tau/4096 ≤ 1/4096 ∧
      15 ≤ j ∧ j ≤ u+9 ∧ tau/4096=((2:ℝ)⁻¹^u/512)*(2:ℝ)^(j-12) ∧
      ∃s : ℕ,9 ≤ s ∧ s ≤ u+3 ∧ tau/4096=(64/((2^s:ℕ):ℝ))/512 := by
  obtain ⟨delta0,hd0,H⟩ := exists_factor_gap_cutoff chi 32768 hchi (by norm_num)
  refine ⟨delta0,hd0,?_⟩
  intro u j rho tau hsmall hdr hgap hupper htau
  have hg := H ((2:ℝ)⁻¹^u/512) rho tau (by positivity) hsmall hdr hgap
  have hparent := parent_4096_depth u j tau htau hg.2 hupper
  refine ⟨?_,?_,div_le_div_of_nonneg_right hupper (by norm_num),hparent⟩
  · linarith only [hg.1]
  · linarith only [hg.2]

end NativeAlignmentParentWidth
