/- Exact dyadic range of Lemma5.3's unchanged tau at the actual final base. -/
import Theorems.Thm_StickyKakeya4_native_configured_dyadic_matching

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeAlignmentTauRange

/-- This cutoff precedes the planar input. The gap in Lemma5.3 then
places tau above the ACTUAL tube thickness8deltaY, with no scale rounding. -/
theorem exists_gap_cutoff (chi : ℝ) (hchi : 0 < chi) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ deltaY rho tau : ℝ, 0 < deltaY → deltaY ≤ delta0 →
        deltaY ≤ rho → deltaY^(-chi) ≤ tau/rho → 8*deltaY ≤ tau := by
  refine ⟨(1/8:ℝ)^(chi⁻¹),Real.rpow_pos_of_pos (by norm_num) _,?_⟩
  intro deltaY rho tau hd hsmall hdr hgap
  have hpow : deltaY^chi ≤ (1/8:ℝ) :=
    (Real.rpow_le_rpow hd.le hsmall hchi.le).trans_eq
      (Real.rpow_inv_rpow (by norm_num : (0:ℝ) ≤ 1/8) hchi.ne')
  have h8 : (8:ℝ) ≤ deltaY^(-chi) := by
    rw [Real.rpow_neg hd.le,←one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hd chi)).mpr
    linarith only [hpow]
  have hrho : 0 < rho := hd.trans_le hdr
  have ht := (le_div_iff₀ hrho).mp (h8.trans hgap)
  linarith only [ht,hdr]

lemma input_mesh_product (u : ℕ) :
    ((2:ℝ)⁻¹^u/512)*(2:ℝ)^(u+9)=1 := by
  rw [inv_pow,pow_add]
  norm_num
  field_simp

/-- The literal dyadic tau yields an exact relative phase depth. The
top endpoint remains6, so no false depth>=15 requirement is introduced. -/
theorem phase_depth (u j : ℕ) (tau : ℝ)
    (htau : tau=((2:ℝ)⁻¹^u/512)*(2:ℝ)^j)
    (hlower : (2:ℝ)⁻¹^u/64 ≤ tau) (hupper : tau ≤ 1) :
    3 ≤ j ∧ j ≤ u+9 ∧ 6 ≤ u+15-j ∧ u+15-j ≤ u+12 ∧
      tau=64/((2^(u+15-j):ℕ):ℝ) := by
  have hd : 0 < (2:ℝ)⁻¹^u/512 := by positivity
  have hbase : (2:ℝ)⁻¹^u/64=8*((2:ℝ)⁻¹^u/512) := by ring
  have hp : (8:ℝ) ≤ (2:ℝ)^j := by
    rw [hbase,htau] at hlower
    exact (mul_le_mul_iff_right₀ hd).mp (by simpa only [mul_comm] using hlower)
  have hj : 3 ≤ j :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp (by exact_mod_cast hp)
  have hprod : tau*(2:ℝ)^(u+9)=(2:ℝ)^j := by
    rw [htau]
    calc
      _ = (((2:ℝ)⁻¹^u/512)*(2:ℝ)^(u+9))*(2:ℝ)^j := by ring
      _ = _ := by rw [input_mesh_product,one_mul]
  have hjup : j ≤ u+9 := by
    have hh := mul_le_mul_of_nonneg_right hupper (by positivity : (0:ℝ) ≤ (2:ℝ)^(u+9))
    rw [hprod,one_mul] at hh
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp (by exact_mod_cast hh)
  refine ⟨hj,hjup,by omega,by omega,?_⟩
  apply (eq_div_iff (by positivity : (((2^(u+15-j):ℕ):ℝ)) ≠ 0)).mpr
  rw [Nat.cast_pow,Nat.cast_ofNat,htau]
  calc
    _ = ((2:ℝ)⁻¹^u/512)*((2:ℝ)^j*(2:ℝ)^(u+15-j)) := by ring
    _ = ((2:ℝ)⁻¹^u/512)*(2:ℝ)^(u+15) := by
      rw [←pow_add,show j+(u+15-j)=u+15 by omega]
    _ = (((2:ℝ)⁻¹^u/512)*(2:ℝ)^(u+9))*(2:ℝ)^6 := by
      rw [show u+15=(u+9)+6 by omega,pow_add]
      ring
    _ = 64 := by rw [input_mesh_product]; norm_num

/-- Interior tau is exactly one admissible current joint depth, derived
from the actual dyadic output and the gap cutoff, rather than assumed. -/
theorem interior_depth (u j : ℕ) (tau : ℝ)
    (htau : tau=((2:ℝ)⁻¹^u/512)*(2:ℝ)^j)
    (hlower : (2:ℝ)⁻¹^u/64 ≤ tau) (hupper : tau ≤ 1/512) :
    ∃s : ℕ,6 ≤ s ∧ s ≤ u+3 ∧
      tau=(64/((2^s:ℕ):ℝ))/512 ∧ u+15-j=s+9 := by
  obtain ⟨_hj,hjup,hb,hbu,he⟩ := phase_depth u j tau htau hlower (hupper.trans (by norm_num))
  have hprod : tau*(2:ℝ)^(u+15-j)=64 := by
    rw [he,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  have h15 : 15 ≤ u+15-j := by
    have hh := mul_le_mul_of_nonneg_right hupper
      (by positivity : (0:ℝ) ≤ (2:ℝ)^(u+15-j))
    rw [hprod] at hh
    have hp : (2:ℝ)^15 ≤ (2:ℝ)^(u+15-j) := by norm_num; linarith only [hh]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp (by exact_mod_cast hp)
  let s := u+15-j-9
  have hs : u+15-j=s+9 := by dsimp only [s]; omega
  refine ⟨s,by dsimp only [s]; omega,by dsimp only [s]; omega,?_,hs⟩
  rw [he,hs,Nat.cast_pow,Nat.cast_ofNat,pow_add]
  norm_num
  field_simp

/-- The fixed top interval uses the exact coarser phase depth6..15.
Its spatial cover may use the fixed depth6 independently. Tau is unchanged. -/
theorem top_depth (u j : ℕ) (tau : ℝ)
    (htau : tau=((2:ℝ)⁻¹^u/512)*(2:ℝ)^j)
    (hlower : (2:ℝ)⁻¹^u/64 ≤ tau) (hbottom : 1/512 ≤ tau) (hupper : tau ≤ 1) :
    ∃b : ℕ,6 ≤ b ∧ b ≤ 15 ∧ b ≤ u+12 ∧ tau=64/((2^b:ℕ):ℝ) := by
  obtain ⟨_hj,_hjup,hb,hbu,he⟩ := phase_depth u j tau htau hlower hupper
  have hprod : tau*(2:ℝ)^(u+15-j)=64 := by
    rw [he,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  have h15 : u+15-j ≤ 15 := by
    have hh := mul_le_mul_of_nonneg_right hbottom
      (by positivity : (0:ℝ) ≤ (2:ℝ)^(u+15-j))
    rw [hprod] at hh
    have hp : (2:ℝ)^(u+15-j) ≤ (2:ℝ)^15 := by norm_num; linarith only [hh]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp (by exact_mod_cast hp)
  exact ⟨u+15-j,hb,h15,hbu,he⟩

end NativeAlignmentTauRange
