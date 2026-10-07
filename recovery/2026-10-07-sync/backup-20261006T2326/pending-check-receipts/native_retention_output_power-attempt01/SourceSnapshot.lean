import Theorems.Thm_StickyKakeya4_native_effective_output_threshold

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeRetentionOutputPower
open NativeQuarterScaleParameters

/-- The actual configured base is chosen below twice the original error
envelope. At its output tube width Delta=base/64, the reference radius
is at least Delta squared. No new source-dependent threshold is chosen. -/
theorem configured_square_le_reference {rho Delta epsilon : ℝ}
    (hr : 0 < rho) (hr1 : rho ≤ 1) (hD : 0 ≤ Delta)
    (he : 0 ≤ epsilon) (he4 : epsilon ≤ 1/4)
    (hbase : 64*Delta ≤ 2*max ((5/4:ℝ)*rho^(1-2*epsilon)) rho) :
    Delta^2 ≤ rho := by
  have hp : rho^(1-2*epsilon) ≤ Real.sqrt rho := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith only [he4])
  have hrp : rho ≤ Real.sqrt rho := by
    rw [Real.sqrt_eq_rpow]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hr hr1
      (show (1/2:ℝ) ≤ 1 by norm_num)
  have hs : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have hmax : max ((5/4:ℝ)*rho^(1-2*epsilon)) rho ≤ (5/4:ℝ)*Real.sqrt rho :=
    max_le (mul_le_mul_of_nonneg_left hp (by norm_num)) (by nlinarith only [hrp,hs])
  have hds : Delta ≤ Real.sqrt rho := by nlinarith only [hbase,hmax,hs]
  have hsq := mul_self_le_mul_self hD hds
  simpa only [←sq,Real.sq_sqrt hr.le] using hsq

/-- The literal middle-scale square bound now gives a fourth-power lower
bound for the original stop scale in terms of the eventual output scale. -/
theorem output_fourth_le_stop {rho Delta r : ℝ}
    (hrho : 0 ≤ rho) (hshape : Delta^2 ≤ rho) (hstop : rho^2 ≤ 6144*r) :
    Delta^4 ≤ 6144*r := by
  have hh := mul_self_le_mul_self (sq_nonneg Delta) hshape
  nlinarith only [hh,hstop]

theorem reference_loss_to_output {rho Delta A : ℝ}
    (hD : 0 < Delta) (hA : 0 ≤ A) (hshape : Delta^2 ≤ rho) :
    rho^(-A) ≤ Delta^(-(2*A)) := by
  have hh := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hD) hshape (neg_nonpos.mpr hA)
  have heq : (Delta^2)^(-A)=Delta^(-(2*A)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hD.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  exact hh.trans_eq heq

/-- Bounding nu by one makes the constant uniform over every later loss
exponent, as required when choosing the initial source cutoff. -/
theorem stop_loss_to_output {r Delta nu : ℝ}
    (hD : 0 < Delta) (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1)
    (hstop : Delta^4 ≤ 6144*r) :
    r^(-nu) ≤ 6144*Delta^(-(4*nu)) := by
  have hlo : Delta^4/6144 ≤ r := by linarith only [hstop]
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < Delta^4/6144)
    hlo (neg_nonpos.mpr hnu)
  have heq : (Delta^4/6144)^(-nu)=(6144:ℝ)^nu*Delta^(-(4*nu)) := by
    rw [Real.div_rpow (by positivity) (by norm_num),←Real.rpow_natCast,
      ←Real.rpow_mul hD.le,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 6144),div_inv_eq_mul]
    norm_num only [Nat.cast_ofNat]
    have he : (4:ℝ)*(-nu)=-(4*nu) := by ring
    rw [he,mul_comm]
  rw [heq] at hh
  have hC : (6144:ℝ)^nu ≤ 6144 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 6144) hnu1
  exact hh.trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hD.le _))

/-- The input is the actual unnormalized retention payment after source
cuts. All powers are transported to the same output Delta. -/
theorem total_retention_at_output {F C r rho Delta nu A zeta : ℝ}
    (hC : 0 ≤ C) (hD : 0 < Delta) (hrho : 0 ≤ rho)
    (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1) (hA : 0 ≤ A)
    (hshape : Delta^2 ≤ rho) (hstop : rho^2 ≤ 6144*r)
    (hF : F ≤ C*r^(-nu)*rho^(-A)*Delta^(-zeta)) :
    F ≤ (6144*C)*Delta^(-(4*nu+2*A+zeta)) := by
  have h4 := output_fourth_le_stop hrho hshape hstop
  have hnew := stop_loss_to_output hD hnu hnu1 h4
  have hold := reference_loss_to_output hD hA hshape
  apply hF.trans
  calc
    C*r^(-nu)*rho^(-A)*Delta^(-zeta) ≤
        C*(6144*Delta^(-(4*nu)))*Delta^(-(2*A))*Delta^(-zeta) := by
      gcongr
    _ = (6144*C)*(Delta^(-(4*nu))*Delta^(-(2*A))*Delta^(-zeta)) := by ring
    _ = _ := by
      rw [←Real.rpow_add hD,←Real.rpow_add hD]
      congr 2
      ring

/-- A fixed coefficient is absorbed once, before all source objects and
allowed output scales. The margin e/64 is retained for later costs. -/
theorem exists_uniform_retention_cutoff (e C : ℝ) (he : 0 < e) (hC : 0 < C) :
    ∃D0 : ℝ,0 < D0 ∧ D0 ≤ 1 ∧ ∀Delta F p : ℝ,
      0 < Delta → Delta ≤ D0 → p ≤ e/64 →
      F ≤ C*Delta^(-p) → F ≤ Delta^(-(e/32)) := by
  obtain ⟨D0,hD0,hD01,H⟩ := exists_small_power_cutoff
    (show 0 < e/64 by positivity) (show 0 < 1/C by positivity)
  refine ⟨D0,hD0,hD01,?_⟩
  intro Delta F p hD hsmall hp hF
  have hD1 := hsmall.trans hD01
  have hpay : C*Delta^(e/64) ≤ 1 := by
    have hh := (le_div_iff₀ hC).mp (H Delta hD hsmall)
    simpa only [mul_comm] using hh
  have hcp : C ≤ Delta^(-(e/64)) := by
    have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hD (e/64))).mpr hpay
    simpa only [one_div,Real.rpow_neg hD.le] using hh
  calc
    F ≤ C*Delta^(-p) := hF
    _ ≤ Delta^(-(e/64))*Delta^(-(e/64)) := by
      exact mul_le_mul hcp
        (Real.rpow_le_rpow_of_exponent_ge hD hD1 (neg_le_neg hp))
        (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg hD.le _)
    _ = Delta^(-(e/32)) := by
      rw [←Real.rpow_add hD]
      congr 1
      ring

end NativeRetentionOutputPower
