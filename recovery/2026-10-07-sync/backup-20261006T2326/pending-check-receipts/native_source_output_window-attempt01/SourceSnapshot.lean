import Theorems.Thm_StickyKakeya4_native_retention_output_power

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
noncomputable section
namespace NativeSourceOutputWindow
open NativeQuarterScaleParameters NativeRetentionOutputPower

/-- A source cutoff, fixed before the datum and its selected rank, supplies
the power window used by output-scale admission. The middle radius is the
literal 64/2^m and the base error envelope is unchanged. -/
theorem exists_uniform_source_window (amin : ℝ) (ha : 0 < amin) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀delta r power : ℝ,0 < delta → delta ≤ delta0 → amin ≤ power → r ≤ delta^power →
      ∀m : ℕ,((64:ℝ)/((2^m:ℕ):ℝ)) ≤ 1 →
        ((64:ℝ)/((2^m:ℕ):ℝ))^2 ≤ 6144*r →
      ∀epsilon Delta : ℝ,0 ≤ epsilon → epsilon ≤ 1/4 → 0 ≤ Delta →
        64*Delta ≤ 2*max ((5/4:ℝ)*((64:ℝ)/((2^m:ℕ):ℝ))^(1-2*epsilon))
          ((64:ℝ)/((2^m:ℕ):ℝ)) →
        Delta ≤ delta^(amin/8) := by
  obtain ⟨delta0,hd0,hd01,H⟩ := exists_small_power_cutoff
    (show 0 < amin/2 by positivity) (by norm_num : (0:ℝ) < 1/6144)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta r power hd hsmall hpower hr m hrho1 hstop epsilon Delta he he4 hD hbase
  let rho : ℝ := 64/((2^m:ℕ):ℝ)
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hshape : Delta^2 ≤ rho := configured_square_le_reference hrho hrho1 hD he he4 hbase
  have hfour := output_fourth_le_stop hrho.le hshape hstop
  have hdp : delta^power ≤ delta^amin :=
    Real.rpow_le_rpow_of_exponent_ge hd (hsmall.trans hd01) hpower
  have hpay : (6144:ℝ)*delta^(amin/2) ≤ 1 := by
    have hh := H delta hd hsmall
    nlinarith only [hh]
  have heq : delta^(amin/2)*delta^(amin/2)=delta^amin := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  have hfourUpper : Delta^4 ≤ delta^(amin/2) := by
    calc
      Delta^4 ≤ 6144*r := hfour
      _ ≤ 6144*delta^amin := by nlinarith only [hr,hdp]
      _ = (6144*delta^(amin/2))*delta^(amin/2) := by rw [mul_assoc,heq]
      _ ≤ delta^(amin/2) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hpay (Real.rpow_nonneg hd.le _)
  have hroot : (delta^(amin/8))^4=delta^(amin/2) := by
    rw [←Real.rpow_mul_natCast hd.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  rw [←hroot] at hfourUpper
  have hsquares : (Delta^2)^2 ≤ ((delta^(amin/8))^2)^2 := by
    convert hfourUpper using 1 <;> ring
  have hs := (sq_le_sq₀ (sq_nonneg Delta) (sq_nonneg (delta^(amin/8)))).mp hsquares
  exact (sq_le_sq₀ hD (Real.rpow_nonneg hd.le _)).mp hs

end NativeSourceOutputWindow
