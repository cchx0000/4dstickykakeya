import Theorems.Thm_StickyKakeya4_native_pruned_power_constants
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NativePaddedSourcePowerBudget
open StickyKakeya4
open scoped ENNReal

/-- Every actual fixed cost in the source construction fits in one explicit
constant, including density, CW, source retention, and the scale change. -/
lemma fixed_cost_bounds :
    (2048:ℝ)^3 ≤ 2^64 ∧ (10077696:ℝ) ≤ 2^64 ∧
    (512*175616*64^4:ℝ) ≤ 2^64 ∧ (373248*512^4:ℝ) ≤ 2^64 ∧
    (4*373248*175616*64^4:ℝ) ≤ 2^64 ∧ (373248:ℝ) ≤ 2^64 ∧
    (625*64^3:ℝ) ≤ 2^64 := by norm_num

/-- One genuine scale cutoff absorbs all fixed costs before a source is chosen. -/
theorem exists_master_cutoff {e : ℝ} (he : 0 < e) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/8 ∧
      ∀delta : ℝ,0 < delta → delta ≤ delta0 → (2:ℝ)^64*delta^(e/2) ≤ 1 := by
  obtain ⟨d,hd,_hd1,hb⟩ := exists_positive_rpow_absorption_threshold
    (half_pos he) (show (0:ℝ) ≤ (2:ℝ)^64 by positivity) (show (0:ℝ) < 1 by norm_num)
  refine ⟨min d (1/8),lt_min hd (by norm_num),min_le_right _ _,?_⟩
  intro delta hdelta hsmall
  exact hb delta hdelta (hsmall.trans (min_le_left _ _))

lemma cost_of_master {delta e g C : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hmaster : (2:ℝ)^64*delta^(e/2) ≤ 1) (hC : C ≤ (2:ℝ)^64) (hg : e/2 ≤ g) :
    C*delta^g ≤ 1 := by
  exact (mul_le_mul_of_nonneg_right hC (Real.rpow_pos_of_pos hd _).le).trans
    ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hd hd1 hg)
      (by positivity : (0:ℝ) ≤ (2:ℝ)^64)).trans hmaster)

lemma positive_power_ratio {delta e zeta C : ℝ} (hd : 0 < delta) (he : 0 ≤ e) (hC : 0 < C)
    (hbudget : C*delta^(e-zeta) ≤ 1) : (delta/64)^e ≤ delta^zeta/C := by
  have hp : C*delta^e ≤ delta^zeta := by
    calc
      _ = (C*delta^(e-zeta))*delta^zeta := by
        rw [mul_assoc,←Real.rpow_add hd,sub_add_cancel]
      _ ≤ 1*delta^zeta := mul_le_mul_of_nonneg_right hbudget (Real.rpow_pos_of_pos hd _).le
      _ = _ := one_mul _
  have hs : (delta/64)^e ≤ delta^e := Real.rpow_le_rpow (by positivity) (by linarith) he
  exact hs.trans ((le_div_iff₀ hC).mpr (by simpa only [mul_comm] using hp))

lemma old_exponent_coefficient {delta t e : ℝ} (hd : 0 < delta) (C : ℕ)
    (hbudget : (C:ℝ)*delta^(e-t) ≤ 1) :
    (C:ℝ≥0∞)*(ENNReal.ofReal delta).rpow (-t) ≤ (ENNReal.ofReal delta).rpow (-e) := by
  have hp := Real.rpow_pos_of_pos hd e
  have hr : (C:ℝ)*delta^(-t) ≤ delta^(-e) := by
    apply (mul_le_mul_iff_left₀ hp).mp
    have hl : ((C:ℝ)*delta^(-t))*delta^e=(C:ℝ)*delta^(e-t) := by
      rw [mul_assoc,←Real.rpow_add hd]
      congr 2
      ring
    have hu : delta^(-e)*delta^e=1 := by rw [←Real.rpow_add hd]; simp
    rw [hl,hu]
    exact hbudget
  have hh := ENNReal.ofReal_le_ofReal hr
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg C),ENNReal.ofReal_natCast,
    ENNReal.ofReal_rpow_of_pos hd,ENNReal.rpow_eq_pow] using hh

lemma new_exponent_coefficient {delta t e : ℝ} (hd : 0 < delta) (he : 0 ≤ e) (C : ℕ)
    (hbudget : (C:ℝ)*delta^(e-t) ≤ 1) :
    (C:ℝ≥0∞)*(ENNReal.ofReal delta).rpow (-t) ≤ (ENNReal.ofReal (delta/64)).rpow (-e) := by
  have hdp : 0 < delta/64 := by positivity
  have hs : (delta/64)^e ≤ delta^e := Real.rpow_le_rpow hdp.le (by linarith) he
  have hi := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 1 by norm_num) (Real.rpow_pos_of_pos hdp e) hs
  have hr : delta^(-e) ≤ (delta/64)^(-e) := by
    simpa only [Real.rpow_neg hd.le,Real.rpow_neg hdp.le,one_div] using hi
  have hE : (ENNReal.ofReal delta).rpow (-e) ≤ (ENNReal.ofReal (delta/64)).rpow (-e) := by
    simpa only [ENNReal.ofReal_rpow_of_pos hd,ENNReal.ofReal_rpow_of_pos hdp,ENNReal.rpow_eq_pow] using
      ENNReal.ofReal_le_ofReal hr
  exact (old_exponent_coefficient hd C hbudget).trans hE

/-- Apply a fixed loss to actual nonnegative masses, at the original scale. -/
lemma density_power {delta zeta e : ℝ} (hd : 0 < delta) (C : ℕ)
    (hbudget : (C:ℝ)*delta^(e-zeta) ≤ 1) {T M : ℝ≥0∞}
    (hden : (ENNReal.ofReal delta).rpow zeta*T ≤ C*M) :
    (ENNReal.ofReal delta).rpow e*T ≤ M := by
  let d := ENNReal.ofReal delta
  have hd0 : d ≠ 0 := by dsimp [d]; positivity
  have hdT : d ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc : (C:ℝ≥0∞)*d.rpow (e-zeta) ≤ 1 := by
    have hh := ENNReal.ofReal_le_ofReal hbudget
    simpa only [d,ENNReal.rpow_eq_pow,ENNReal.ofReal_mul (Nat.cast_nonneg C),
      ENNReal.ofReal_natCast,ENNReal.ofReal_rpow_of_pos hd,ENNReal.ofReal_one] using hh
  calc
    _ = d.rpow (e-zeta)*(d.rpow zeta*T) := by
      rw [←mul_assoc]
      simp only [ENNReal.rpow_eq_pow]
      rw [←ENNReal.rpow_add _ _ hd0 hdT]
      congr 2
      ring
    _ ≤ d.rpow (e-zeta)*(C*M) := mul_le_mul' le_rfl hden
    _ = ((C:ℝ≥0∞)*d.rpow (e-zeta))*M := by ring
    _ ≤ 1*M := mul_le_mul' hc le_rfl
    _ = _ := one_mul _
end NativePaddedSourcePowerBudget
