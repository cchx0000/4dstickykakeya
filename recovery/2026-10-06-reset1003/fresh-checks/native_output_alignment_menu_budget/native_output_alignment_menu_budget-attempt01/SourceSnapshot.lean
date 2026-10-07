import Theorems.Thm_StickyKakeya4_native_coarse_mass_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeOutputAlignmentMenuBudget
open NativeOriginalLogBudget NativeDyadicPruningCutoff NativeQuarterScaleParameters

/-- The actual two dyadic scales, two orientations and fixed exponent-bin
menu cost only an arbitrarily small output power. The cutoff precedes u and
the source. The output scale is literally 2^(-u-6), not the old fine mesh. -/
theorem exists_menu_cutoff (loss : ℝ) (hloss : 0 < loss) (Ns : ℕ) :
    ∃D0 : ℝ,0 < D0 ∧ D0 ≤ 1 ∧ ∀u : ℕ,
      (2:ℝ)⁻¹^(u+6) ≤ D0 →
      (2:ℝ)*((u:ℝ)+10)^2*((Ns:ℝ)+1) ≤ ((2:ℝ)⁻¹^(u+6))^(-loss) := by
  have hz : 0 < loss/4 := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨dl,hdl,hdl1,HL⟩ := exists_logarithmic_budget_cutoff hz
    (by norm_num : (0:ℝ) ≤ 4) (show 0 ≤ 1/Real.log 2 by positivity)
  let C : ℝ := 2*((Ns:ℝ)+1)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨dc,hdc,_hdc1,HC⟩ := exists_small_power_cutoff hz (show 0 < 1/C by positivity)
  refine ⟨min dl dc,lt_min hdl hdc,(min_le_left _ _).trans hdl1,?_⟩
  intro u hsmall
  let Delta : ℝ := (2:ℝ)⁻¹^(u+6)
  have hD : 0 < Delta := by dsimp [Delta]; positivity
  have hD1 : Delta ≤ 1 := (hsmall.trans (min_le_left _ _)).trans hdl1
  have hdepth : (u:ℝ)+10 ≤ Delta^(-(loss/4)) := by
    have hh := HL Delta hD (hsmall.trans (min_le_left _ _))
    have hl := dyadic_depth_log (u+6) (show Delta=(2:ℝ)⁻¹^(u+6) from rfl)
    push_cast at hl
    have heq : (u:ℝ)+10=4+(1/Real.log 2)*(-Real.log Delta) := by
      rw [one_div,mul_comm,←div_eq_mul_inv]
      linarith only [hl]
    rwa [←heq] at hh
  have hCp : C ≤ Delta^(-(loss/4)) := by
    have hh := (le_div_iff₀ hC).mp (HC Delta hD (hsmall.trans (min_le_right _ _)))
    have hq : C ≤ 1/Delta^(loss/4) :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hD _)).mpr (by simpa only [mul_comm] using hh)
    simpa only [one_div,Real.rpow_neg hD.le] using hq
  calc
    (2:ℝ)*((u:ℝ)+10)^2*((Ns:ℝ)+1)=C*((u:ℝ)+10)^2 := by dsimp [C]; ring
    _ ≤ Delta^(-(loss/4))*(Delta^(-(loss/4)))^2 := by
      exact mul_le_mul hCp (pow_le_pow_left₀ (by positivity) hdepth 2)
        (sq_nonneg _) (Real.rpow_nonneg hD.le _)
    _ = Delta^(-(3*loss/4)) := by
      rw [←Real.rpow_mul_natCast hD.le,←Real.rpow_add hD]
      norm_num only [Nat.cast_ofNat]
      congr 1
      ring
    _ ≤ Delta^(-loss) := Real.rpow_le_rpow_of_exponent_ge hD hD1 (by linarith only [hloss])

/-- Common-scale selection is charged to the actual chosen fraction, with
deltaY=Delta/8. There is no fixed positive-fraction assumption. -/
theorem inverse_selected_fraction {Delta theta M zeta loss : ℝ}
    (hD : 0 < Delta) (htheta : 0 < theta) (hM : 0 < M)
    (hmenu : M ≤ Delta^(-loss))
    (hret : (Delta/8)^zeta/M ≤ theta) :
    1/theta ≤ (8:ℝ)^zeta*Delta^(-(zeta+loss)) := by
  have hp : 0 < (Delta/8)^zeta := Real.rpow_pos_of_pos (by positivity) _
  have hi : 1/theta ≤ M/(Delta/8)^zeta := by
    have hh := (div_le_iff₀ hM).mp hret
    apply (div_le_div_iff₀ htheta hp).mpr
    simpa only [one_mul,mul_comm] using hh
  apply hi.trans
  calc
    M/(Delta/8)^zeta ≤ Delta^(-loss)/(Delta/8)^zeta := div_le_div_of_nonneg_right hmenu hp.le
    _ = (8:ℝ)^zeta*Delta^(-(zeta+loss)) := by
      rw [Real.div_rpow hD.le (by norm_num),div_div_eq_mul_div,←Real.rpow_sub hD]
      have he : -loss-zeta=-(zeta+loss) := by ring
      rw [he,mul_comm]

end NativeOutputAlignmentMenuBudget
