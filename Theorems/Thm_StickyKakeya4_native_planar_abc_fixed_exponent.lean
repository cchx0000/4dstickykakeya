import Theorems.Thm_StickyKakeya4_native_planar_abc_input
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
namespace NativePlanarABCFixedExponent
open Classical NativePlanarABCInput FiniteVoronoiPopulation
/-- The actual nonempty unit-box C population forces its relative angular
 constant to be at least one. This is not an additional source premise. -/
theorem actual_angular_constant_ge_one
    {mesh exponent ballK angularK density lineWidth lineFraction coverK : ℝ}
    (data : Data mesh exponent ballK angularK density lineWidth lineFraction coverK)
    (hm1 : mesh ≤ 1) : 1 ≤ angularK := by
  have hball : carrierBall data.C 0 1=data.C := by
    apply Finset.filter_eq_self.mpr
    intro c hc
    simpa only [Real.dist_eq,sub_zero] using data.boxC c hc
  have hc := data.frostmanC 0 1 hm1
  rw [hball,Real.one_rpow,mul_one] at hc
  have hcard : (0:ℝ)<data.C.card := Nat.cast_pos.mpr data.nonemptyC.card_pos
  nlinarith only [hc,hcard]
/-- Weaken only the upper angular exponent on the ACTUAL constructed data.
 The sets, graph, density, line exclusion, and output cover are unchanged. -/
theorem exists_fixed_exponent_data
    {mesh exponent fixedExponent ballK angularK density lineWidth lineFraction coverK : ℝ}
    (data : Data mesh exponent ballK angularK density lineWidth lineFraction coverK)
    (hm : 0 < mesh) (hm1 : mesh ≤ 1) (hfixed : 0 ≤ fixedExponent)
    (hexponent : fixedExponent ≤ exponent) :
    ∃ fixed : Data mesh fixedExponent ballK angularK density lineWidth lineFraction coverK,
      fixed.A=data.A ∧ fixed.B=data.B ∧ fixed.C=data.C ∧ fixed.G=data.G := by
  have hK := actual_angular_constant_ge_one data hm1
  have hFrostman : ∀ center R : ℝ, mesh ≤ R →
      ((carrierBall data.C center R).card : ℝ) ≤ angularK*R^fixedExponent*(data.C.card:ℝ) := by
    intro center R hR
    have hR0 : 0 < R := hm.trans_le hR
    by_cases hR1 : R ≤ 1
    · exact OriginalAngularBalancedFrostman.weaken_upper_exponent (Nat.cast_nonneg _)
        (le_trans (by norm_num) hK) hR0 hR1 hexponent (data.frostmanC center R hR)
    · have hRP : 1 ≤ R^fixedExponent := Real.one_le_rpow (le_of_lt (lt_of_not_ge hR1)) hfixed
      have hKP : 1 ≤ angularK*R^fixedExponent := by
        have hh := mul_le_mul_of_nonneg_left hRP (le_trans (by norm_num) hK)
        rw [mul_one] at hh
        exact hK.trans hh
      have hc : ((carrierBall data.C center R).card : ℝ) ≤ (data.C.card:ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun c : ℝ => dist c center ≤ R) data.C)
      exact hc.trans (by nlinarith only [mul_le_mul_of_nonneg_right hKP (Nat.cast_nonneg data.C.card)])
  let fixed : Data mesh fixedExponent ballK angularK density lineWidth lineFraction coverK := {
    A := data.A, B := data.B, C := data.C, G := data.G,
    nonemptyA := data.nonemptyA, nonemptyB := data.nonemptyB, nonemptyC := data.nonemptyC,
    graph_subset := data.graph_subset, boxA := data.boxA, boxB := data.boxB, boxC := data.boxC,
    separatedA := data.separatedA, separatedB := data.separatedB, separatedC := data.separatedC,
    ballB := data.ballB, lineB := data.lineB, frostmanC := hFrostman,
    graph_density := data.graph_density, output_cover := data.output_cover }
  exact ⟨fixed,rfl,rfl,rfl,rfl⟩
/-- In the nontrivial branch, analytic constants can be chosen using the
 fixed positive exponent zeta/2 while the original C cardinality is exact. -/
theorem exists_zeta_exponent_data
    {mesh exponent zeta ballK angularK density lineWidth lineFraction coverK : ℝ}
    (data : Data mesh exponent ballK angularK density lineWidth lineFraction coverK)
    (hm : 0 < mesh) (hm1 : mesh ≤ 1) (hz : 0 < zeta) (hbranch : zeta < exponent) :
    ∃ fixed : Data mesh (zeta/2) ballK angularK density lineWidth lineFraction coverK,
      fixed.A=data.A ∧ fixed.B=data.B ∧ fixed.C=data.C ∧ fixed.G=data.G := by
  exact exists_fixed_exponent_data data hm hm1 (by positivity) (by linarith)
end NativePlanarABCFixedExponent
