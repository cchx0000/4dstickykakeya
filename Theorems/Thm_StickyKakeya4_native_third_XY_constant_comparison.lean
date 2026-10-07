import Theorems.Thm_StickyKakeya4_native_third_XY_data
import Theorems.Thm_StickyKakeya4_native_retained_slice_budget_source

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeThirdXYConstantComparison
open NativeThirdXYData NativeSliceADConstant NativeReferenceColumnExponents
open NativeReferenceSliceBudgetAlgebra NativeRetainedSliceBudgetSource NativeRetainedSliceBudgetAlgebra
open NativeSquaredGrainQueries NativeFixedCompactKakeyaExponent

/-- The coordinate change costs a fixed number, independent of every source
and scale. -/
def geometryCost : ℝ := 512*27*((1201^3:ℕ):ℝ)^2*((201^3:ℕ):ℝ)

lemma geometryCost_one_le : 1 ≤ geometryCost := by norm_num [geometryCost]

lemma constant_grid_comparison {l u B B' s A C : ℝ}
    (hl : 0 < l) (hu : 0 ≤ u) (hA : 1 ≤ A) (hAC : A ≤ C)
    (hB : 0 < B) (hpow : B'^s ≤ 512*B^s) :
    constant (l/A) (C*u) B' s ≤ (512*C)*constant l u B s := by
  have hC : 1 ≤ C := hA.trans hAC
  have hCn : 0 ≤ C := (by norm_num : (0:ℝ)≤1).trans hC
  have hAn : 0 ≤ A := (by norm_num : (0:ℝ)≤1).trans hA
  have hK : 1 ≤ constant l u B s := one_le_constant _ _ _ _
  have hLo : B^s/l ≤ constant l u B s := (le_max_left _ _).trans (le_max_right _ _)
  have hUp : 729*u*B^s ≤ constant l u B s := (le_max_right _ _).trans (le_max_right _ _)
  have hlow : B'^s/(l/A) ≤ (512*C)*constant l u B s := by
    calc
      _ = A*(B'^s/l) := by field_simp
      _ ≤ A*((512*B^s)/l) := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow hl.le) hAn
      _ ≤ C*((512*B^s)/l) := mul_le_mul_of_nonneg_right hAC (by positivity)
      _ = (512*C)*(B^s/l) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLo (by positivity)
  have hupp : 729*(C*u)*B'^s ≤ (512*C)*constant l u B s := by
    calc
      _ ≤ 729*(C*u)*(512*B^s) := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (512*C)*(729*u*B^s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hUp (by positivity)
  have hone : 1 ≤ (512*C)*constant l u B s := by nlinarith only [hC,hK]
  exact max_le hone (max_le hlow hupp)

lemma gap_power_comparison {x s : ℝ} (_hx : 0 ≤ x) (hs : 0 ≤ s) (hs3 : s ≤ 3) :
    (max 64 x)^s ≤ 512*(max 8 x)^s := by
  have hB : 0 < max 8 x := lt_of_lt_of_le (by norm_num : (0:ℝ)<8) (le_max_left _ _)
  have hgap : max 64 x ≤ 8*max 8 x := by
    apply max_le
    · have hh := le_max_left (8:ℝ) x
      linarith only [hh]
    · have h1 := le_max_right (8:ℝ) x
      nlinarith only [h1,hB]
  have hh := Real.rpow_le_rpow (le_trans (by norm_num : (0:ℝ)≤64) (le_max_left _ _)) hgap hs
  rw [Real.mul_rpow (by norm_num) hB.le] at hh
  have h8 : (8:ℝ)^s ≤ 512 := by
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤8) hs3
    norm_num at hp
    exact hp
  exact hh.trans (mul_le_mul_of_nonneg_right h8 (Real.rpow_nonneg hB.le _))

/-- Compare the literal two-map XY constant with the already paid retained
slice constant. The one third-core F3/Q3 cost remains identical. -/
theorem xyConstant_le_retained {delta zeta population PL PU lambda loss : ℝ}
    (Qref Q3 J m : ℕ) (hd : 0 < delta) (hpop : 0 < population) (hPL : 0 < PL) (hPU : 0 < PU)
    (hlambda : 0 < lambda) (hloss : 0 < loss) (hQ : 0 < Qref) (hQ3 : 0 < Q3) :
    xyConstant delta zeta population PL PU lambda loss Qref Q3 J m ≤
      geometryCost*constant
        (lambda*(lowerCountCoefficient delta zeta population PU/upperCountCoefficient delta zeta PL)/
          (loss*(Qref:ℝ)^2*(Q3:ℝ)^4))
        ((Qref:ℝ)^4*upperCountCoefficient delta zeta PL/lowerCountCoefficient delta zeta population PU)
        (max 8 ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)) (3-extremalExponent) := by
  obtain ⟨hL,hU⟩ := count_coefficients_pos (zeta:=zeta) hd hpop hPL hPU
  have hQr : (0:ℝ)<Qref := by exact_mod_cast hQ
  have hQ3r : (0:ℝ)<Q3 := by exact_mod_cast hQ3
  let low := lowerCountCoefficient delta zeta population PU
  let up := upperCountCoefficient delta zeta PL
  let l := lambda*(low/up)/(loss*(Qref:ℝ)^2*(Q3:ℝ)^4)
  let u := (Qref:ℝ)^4*up/low
  let Ci : ℝ := ((201^3:ℕ):ℝ)
  let Cf : ℝ := ((1201^3:ℕ):ℝ)
  have hl : 0 < l := by dsimp [l,low,up]; positivity
  have hu : 0 ≤ u := by dsimp [u,low,up]; positivity
  have hA : 1 ≤ Ci*Cf := by norm_num [Ci,Cf]
  have hAC : Ci*Cf ≤ 27*Cf^2*Ci := by norm_num [Ci,Cf]
  have hB : (0:ℝ) < max 8 (((2^((phaseDepth m-m)/J+1):ℕ):ℝ)) :=
    lt_of_lt_of_le (by norm_num : (0:ℝ)<8) (le_max_left _ _)
  have hp := gap_power_comparison (Nat.cast_nonneg (2^((phaseDepth m-m)/J+1)))
    (show 0 ≤ 3-extremalExponent from sub_nonneg.mpr extremalExponent_le_three)
    (show 3-extremalExponent ≤ 3 by linarith only [extremalExponent_nonneg])
  have hh := constant_grid_comparison hl hu hA hAC hB hp
  have hLower : lambda*(low/up)/(loss*(Qref:ℝ)^2*Ci*Cf*(Q3:ℝ)^4)=l/(Ci*Cf) := by
    dsimp [l]
    field_simp
  have hUpper : (27*Cf)*(Cf*Ci*((Qref:ℝ)^4*up/low))=(27*Cf^2*Ci)*u := by
    dsimp [u]
    ring
  have hCost : geometryCost=512*(27*Cf^2*Ci) := by norm_num [geometryCost,Ci,Cf]
  dsimp only [xyConstant]
  change constant (lambda*(low/up)/(loss*(Qref:ℝ)^2*Ci*Cf*(Q3:ℝ)^4))
      ((27*Cf)*(Cf*Ci*((Qref:ℝ)^4*up/low)))
      (max 64 ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)) (3-extremalExponent) ≤
    geometryCost*constant l u (max 8 ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)) (3-extremalExponent)
  rw [hLower,hUpper,hCost]
  exact hh

end NativeThirdXYConstantComparison
