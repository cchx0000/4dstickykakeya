import Theorems.Thm_StickyKakeya4_native_window_integer_interpolation
import Theorems.Thm_StickyKakeya4_native_horizontal_menu_scale_cost

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeWindowInterpolationCost
open NativeWindowIntegerInterpolation NativeSquaredGrainQueries

/-- The literal predecessor/successor transfer spends at most the square
of the actual menu gap in the one- and two-dimensional quotient cases. -/
theorem low_dim_constant_le (l Ds Db B : ℕ) {K s : ℝ}
    (hl : l ≤ 2) (hDs : 0 < Ds) (hDsB : Ds ≤ B) (hDbB : Db ≤ B)
    (hK : 1 ≤ K) (hs2 : s ≤ 2) :
    NativeHalfScaleInterpolation.constant ((1/K)/(Ds:ℝ)^l)
      (upperConstant l Db K s) ((Db:ℝ)^l*K) s ≤ 36*K*(B:ℝ)^2 := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hKB : 0 ≤ K*(B:ℝ)^2 := mul_nonneg hKp.le (sq_nonneg _)
  have hDsp : (0:ℝ) < Ds := Nat.cast_pos.mpr hDs
  have hBp : (1:ℝ) ≤ B := by exact_mod_cast (hDs.trans_le hDsB)
  have hpow (D : ℕ) (hDB : D ≤ B) : (D:ℝ)^l ≤ (B:ℝ)^2 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg D) (Nat.cast_le.mpr hDB) l).trans
      (pow_le_pow_right₀ hBp hl)
  have htwo : (2:ℝ)^s ≤ 4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hs2
    norm_num at hh
    exact hh
  have htwo0 : 0 ≤ (2:ℝ)^s := by positivity
  have hfirst : (2:ℝ)^s/((1/K)/(Ds:ℝ)^l) ≤ 4*K*(B:ℝ)^2 := by
    have hid : (2:ℝ)^s/((1/K)/(Ds:ℝ)^l)=(2:ℝ)^s*K*(Ds:ℝ)^l := by field_simp
    rw [hid]
    exact mul_le_mul (mul_le_mul_of_nonneg_right htwo hKp.le) (hpow Ds hDsB)
      (by positivity) (by positivity)
  have h3 : (3*(Db:ℝ))^l ≤ 9*(B:ℝ)^2 := by
    have hh := (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 3*(Db:ℝ))
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hDbB) (by norm_num : (0:ℝ) ≤ 3)) l).trans
      (pow_le_pow_right₀ (by linarith only [hBp] : (1:ℝ) ≤ 3*(B:ℝ)) hl)
    nlinarith only [hh]
  have hKpow : (Db:ℝ)^l*K ≤ K*(B:ℝ)^2 := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hpow Db hDbB) hKp.le
  have hK2 : (Db:ℝ)^l*K*(2:ℝ)^s ≤ 4*K*(B:ℝ)^2 := by
    have hh := mul_le_mul hKpow htwo htwo0 (by positivity : 0 ≤ K*(B:ℝ)^2)
    nlinarith only [hh]
  have hupper : upperConstant l Db K s ≤ 9*K*(B:ℝ)^2 := by
    unfold upperConstant
    have hBsq := sq_nonneg (B:ℝ)
    have hpay := mul_le_mul_of_nonneg_right hK hBsq
    exact max_le (h3.trans (by nlinarith only [hpay]))
      (hK2.trans (by nlinarith only [hKB]))
  have hmax : max (upperConstant l Db K s) ((Db:ℝ)^l*K) ≤ 9*K*(B:ℝ)^2 :=
    max_le hupper (hKpow.trans (by nlinarith only [hKB]))
  have hlast : (2:ℝ)^s*max (upperConstant l Db K s) ((Db:ℝ)^l*K) ≤ 36*K*(B:ℝ)^2 := by
    have hh := mul_le_mul htwo hmax
      ((upperConstant_nonneg l Db K s).trans (le_max_left _ _)) (by norm_num : (0:ℝ) ≤ 4)
    nlinarith only [hh]
  have hBsq : (1:ℝ) ≤ (B:ℝ)^2 := one_le_pow₀ hBp
  have hbase : (1:ℝ) ≤ K*(B:ℝ)^2 := one_le_mul_of_one_le_of_one_le hK hBsq
  unfold NativeHalfScaleInterpolation.constant
  exact max_le (by nlinarith only [hbase])
    (max_le (hfirst.trans (by nlinarith only [hKB])) hlast)

lemma final_middle_cost_le {K B s : ℝ} (hK : 0 ≤ K) (hs2 : s ≤ 2) :
    (512:ℝ)^s*(36*K*B^2) ≤ (2:ℝ)^40*K*B^2 := by
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 512) hs2
  norm_num at hp
  have hh := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 36*K*B^2)
  have hn : 0 ≤ K*B^2 := mul_nonneg hK (sq_nonneg _)
  norm_num
  nlinarith only [hh,hn]

lemma final_coarse_cost_le {K B : ℝ} (hK : 0 ≤ K) (hB : 1 ≤ B) :
    (2:ℝ)^40*K ≤ (2:ℝ)^40*K*B^2 :=
  le_mul_of_one_le_right (by positivity) (one_le_pow₀ hB)

lemma AD_mono {X : Type*} [PseudoMetricSpace X] (P : Finset X) {mu K C s : ℝ}
    (hmu : 0 < mu) (hK : 0 < K) (hKC : K ≤ C) (H : FiniteVoronoiRealADCoarsening.ADBounds P mu K s) :
    FiniteVoronoiRealADCoarsening.ADBounds P mu C s := by
  intro x hx r hr hr1
  obtain ⟨hl,hu⟩ := H x hx r hr hr1
  have hrp : 0 < r := hmu.trans_le hr
  constructor
  · exact (div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity : 0 ≤ r/mu) _) hK hKC).trans hl
  · exact hu.trans (mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg (by positivity : 0 ≤ r/mu) _))

/-- This additional height-window interpolation cost is paid at the
parent scale. J is fixed before the later rank and source parameters. -/
theorem actual_gap_cost (J m : ℕ) (hJ : 0 < J) (hm : 6 ≤ m) {K : ℝ} (hK : 0 ≤ K) :
    36*K*(((2^((phaseDepth m-m)/J+1):ℕ):ℝ))^2 ≤
      18432*K*((64:ℝ)/((2^m:ℕ):ℝ))^(-(3/(J:ℝ))) := by
  have hh := NativeHorizontalMenuScaleCost.intrinsic_gap_power_cost J m hJ hm 2 (by norm_num) (by norm_num)
  rw [Real.rpow_ofNat] at hh
  have hg := pow_le_pow_left₀ (Nat.cast_nonneg (2^((phaseDepth m-m)/J+1)))
    (le_max_right 8 (((2^((phaseDepth m-m)/J+1):ℕ):ℝ))) 2
  have hp := mul_le_mul_of_nonneg_left (hg.trans hh) (by positivity : (0:ℝ) ≤ 36*K)
  nlinarith only [hp]

end NativeWindowInterpolationCost
