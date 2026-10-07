import Theorems.Thm_StickyKakeya4_native_encoded_quotient_ad

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
noncomputable section
namespace NativeQuotientConstantBound
open NativeEncodedQuotientAD NativeHalfScaleInterpolation

/-- The actual rank2/3 quotient step costs only an absolute factor times
the two already paid ambient and full-fiber constants. -/
theorem quotientConstant_le (ell : ℕ) (hell2 : 2 ≤ ell) (hell3 : ell ≤ 3)
    (kappa K C : ℝ) (hkappa : 0 ≤ kappa) (hK : 1 ≤ K) (hC : 0 < C) :
    quotientConstant (ell-1) (4-ell) (1/((32:ℝ)^(ell-1)*C)) K (3-kappa) ≤
      512000*K*max 1 C := by
  have hKp : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hmax : (1:ℝ) ≤ max 1 C := le_max_left _ _
  have hCmax : C ≤ max 1 C := le_max_right _ _
  have hpow : (2:ℝ)^((3-kappa)-((ell-1:ℕ):ℝ)) ≤ 4 := by
    have hexp : (3-kappa)-((ell-1:ℕ):ℝ) ≤ 2 := by
      have hh : (1:ℝ) ≤ ((ell-1:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ ell-1 by omega)
      linarith only [hkappa,hh]
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hexp
    norm_num at hh ⊢
    exact hh
  have hpow0 : 0 ≤ (2:ℝ)^((3-kappa)-((ell-1:ℕ):ℝ)) := by positivity
  have htarget : 1 ≤ 512000*K*max 1 C := by nlinarith [mul_le_mul hK hmax (by norm_num : (0:ℝ)≤1) (by positivity : 0≤K)]
  unfold quotientConstant NativeHalfScaleInterpolation.constant
  apply max_le htarget
  apply max_le
  · have he : (2:ℝ)^((3-kappa)-((ell-1:ℕ):ℝ))/((1/K)/(3:ℝ)^(ell-1))=
        (2:ℝ)^((3-kappa)-((ell-1:ℕ):ℝ))*(3:ℝ)^(ell-1)*K := by
      field_simp
    rw [he]
    have hthree : (3:ℝ)^(ell-1) ≤ 9 := by interval_cases ell <;> norm_num
    have hprod : (2:ℝ)^((3-kappa)-((ell-1:ℕ):ℝ))*(3:ℝ)^(ell-1) ≤ 36 := by
      nlinarith [mul_le_mul hpow hthree (by positivity : (0:ℝ)≤(3:ℝ)^(ell-1)) (by norm_num : (0:ℝ)≤4)]
    have hh := mul_le_mul_of_nonneg_right hprod hKp.le
    have hhmax := mul_le_mul_of_nonneg_left hmax (by positivity : 0≤512000*K)
    nlinarith only [hh,hhmax,hKp]
  · have hd : (ell-1)+(4-ell)=3 := by omega
    rw [hd]
    have hu : (3:ℝ)^(ell-1)*(2:ℝ)^3*K/(1/((32:ℝ)^(ell-1)*C)) ≤ 128000*K*C := by
      have he : (3:ℝ)^(ell-1)*(2:ℝ)^3*K/(1/((32:ℝ)^(ell-1)*C))=
          ((3:ℝ)^(ell-1)*8*(32:ℝ)^(ell-1))*K*C := by field_simp; ring
      rw [he]
      have hn : (3:ℝ)^(ell-1)*8*(32:ℝ)^(ell-1) ≤ 128000 := by interval_cases ell <;> norm_num
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hKp.le) hC.le
    have hg : (5:ℝ)^3*K/(1/((32:ℝ)^(ell-1)*C)) ≤ 128000*K*C := by
      have he : (5:ℝ)^3*K/(1/((32:ℝ)^(ell-1)*C))=
          (125*(32:ℝ)^(ell-1))*K*C := by field_simp; ring
      rw [he]
      have hn : 125*(32:ℝ)^(ell-1) ≤ 128000 := by interval_cases ell <;> norm_num
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hKp.le) hC.le
    have hh := mul_le_mul_of_nonneg_left (max_le hu hg) hpow0
    have hhpow := mul_le_mul_of_nonneg_right hpow (by positivity : 0≤128000*K*C)
    have hhm := mul_le_mul_of_nonneg_left hCmax (by positivity : 0≤512000*K)
    nlinarith only [hh,hhpow,hhm]

end NativeQuotientConstantBound
