import Theorems.Thm_StickyKakeya4_native_fixed_menu_slice_ad

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeHorizontalMenuScaleCost
open NativeSquaredGrainQueries

lemma parent_scale_dyadic_span (m : ℕ) (hm6 : 6 ≤ m) :
    (64:ℝ)/((2^m:ℕ):ℝ)=(2:ℝ)⁻¹^(phaseDepth m-m) := by
  have hspan : phaseDepth m-m=m-6 := by unfold phaseDepth; omega
  have hp : (2^m:ℕ)=2^(m-6)*64 := by
    calc
      _ = 2^((m-6)+6) := by rw [Nat.sub_add_cancel hm6]
      _ = _ := by rw [pow_add]; norm_num
  rw [hspan,hp]
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,inv_pow]
  field_simp

/-- The horizontal-menu interpolation loss is measured at the parent
scale itself. No comparison between that scale and the source delta is needed. -/
lemma intrinsic_gap_cost (J m : ℕ) (hJ : 0 < J) (hm6 : 6 ≤ m) :
    max 8 (((2^((phaseDepth m-m)/J+1):ℕ):ℝ)) ≤
      8*((64:ℝ)/((2^m:ℕ):ℝ))^(-(1/(J:ℝ))) := by
  have hdy := parent_scale_dyadic_span m hm6
  have hfloor : (((phaseDepth m-m)/J:ℕ):ℝ) ≤ ((phaseDepth m-m:ℕ):ℝ)/(J:ℝ) := Nat.cast_div_le
  have hgap : ((((phaseDepth m-m)/J+1)-0:ℕ):ℝ) ≤ ((phaseDepth m-m:ℕ):ℝ)/J+1 := by
    simp only [Nat.sub_zero,Nat.cast_add,Nat.cast_one]
    linarith only [hfloor]
  have hp := NativeFixedSizeScaleMenu.dyadic_gap_power (phaseDepth m-m)
    ((phaseDepth m-m)/J+1) 0 J hJ hdy hgap
  simp only [Nat.sub_zero] at hp
  have hR : (0:ℝ)<64/((2^m:ℕ):ℝ) := by positivity
  have hR1 : (64:ℝ)/((2^m:ℕ):ℝ) ≤ 1 := by
    rw [hdy]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hpow : 1 ≤ ((64:ℝ)/((2^m:ℕ):ℝ))^(-(1/(J:ℝ))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hR hR1 (neg_nonpos.mpr (by positivity))
  exact max_le (by nlinarith only [hpow]) (hp.trans (by nlinarith only [hpow]))

/-- A fixed J spends at most3/J of the parent-scale exponent in the
all-radius interpolation. This choice can precede tau and the source. -/
lemma intrinsic_gap_power_cost (J m : ℕ) (hJ : 0 < J) (hm6 : 6 ≤ m)
    (s : ℝ) (hs : 0 ≤ s) (hs3 : s ≤ 3) :
    (max 8 (((2^((phaseDepth m-m)/J+1):ℕ):ℝ)))^s ≤
      512*((64:ℝ)/((2^m:ℕ):ℝ))^(-(3/(J:ℝ))) := by
  have hR : (0:ℝ)<64/((2^m:ℕ):ℝ) := by positivity
  have hR1 : (64:ℝ)/((2^m:ℕ):ℝ) ≤ 1 := by
    rw [parent_scale_dyadic_span m hm6]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hJr : (0:ℝ)<J := by exact_mod_cast hJ
  have hp := Real.rpow_le_rpow
    (by positivity : (0:ℝ) ≤ max 8 (((2^((phaseDepth m-m)/J+1):ℕ):ℝ)))
    (intrinsic_gap_cost J m hJ hm6) hs
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hR.le _),←Real.rpow_mul hR.le] at hp
  have h8 : (8:ℝ)^s ≤ 512 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤8) hs3
    norm_num at hh
    exact hh
  have hexp : -(3/(J:ℝ)) ≤ -(1/(J:ℝ))*s := by
    calc
      _ ≤ -(s/(J:ℝ)) := neg_le_neg (div_le_div_of_nonneg_right hs3 hJr.le)
      _ = _ := by ring
  have hRPow := Real.rpow_le_rpow_of_exponent_ge hR hR1 hexp
  exact hp.trans (mul_le_mul h8 hRPow (by positivity) (by norm_num))

end NativeHorizontalMenuScaleCost
