import Theorems.Thm_StickyKakeya4_original_native_power_algebra
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
set_option exponentiation.threshold 2048
noncomputable section

namespace OriginalNativeComparisonPowerAlgebra
open OriginalNativePowerAlgebra OriginalNativeProjectionBSGCore
open OriginalTwoProjectionCartesian OriginalNativeStructuredPowerBounds

/-- All numerical losses of the actual original-source comparison are a
fixed monomial. In particular they do not depend on the exhaustion length. -/
theorem native_comparison_power {t h N M Z : ℝ} (ht : 0<t)
    (hh : 0<h) (hh1 : h≤1) (hN : 0<N) (hM : M^2=N/t^2) (hZ : 0≤Z)
    (hcomp : t*(originalDensity (t^3/16) N h M)^77*Z <
      (2:ℝ)^242*fiberBound h*(restrictedSumLoss h)^15*(12672/h^5)) :
    t^386*h^206*Z < (2:ℝ)^1018*7920^15*12672 := by
  have hlo := (native_density_retention_lower ht hh hh1 hN hM).1
  have hgeo := original_geometric_cover_power_bounds hh hh1
    (show |(0:ℝ)|≤4/h^2 by simp; positivity)
  have hleft := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (show 0≤t^5*h^2/(2:ℝ)^10 by positivity) hlo 77) ht.le) hZ
  have hK : 0≤restrictedSumLoss h := by unfold restrictedSumLoss; positivity
  have hright : (2:ℝ)^242*fiberBound h*(restrictedSumLoss h)^15*(12672/h^5) ≤
      (2:ℝ)^242*(64/h^2)*(7920/h^3)^15*(12672/h^5) := by
    apply mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hgeo.1 (by positivity))
      (pow_le_pow_left₀ hK hgeo.2.1 15) (pow_nonneg hK 15) (by positivity)
  have hh' := (hleft.trans_lt hcomp).trans_le hright
  have hmul := mul_lt_mul_of_pos_right hh'
    (show 0<(2:ℝ)^770*h^52 by positivity)
  have hidL : t*(t^5*h^2/(2:ℝ)^10)^77*Z*((2:ℝ)^770*h^52)=t^386*h^206*Z := by ring
  have hidR : (2:ℝ)^242*(64/h^2)*(7920/h^3)^15*(12672/h^5)*((2:ℝ)^770*h^52)=
      (2:ℝ)^1018*7920^15*12672 := by field_simp; ring
  rwa [hidL,hidR] at hmul

end OriginalNativeComparisonPowerAlgebra
