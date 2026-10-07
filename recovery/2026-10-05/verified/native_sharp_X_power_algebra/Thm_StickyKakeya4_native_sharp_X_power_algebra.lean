import Theorems.Thm_StickyKakeya4_native_sharp_X_cap_cancellation
import Theorems.Thm_StickyKakeya4_native_retained_slice_budget_algebra

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeSharpXPowerAlgebra
open NativeSourceParentGrainCleanup NativeActualProjectedGrainCount NativeActualRichPacketLayers
open NativeRetainedSliceBudgetAlgebra

/-- All costs after the genuine vertex-cap cancellation. The scale exponent
is separate; every remaining factor is a source retention or a finite count. -/
def fiberCoefficient (delta eta zeta tau c1 c2 lambda b : ℝ)
    (F1 G Q2 F3 Q3 : ℕ) (q : ℝ) (ell : ℕ) : ℝ :=
  parentGrainConstant*(2*(ell:ℝ)*(referenceConstant:ℝ))^ell*transverseCost q ell*quotientCost q*
    ((F1:ℝ)*G*(Q2:ℝ)^2*F3*(Q3:ℝ)^2*
      delta^(-(2*eta+3*zeta+7*tau+(ell:ℝ)*(c1+5*c2))))/(lambda*b)^(ell+1)

lemma gain_identity {delta rho lambda b C tax gamma : ℝ} (ell : ℕ)
    (hd : 0 < delta) (hrho : 0 < rho) (hC : 0 < C) :
    lambda*delta^tax*b*(b*lambda*delta^gamma/(C*rho))^ell*rho =
      ((lambda*b)^(ell+1)*delta^(tax+(ell:ℝ)*gamma)/C^ell)*rho^(-((ell:ℝ)-1)) := by
  rw [show -((ell:ℝ)-1)=1-(ell:ℝ) by ring,Real.rpow_sub hrho,Real.rpow_one,Real.rpow_natCast]
  rw [Real.rpow_add hd,show (ell:ℝ)*gamma=gamma*(ell:ℝ) by ring,
    Real.rpow_mul hd.le,Real.rpow_natCast]
  rw [div_pow,mul_pow,mul_pow,mul_pow,pow_succ]
  field_simp
  ring

/-- The original squared-scale time preimage removes exactly one of the
ell predecessor powers. No X-fiber regularity is used. -/
theorem gain_to_X {delta rho lambda b C tax gamma D X : ℝ} (ell : ℕ)
    (hd : 0 < delta) (hrho : 0 < rho) (hC : 0 < C) (hlambda : 0 < lambda) (hb : 0 < b)
    (H : lambda*delta^tax*b*(b*lambda*delta^gamma/(C*rho))^ell ≤ D*(1/rho)*X) :
    rho^(-((ell:ℝ)-1)) ≤ (D*C^ell*delta^(-(tax+(ell:ℝ)*gamma))/(lambda*b)^(ell+1))*X := by
  have hp : 0 < (lambda*b)^(ell+1)*delta^(tax+(ell:ℝ)*gamma)/C^ell := by positivity
  have hh := mul_le_mul_of_nonneg_right H hrho.le
  rw [gain_identity ell hd hrho hC] at hh
  have hright : (D*(1/rho)*X)*rho=D*X := by field_simp
  rw [hright] at hh
  have hresult : rho^(-((ell:ℝ)-1)) ≤
      (D*X)/((lambda*b)^(ell+1)*delta^(tax+(ell:ℝ)*gamma)/C^ell) :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hh)
  have heq : (D*X)/((lambda*b)^(ell+1)*delta^(tax+(ell:ℝ)*gamma)/C^ell)=
      (D*C^ell*delta^(-(tax+(ell:ℝ)*gamma))/(lambda*b)^(ell+1))*X := by
    rw [Real.rpow_neg hd.le]
    field_simp
  exact hresult.trans_eq heq

end NativeSharpXPowerAlgebra
