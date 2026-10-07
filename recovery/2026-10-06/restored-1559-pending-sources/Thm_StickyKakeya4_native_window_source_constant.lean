import Theorems.Thm_StickyKakeya4_native_window_constant_algebra
import Theorems.Thm_StickyKakeya4_native_window_coefficient_comparison
import Theorems.Thm_StickyKakeya4_native_actual_window_XY_ad
import Theorems.Thm_StickyKakeya4_native_window_power_payment

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeWindowSourceConstant
open NativeSliceADConstant NativeReferenceColumnExponents NativeFixedCompactKakeyaExponent
open NativeWindowConstantAlgebra NativeActualWindowXYAD NativeWindowXYMetric

/-- The literal variable-height source constant is compared to the same
retained-core constant. The new reference loss 65536 and the varying-map
capacity both remain explicit; no new retained set is constructed. -/
theorem windowConstant_le_retained {delta zeta population eps fullLower fullUpper retain loss : ℝ}
    (Qref Qnew C gap : ℕ) (hd : 0 < delta) (hpop : 0 < population) (heps : 0 < eps)
    (hPL : 0 < fullLower) (hPU : 0 < fullUpper) (hretain : 0 < retain) (hloss : 0 < loss)
    (hQ : 0 < Qref) (hQnew : 0 < Qnew) (hC : 0 < C) :
    let Cnew := NativeVariableHeightSourceBridge.comparisonCost
    let Cold := NativeAnisotropicGlobalSourceBridge.comparisonCost
    let Ln := lowerCountCoefficient delta zeta population ((Cnew/eps)*fullUpper)
    let Un := 8*(NativeVariableHeightNumeratorUpper.pairUpperConstant*delta^(-2*zeta))/((eps/Cnew)*fullLower)
    let Lo := lowerCountCoefficient delta zeta population ((Cold/eps)*fullUpper)
    let Uo := upperCountCoefficient delta zeta ((eps/Cold)*fullLower)
    windowConstant Ln Un retain loss Qref Qnew C gap ≤
      (65536*512*27*(C:ℝ)^3)*constant
        (retain*(Lo/Uo)/(loss*(Qref:ℝ)^2*(Qnew:ℝ)^4))
        ((Qref:ℝ)^4*Uo/Lo) (max 8 ((2^gap:ℕ):ℝ)) (3-extremalExponent) := by
  intro Cnew Cold Ln Un Lo Uo
  have hCn : 0 < Cnew := NativeVariableHeightSourceBridge.comparisonCost_pos
  have hCo : 0 < Cold := NativeAnisotropicGlobalSourceBridge.comparisonCost_pos
  have hPn := NativeVariableHeightNumeratorUpper.pairUpperConstant_pos
  obtain ⟨hLo,hUo⟩ := count_coefficients_pos (zeta:=zeta) hd hpop
    (by positivity : 0 < (eps/Cold)*fullLower) (by positivity : 0 < (Cold/eps)*fullUpper)
  have hLn : 0 < Ln := by dsimp [Ln,lowerCountCoefficient]; positivity
  have hUn : 0 < Un := by dsimp [Un]; positivity
  have hQr : (0:ℝ) < Qref := by exact_mod_cast hQ
  have hQnr : (0:ℝ) < Qnew := by exact_mod_cast hQnew
  have hCr : (1:ℝ) ≤ C := by exact_mod_cast hC
  have hratio : Un/Ln ≤ 65536*(Uo/Lo) :=
    NativeWindowCoefficientComparison.source_ratio_le hd hpop heps hPL hPU
  let lbase := retain/(loss*(Qref:ℝ)^2*(Qnew:ℝ)^4)
  have hh := ratio_window_le (by dsimp [lbase]; positivity : 0 < lbase)
    (by positivity : 0 ≤ (Qref:ℝ)^4) (div_pos hUn hLn) (div_pos hUo hLo)
    (by norm_num : (1:ℝ) ≤ 65536) hCr hratio (Nat.cast_nonneg (2^gap))
    (sub_nonneg.mpr extremalExponent_le_three)
    (show 3-extremalExponent ≤ 3 by linarith only [extremalExponent_nonneg])
  have hln : lbase/((C:ℝ)^2*(Un/Ln)) = retain*(Ln/Un)/(loss*(Qref:ℝ)^2*C*C*(Qnew:ℝ)^4) := by
    dsimp [lbase]
    field_simp <;> ring
  have hlo : lbase/(Uo/Lo) = retain*(Lo/Uo)/(loss*(Qref:ℝ)^2*(Qnew:ℝ)^4) := by
    dsimp [lbase]
    field_simp
  have hun : 27*(C:ℝ)^3*(Qref:ℝ)^4*(Un/Ln) =
      (27*(C:ℝ))*((C:ℝ)*C*((Qref:ℝ)^4*Un/Ln)) := by ring
  have huo : (Qref:ℝ)^4*(Uo/Lo) = (Qref:ℝ)^4*Uo/Lo := by ring
  rw [hln,hlo,hun,huo] at hh
  simpa only [windowConstant,mul_assoc,mul_left_comm,mul_comm] using hh

/-- The source Lipschitz exponent is spent nine times in the original
stopping scale r. The quotient-Y projection factor is still separate. -/
theorem windowConstant_le_retained_power {delta zeta population eps fullLower fullUpper retain loss Lip A r e : ℝ}
    (Qref Qnew gap : ℕ) (hd : 0 < delta) (hpop : 0 < population) (heps : 0 < eps)
    (hPL : 0 < fullLower) (hPU : 0 < fullUpper) (hretain : 0 < retain) (hloss : 0 < loss)
    (hQ : 0 < Qref) (hQnew : 0 < Qnew) (hLip : 0 ≤ Lip) (hA : 1 ≤ A)
    (hr : 0 < r) (hr1 : r ≤ 1) (he : 0 ≤ e) (hbound : Lip ≤ A*r^(-e)) :
    let Cnew := NativeVariableHeightSourceBridge.comparisonCost
    let Cold := NativeAnisotropicGlobalSourceBridge.comparisonCost
    let Ln := lowerCountCoefficient delta zeta population ((Cnew/eps)*fullUpper)
    let Un := 8*(NativeVariableHeightNumeratorUpper.pairUpperConstant*delta^(-2*zeta))/((eps/Cnew)*fullLower)
    let Lo := lowerCountCoefficient delta zeta population ((Cold/eps)*fullUpper)
    let Uo := upperCountCoefficient delta zeta ((eps/Cold)*fullLower)
    windowConstant Ln Un retain loss Qref Qnew ((2*menuRadius Lip+1)^3) gap ≤
      (65536*512*27*(2418*A)^9)*r^(-(9*e))*constant
        (retain*(Lo/Uo)/(loss*(Qref:ℝ)^2*(Qnew:ℝ)^4))
        ((Qref:ℝ)^4*Uo/Lo) (max 8 ((2^gap:ℕ):ℝ)) (3-extremalExponent) := by
  intro Cnew Cold Ln Un Lo Uo
  have hh := windowConstant_le_retained Qref Qnew ((2*menuRadius Lip+1)^3) gap
    hd hpop heps hPL hPU hretain hloss hQ hQnew (by positivity)
  have hK : 0 ≤ constant (retain*(Lo/Uo)/(loss*(Qref:ℝ)^2*(Qnew:ℝ)^4))
      ((Qref:ℝ)^4*Uo/Lo) (max 8 ((2^gap:ℕ):ℝ)) (3-extremalExponent) :=
    le_trans (by norm_num) (one_le_constant _ _ _ _)
  have hcap := menu_cube_cost_of_lip_bound hLip hA hr hr1 he hbound
  exact hh.trans (by
    have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcap
      (by norm_num : (0:ℝ) ≤ 65536*512*27)) hK
    simpa only [mul_assoc] using hh')

/-- The actual mapped chart has Lip at most 3*r^(-2*geometryTolerance).
With the three quarter-budget margins, geometryTolerance <= epsilon/144
pays the same-source window quotient constant at the requested epsilon. -/
theorem pay_factory_window_and_quotient {rho r geometryTolerance epsilon Kret KXY CX KY : ℝ}
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (he : 0 < epsilon)
    (hg : 0 ≤ geometryTolerance) (hgsmall : geometryTolerance ≤ epsilon/144)
    (hscale : rho^2 ≤ 6144*r) (hret0 : 0 ≤ Kret) (hxy0 : 0 ≤ KXY)
    (hfixed : NativeWindowPowerPayment.productCost 3 (2*geometryTolerance) ≤ rho^(-(epsilon/4)))
    (hret : Kret ≤ rho^(-(epsilon/4))) (hX : CX ≤ rho^(-(epsilon/4)))
    (hXY : KXY ≤ NativeWindowPowerPayment.coordinateCost 3*r^(-(18*geometryTolerance))*Kret)
    (hY : KY ≤ 512000*KXY*max 1 CX) :
    KXY ≤ rho^(-(3*epsilon/4)) ∧ KY ≤ rho^(-epsilon) := by
  have hXY' : KXY ≤ NativeWindowPowerPayment.coordinateCost 3*r^(-(9*(2*geometryTolerance)))*Kret := by
    have hexp : 9*(2*geometryTolerance)=18*geometryTolerance := by ring
    simpa only [hexp] using hXY
  have hh := NativeWindowPowerPayment.pay_window_and_quotient hrho hrho1 (by norm_num : (0:ℝ)<3)
    (by positivity : 0 ≤ 2*geometryTolerance) (by positivity : 0 ≤ epsilon/4)
    hscale hret0 hxy0 hfixed hret hX hXY' hY
  constructor
  · exact hh.1.trans (Real.rpow_le_rpow_of_exponent_ge hrho hrho1 (by linarith only [hgsmall]))
  · exact hh.2.trans (Real.rpow_le_rpow_of_exponent_ge hrho hrho1 (by linarith only [hgsmall]))

end NativeWindowSourceConstant
