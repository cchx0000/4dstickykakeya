import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

noncomputable section
namespace NativeA2ParameterIdentities

/-- Every geometric query is at an allowed original radius. -/
theorem native_geometric_scales (delta eps1 : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (he1 : eps1<1/8)
    (hsmall : delta^eps1≤1/1408) :
    let theta := delta^eps1
    11*(2*theta^4)/(theta^2)=22*theta^2 ∧
    4*(11*(2*theta^4)/(theta^2))/(theta/8)=704*theta ∧
    delta≤2*theta^2 ∧ 2*theta^2≤1 ∧
    delta≤2*(704*theta) ∧ 2*(704*theta)≤1 ∧
    3*(22*theta^2)+2*(theta/8)≤theta/2 := by
  let theta := delta^eps1
  have ht : 0<theta := Real.rpow_pos_of_pos hd _
  have ht0 : theta≠0 := ne_of_gt ht
  have hw : 11*(2*theta^4)/(theta^2)=22*theta^2 := by field_simp; ring
  have hR : 4*(11*(2*theta^4)/(theta^2))/(theta/8)=704*theta := by
    rw [hw]
    field_simp
    ring
  have hdtheta : delta≤theta := by
    have h := Real.rpow_le_rpow_of_exponent_ge hd hd1 (show eps1≤1 by linarith)
    simpa only [Real.rpow_one] using h
  have hdrho : delta≤theta^2 := by
    have h := Real.rpow_le_rpow_of_exponent_ge hd hd1 (show eps1*2≤1 by linarith)
    rw [Real.rpow_one,Real.rpow_mul hd.le,Real.rpow_two] at h
    exact h
  have htSmall : theta≤1/1408 := hsmall
  have hs := mul_le_mul htSmall htSmall ht.le (by norm_num : (0:ℝ)≤1/1408)
  have hlin := mul_le_mul_of_nonneg_left htSmall ht.le
  refine ⟨hw,hR,?_,?_,?_,?_,?_⟩ <;> nlinarith only [hdtheta,hdrho,ht,htSmall,hs,hlin]

/-- The original Euclidean Frostman overlap cost has exactly the exponent
2t*eps1-3chi after the two rich-density powers have been divided out. -/
theorem overlap_power_identity (delta eps1 t chi : ℝ) (hd : 0<delta) :
    delta^(-chi)*((delta^eps1)^2)^t=
      (delta^chi)^2*delta^(2*t*eps1-3*chi) := by
  have htheta : 0≤delta^eps1 := Real.rpow_nonneg hd.le _
  rw [← Real.rpow_natCast_mul htheta 2 t,← Real.rpow_mul hd.le,
    ← Real.rpow_add hd,← Real.rpow_mul_natCast hd.le chi 2,← Real.rpow_add hd]
  congr 1
  ring

/-- The transverse radius is 704*delta^eps1, retaining its complete fixed
constant before using t<=2. -/
theorem transverse_power_identity (delta eps1 t chi : ℝ) (hd : 0<delta) :
    delta^(-chi)*(704*delta^eps1)^t=
      (delta^chi)^2*704^t*delta^(t*eps1-3*chi) := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤704) (Real.rpow_nonneg hd.le _)]
  rw [← Real.rpow_mul hd.le]
  calc
    _ = 704^t*(delta^(-chi)*delta^(eps1*t)) := by ring
    _ = 704^t*delta^(-chi+eps1*t) := by rw [← Real.rpow_add hd]
    _ = 704^t*delta^(chi*2+(t*eps1-3*chi)) := by congr 2; ring
    _ = _ := by rw [Real.rpow_add hd,Real.rpow_mul hd.le,Real.rpow_two]; ring

theorem diagonal_power_identity (delta t chi : ℝ) (hd : 0<delta) :
    delta^(-chi)*delta^t=delta^(t-chi) := by
  rw [← Real.rpow_add hd]
  congr 1
  ring

end NativeA2ParameterIdentities
