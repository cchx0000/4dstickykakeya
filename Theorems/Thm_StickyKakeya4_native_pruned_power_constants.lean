import Theorems.Thm_StickyKakeya4_native_original_pruned_mass
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativePrunedPowerConstants
open Classical Finset StickyKakeya4 NativeOriginalPrunedMass
open scoped ENNReal

lemma exponent_coefficient {delta eta zeta : ℝ} (hd : 0<delta)
    (hsmall : 2*delta^(zeta-eta)≤1) :
    2*(ENNReal.ofReal delta).rpow (-eta)≤(ENNReal.ofReal delta).rpow (-zeta) := by
  have hp := Real.rpow_pos_of_pos hd zeta
  have hr : 2*delta^(-eta)≤delta^(-zeta) := by
    apply (mul_le_mul_iff_left₀ hp).mp
    have hl : (2*delta^(-eta))*delta^zeta=2*delta^(zeta-eta) := by
      rw [mul_assoc,←Real.rpow_add hd]
      congr 1
      ring
    have hu : delta^(-zeta)*delta^zeta=1 := by rw [←Real.rpow_add hd]; simp
    rw [hl,hu]
    exact hsmall
  have hh := ENNReal.ofReal_le_ofReal hr
  simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,
    ENNReal.ofReal_rpow_of_pos hd,ENNReal.rpow_eq_pow] using hh

lemma retained_density_power {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    {eta zeta : ℝ} (hd : 0<D.thickness)
    (hsmall : 2*D.thickness^(zeta-eta)≤1)
    (hden : (ENNReal.ofReal D.thickness).rpow eta*tubeMass D R≤2*shadingMass D R) :
    (ENNReal.ofReal D.thickness).rpow zeta*tubeMass D R≤ shadingMass D R := by
  let e := ENNReal.ofReal D.thickness
  have he0 : e≠0 := by dsimp [e]; positivity
  have heT : e≠⊤ := ENNReal.ofReal_ne_top
  have hc : 2*e.rpow (zeta-eta)≤1 := by
    have hh := ENNReal.ofReal_le_ofReal hsmall
    simpa only [e,ENNReal.rpow_eq_pow,ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
      ENNReal.ofReal_ofNat,ENNReal.ofReal_rpow_of_pos hd,ENNReal.ofReal_one] using hh
  calc
    _ = e.rpow (zeta-eta)*(e.rpow eta*tubeMass D R) := by
      rw [←mul_assoc]
      simp only [ENNReal.rpow_eq_pow]
      rw [←ENNReal.rpow_add _ _ he0 heT]
      congr 2
      ring
    _ ≤ e.rpow (zeta-eta)*(2*shadingMass D R) := mul_le_mul' le_rfl hden
    _ = (2*e.rpow (zeta-eta))*shadingMass D R := by ring
    _ ≤ 1*shadingMass D R := mul_le_mul' hc le_rfl
    _ = _ := one_mul _

lemma retained_CW_power {n : ℕ} {D : FiniteScaleSource n} {eta zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (hret : n≤2*R.card)
    (hsmall : 2*D.thickness^(zeta-eta)≤1) (U : Set E4) (hU : Convex ℝ U) :
    ((R.filter (fun i=>markedUnitTube (D.line i) D.thickness⊆U)).card:ℝ≥0∞)≤
      (ENNReal.ofReal D.thickness).rpow (-zeta)*MeasureTheory.volume U*R.card := by
  exact (retained_convexWolff h R hret U hU).trans
    (mul_le_mul' (mul_le_mul' (exponent_coefficient h.1.2.1 hsmall) le_rfl) le_rfl)

end NativePrunedPowerConstants
