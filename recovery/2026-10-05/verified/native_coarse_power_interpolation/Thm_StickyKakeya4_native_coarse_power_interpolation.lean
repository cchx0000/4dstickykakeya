import Theorems.Thm_StickyKakeya4_native_actual_local_extremal

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeCoarsePowerInterpolation

/-- A forward physical-shadow comparison propagates a lower bound toward
the middle scale. Its fixed coefficient and scale ratio are explicitly paid.
No monotonicity of multiplicity in scale is assumed. -/
theorem middle_lower_of_forward_bound_general
    {delta rhoCoarse rhoMiddle r kappa b t C Mc Mm : ℝ}
    (hd : 0 < delta) (hrho : 0 < rhoMiddle) (hr : 0 < r) (hkappa : 0 ≤ kappa)
    (hscale : rhoCoarse=r*rhoMiddle) (hratio : r ≤ delta^(-t))
    (hconstant : C ≤ delta^(-b)) (hnear : delta^b*rhoCoarse^(-kappa) ≤ Mc)
    (hforward : Mc ≤ C*r^4*Mm) (hM : 0 ≤ Mm) :
    delta^(2*b+t*(4+kappa))*rhoMiddle^(-kappa) ≤ Mm := by
  let loss := b+t*(4+kappa)
  have hcancelR : r^(-kappa)*r^kappa=1 := by
    rw [←Real.rpow_add hr]
    simp
  have hcross : delta^b*rhoMiddle^(-kappa) ≤ C*r^(4+kappa)*Mm := by
    calc
      _ = (delta^b*rhoCoarse^(-kappa))*r^kappa := by
        rw [hscale,Real.mul_rpow hr.le hrho.le]
        calc
          _ = delta^b*rhoMiddle^(-kappa)*(r^(-kappa)*r^kappa) := by rw [hcancelR,mul_one]
          _ = _ := by ring
      _ ≤ (C*r^4*Mm)*r^kappa :=
        mul_le_mul_of_nonneg_right (hnear.trans hforward) (Real.rpow_pos_of_pos hr _).le
      _ = _ := by rw [Real.rpow_add hr,Real.rpow_ofNat]; ring
  have hpower : r^(4+kappa) ≤ delta^(-t*(4+kappa)) := by
    calc
      _ ≤ (delta^(-t))^(4+kappa) :=
        Real.rpow_le_rpow hr.le hratio (by linarith)
      _ = _ := (Real.rpow_mul hd.le (-t) (4+kappa)).symm
  have hcoefficient : C*r^(4+kappa) ≤ delta^(-loss) := by
    calc
      _ ≤ delta^(-b)*delta^(-t*(4+kappa)) :=
        mul_le_mul hconstant hpower (Real.rpow_pos_of_pos hr _).le (Real.rpow_pos_of_pos hd _).le
      _ = _ := by rw [←Real.rpow_add hd]; congr 1; dsimp [loss]; ring
  have hpaid := hcross.trans (mul_le_mul_of_nonneg_right hcoefficient hM)
  have hcancel : delta^loss*delta^(-loss)=1 := by rw [←Real.rpow_add hd]; simp
  calc
    _ = delta^loss*(delta^b*rhoMiddle^(-kappa)) := by
      rw [show 2*b+t*(4+kappa)=loss+b by dsimp [loss]; ring,Real.rpow_add hd]
      ring
    _ ≤ delta^loss*(delta^(-loss)*Mm) :=
      mul_le_mul_of_nonneg_left hpaid (Real.rpow_pos_of_pos hd _).le
    _ = Mm := by rw [←mul_assoc,hcancel,one_mul]

/-- The actual physical coarse interpolation constant is 729. -/
theorem middle_lower_of_forward_bound
    {delta rhoCoarse rhoMiddle r kappa b t Mc Mm : ℝ}
    (hd : 0 < delta) (hrho : 0 < rhoMiddle) (hr : 0 < r) (hkappa : 0 ≤ kappa)
    (hscale : rhoCoarse=r*rhoMiddle) (hratio : r ≤ delta^(-t))
    (hconstant : (729:ℝ) ≤ delta^(-b)) (hnear : delta^b*rhoCoarse^(-kappa) ≤ Mc)
    (hforward : Mc ≤ 729*r^4*Mm) (hM : 0 ≤ Mm) :
    delta^(2*b+t*(4+kappa))*rhoMiddle^(-kappa) ≤ Mm :=
  middle_lower_of_forward_bound_general hd hrho hr hkappa hscale hratio hconstant hnear hforward hM

end NativeCoarsePowerInterpolation
