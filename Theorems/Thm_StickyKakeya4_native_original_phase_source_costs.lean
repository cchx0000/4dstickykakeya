import Theorems.Thm_StickyKakeya4_native_original_window_kt
import Theorems.Thm_StickyKakeya4_original_w_normalized_phase
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeOriginalPhaseSourceCosts
open NativeOriginalWindowKT OriginalWNormalizedPhase
/-- The original scalar-column matrix entries give the operator bound used
 in the physical window calculation. -/
theorem scalar_matrix_operator_bound (F : ℝ →L[ℝ] ℝ × ℝ)
    (hentries : |(F 1).1| ≤ 1 ∧ |(F 1).2| ≤ 1) : ‖F‖ ≤ 1 := by
  apply F.opNorm_le_bound (by norm_num)
  intro x
  rw [scalar_operator_apply,norm_smul]
  have hh : ‖F 1‖ ≤ 1 := max_le hentries.1 hentries.2
  simpa only [mul_one,one_mul] using mul_le_mul_of_nonneg_left hh (norm_nonneg x)
/-- Original incidence/direction errors and scheduled slope oscillation
 determine the physical grain window, with the absolute constant retained. -/
theorem original_grain_coefficient_bound {C0 M B A Lip IncErr DirErr : ℝ}
    (hC0 : 1 ≤ C0) (hM : 1 ≤ M) (hB : B ≤ 1) (hA : A ≤ 1)
    (hLip0 : 0 ≤ Lip) (hLip : Lip ≤ C0*M)
    (hInc0 : 0 ≤ IncErr) (hInc : IncErr ≤ C0) (hDir : DirErr ≤ C0) :
    (4*B+1)*Lip+(12+4*A)*max DirErr (2*IncErr) ≤ 37*C0*M := by
  have hC00 : 0 ≤ C0 := by linarith only [hC0]
  have hM0 : 0 ≤ M := by linarith only [hM]
  have hmax0 : 0 ≤ max DirErr (2*IncErr) := (by positivity : 0 ≤ 2*IncErr).trans (le_max_right _ _)
  have hmax : max DirErr (2*IncErr) ≤ 2*C0 := max_le (by linarith only [hDir,hC00]) (by linarith only [hInc])
  have h1 : (4*B+1)*Lip ≤ 5*(C0*M) := by
    calc
      _ ≤ 5*Lip := mul_le_mul_of_nonneg_right (by linarith only [hB]) hLip0
      _ ≤ _ := mul_le_mul_of_nonneg_left hLip (by norm_num)
  have h2 : (12+4*A)*max DirErr (2*IncErr) ≤ 32*C0 := by
    calc
      _ ≤ 16*max DirErr (2*IncErr) := mul_le_mul_of_nonneg_right (by linarith only [hA]) hmax0
      _ ≤ 16*(2*C0) := mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ = _ := by ring
  have hCM : C0 ≤ C0*M := by nlinarith only [hC00,hM]
  linarith only [h1,h2,hCM]
/-- Exact polynomial KT cost from the actual window, a scheduled xi field,
 and its original C0 error. No local A population is supplied as a premise. -/
theorem source_window_KT_coefficient {r tau Delta width A Cxi C0 M : ℝ}
    (hr : 0 < r) (htau : r ≤ tau) (hrDelta : r ≤ Delta) (hDelta : Delta ≤ M*r)
    (hC0 : 1 ≤ C0) (hM : 1 ≤ M) (hwidth0 : 0 ≤ width) (hwidth : width ≤ 40*C0*M*r)
    (hA0 : 0 ≤ A) (hA : A ≤ 1) (hXi0 : 0 ≤ Cxi) (hXi : Cxi ≤ C0) :
    4*windowFiberCap r tau Delta width A Cxi ≤ 5101248*(C0*M)^4 := by
  have hd : 0 < Delta := hr.trans_le hrDelta
  have ht : 0 < tau := hr.trans_le htau
  have hC00 : 0 ≤ C0 := by linarith only [hC0]
  have hM0 : 0 ≤ M := by linarith only [hM]
  have hG1 : 1 ≤ C0*M := by nlinarith only [hC0,hM]
  have hG0 : 0 ≤ C0*M := by positivity
  have hfirst : r/Delta+2 ≤ 3 := by
    have hh := (div_le_one hd).mpr hrDelta
    linarith only [hh]
  have hY : (4*width+A*r)/Delta+2 ≤ 163*(C0*M) := by
    have hAr := mul_le_mul_of_nonneg_right hA hr.le
    have hnum : 4*width+A*r ≤ 161*(C0*M)*r := by nlinarith only [hwidth,hAr,mul_le_mul_of_nonneg_right hG1 hr.le]
    have hrd := mul_le_mul_of_nonneg_left hrDelta (show 0 ≤ 161*(C0*M) by positivity)
    have hh : (4*width+A*r)/Delta ≤ 161*(C0*M) := (div_le_iff₀ hd).mpr (hnum.trans hrd)
    linarith only [hh,hG1]
  have hXiD : Cxi*Delta ≤ (C0*M)*tau := by
    calc
      _ ≤ C0*(M*r) := mul_le_mul hXi hDelta hd.le hC00
      _ ≤ C0*(M*tau) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htau hM0) hC00
      _ = _ := by ring
  have hXiFactor : 2*Cxi*Delta/tau+2 ≤ 4*(C0*M) := by
    have hh : 2*Cxi*Delta/tau ≤ 2*(C0*M) := (div_le_iff₀ ht).mpr (by nlinarith only [hXiD])
    linarith only [hh,hG1]
  have hY0 : 0 ≤ (4*width+A*r)/Delta+2 := by positivity
  have hXiF0 : 0 ≤ 2*Cxi*Delta/tau+2 := by positivity
  unfold windowFiberCap
  calc
    _ ≤ 4*(3*(163*(C0*M))^2*(4*(C0*M))^2) := by gcongr
    _ = _ := by ring
/-- With only the literal source cutoff C0 <= delta^-eta, the actual A KT
 constant is bounded by delta^(-9eta). The exponent is independent of kappa. -/
theorem source_window_KT_power {delta eta r tau Delta width A Cxi C0 : ℝ}
    (hd : 0 < delta) (hMlarge : 5101248 ≤ delta^(-eta)) (hC0 : 1 ≤ C0) (hC0cap : C0 ≤ delta^(-eta))
    (hr : 0 < r) (htau : r ≤ tau) (hrDelta : r ≤ Delta) (hDelta : Delta ≤ delta^(-eta)*r)
    (hwidth0 : 0 ≤ width) (hwidth : width ≤ 40*C0*delta^(-eta)*r)
    (hA0 : 0 ≤ A) (hA : A ≤ 1) (hXi0 : 0 ≤ Cxi) (hXi : Cxi ≤ C0) :
    4*windowFiberCap r tau Delta width A Cxi ≤ delta^(-9*eta) := by
  let M := delta^(-eta)
  have hM1 : 1 ≤ M := by dsimp [M]; linarith only [hMlarge]
  have hM0 : 0 ≤ M := (Real.rpow_pos_of_pos hd _).le
  have hC00 : 0 ≤ C0 := by linarith only [hC0]
  have hh := source_window_KT_coefficient hr htau hrDelta hDelta hC0 hM1 hwidth0 hwidth hA0 hA hXi0 hXi
  have hcap : 5101248*(C0*M)^4 ≤ M^9 := by
    calc
      _ ≤ M*(M*M)^4 := by gcongr
      _ = _ := by ring
  have hid : M^9=delta^(-9*eta) := by
    dsimp [M]
    rw [← Real.rpow_natCast,← Real.rpow_mul hd.le]
    congr 1
    norm_num
    ring
  exact hh.trans (hcap.trans_eq hid)
end NativeOriginalPhaseSourceCosts
