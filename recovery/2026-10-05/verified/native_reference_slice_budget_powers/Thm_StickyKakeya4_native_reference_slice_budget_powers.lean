import Theorems.Thm_StickyKakeya4_native_reference_slice_budget_costs
import Theorems.Thm_StickyKakeya4_native_horizontal_menu_scale_cost

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeReferenceSliceBudgetPowers
open NativeReferenceSliceBudgetAlgebra

/-- Actual rank radius, exact rank retention, and actual retained history
pay the remaining denominator. Here ell is the tuple length, not its Fin4 index. -/
lemma rank_history_power {delta r a t rankLoss lambda b : ℝ} (g ell : ℕ)
    (hd : 0 < delta) (hr : 0 < r) (hr1 : r ≤ 1) (hloss : 0 ≤ rankLoss)
    (hell : ell ≤ 3) (hrdelta : r ≤ delta^a) (ht : t=a*rankLoss)
    (hlambda : lambda=r^rankLoss/(4*((g:ℝ)+1)))
    (hb : r^((2*(ell:ℝ)+1)*rankLoss) ≤ b) :
    delta^(-(3*t))/(lambda^4*b^2) ≤
      (4*((g:ℝ)+1))^4*r^(-(21*rankLoss)) := by
  have hbpos : 0 < b := (Real.rpow_pos_of_pos hr _).trans_le hb
  have hlambdapos : 0 < lambda := by rw [hlambda]; positivity
  have hpow := Real.rpow_le_rpow_of_nonpos hr hrdelta (by linarith : -(3*rankLoss) ≤ 0)
  rw [←Real.rpow_mul hd.le] at hpow
  have he : a*(-(3*rankLoss))=-(3*t) := by rw [ht]; ring
  rw [he] at hpow
  have hp4 : (r^rankLoss)^4=r^(4*rankLoss) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr.le]
    congr 1
    ring
  have hp2 : (r^((2*(ell:ℝ)+1)*rankLoss))^2=r^((4*(ell:ℝ)+2)*rankLoss) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr.le]
    congr 1
    ring
  have hpowers : r^(-(3*rankLoss))/((r^rankLoss)^4*(r^((2*(ell:ℝ)+1)*rankLoss))^2)=
      r^(-((4*(ell:ℝ)+9)*rankLoss)) := by
    rw [hp4,hp2,←Real.rpow_add hr,←Real.rpow_sub hr]
    congr 1
    ring
  calc
    _ ≤ r^(-(3*rankLoss))/(lambda^4*(r^((2*(ell:ℝ)+1)*rankLoss))^2) := by gcongr
    _ = (4*((g:ℝ)+1))^4*
        (r^(-(3*rankLoss))/((r^rankLoss)^4*(r^((2*(ell:ℝ)+1)*rankLoss))^2)) := by
      rw [hlambda]
      field_simp
    _ = (4*((g:ℝ)+1))^4*r^(-((4*(ell:ℝ)+9)*rankLoss)) := by rw [hpowers]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_ge hr hr1
      have hellr : (ell:ℝ) ≤ 3 := by exact_mod_cast hell
      nlinarith only [hellr,hloss]

/-- The exact squared-grain relation converts the rank-radius loss. -/
lemma squared_grain_power {r rho rankLoss : ℝ}
    (_hr : 0 < r) (hrho : 0 < rho) (hloss : 0 ≤ rankLoss) (hloss1 : rankLoss ≤ 1)
    (hscale : rho^2 ≤ 6144*r) :
    r^(-(21*rankLoss)) ≤ (6144:ℝ)^21*rho^(-(42*rankLoss)) := by
  have hratio : rho^2/6144 ≤ r := by linarith only [hscale]
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ)<rho^2/6144)
    hratio (by linarith : -(21*rankLoss) ≤ 0)
  have heq : (rho^2/6144)^(-(21*rankLoss))=(6144:ℝ)^(21*rankLoss)*rho^(-(42*rankLoss)) := by
    rw [Real.div_rpow (sq_nonneg rho) (by norm_num),←Real.rpow_natCast,
      ←Real.rpow_mul hrho.le,Real.rpow_neg (by norm_num : (0:ℝ)≤6144),div_inv_eq_mul]
    norm_num only [Nat.cast_ofNat]
    have he : (2:ℝ)*(-(21*rankLoss))=-(42*rankLoss) := by ring
    rw [he,mul_comm]
  rw [heq] at hp
  have h6144 : (6144:ℝ)^(21*rankLoss) ≤ (6144:ℝ)^21 := by
    rw [←Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num
    linarith only [hloss1]
  exact hp.trans (mul_le_mul_of_nonneg_right h6144 (by positivity))

lemma reference_ad_constant_eq {L U Q B s : ℝ}
    (hL : 0 < L) (hU : 0 < U) (hQ : 0 < Q) (hB : 0 < B) :
    NativeSliceADConstant.constant (L/(Q^4*U)) (Q^4*U/L) B s =
      max 1 (729*(Q^4*(U/L))*B^s) := by
  have hfirst : B^s/(L/(Q^4*U))=(Q^4*(U/L))*B^s := by field_simp
  have hsecond : 729*(Q^4*U/L)*B^s=729*(Q^4*(U/L))*B^s := by ring
  have hp : 0 ≤ (Q^4*(U/L))*B^s := by positivity
  have hle : (Q^4*(U/L))*B^s ≤ 729*(Q^4*(U/L))*B^s := by nlinarith only [hp]
  unfold NativeSliceADConstant.constant
  rw [hfirst,hsecond,max_eq_right hle]

def sourceConstant (g : ℕ) : ℝ :=
  max 1 (729*512*ratioConstant*(4*((g:ℝ)+1))^4*(6144:ℝ)^21)

lemma sourceConstant_one_le (g : ℕ) : 1 ≤ sourceConstant g := le_max_left _ _

end NativeReferenceSliceBudgetPowers
