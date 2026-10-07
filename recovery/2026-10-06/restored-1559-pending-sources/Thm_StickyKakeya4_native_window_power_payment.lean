import Theorems.Thm_StickyKakeya4_native_third_XY_fixed_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeWindowPowerPayment
open NativeReferenceSliceBudgetCutoff

def coordinateCost (A : ℝ) : ℝ := 65536*512*27*(2418*A)^9

/-- The quotient factor 512000 is included exactly here, together with
the actual squared-scale conversion of the nine-fold geometry loss. -/
def productCost (A e : ℝ) : ℝ := 512000*coordinateCost A*(6144:ℝ)^(9*e)

lemma coordinateCost_pos {A : ℝ} (hA : 0 < A) : 0 < coordinateCost A := by
  unfold coordinateCost
  positivity

lemma productCost_pos {A : ℝ} (hA : 0 < A) (e : ℝ) : 0 < productCost A e := by
  unfold productCost
  have hh := coordinateCost_pos hA
  positivity

lemma squared_geometry_loss {r rho e : ℝ} (hrho : 0 < rho) (he : 0 ≤ e)
    (hscale : rho^2 ≤ 6144*r) :
    r^(-(9*e)) ≤ (6144:ℝ)^(9*e)*rho^(-(18*e)) := by
  have hratio : rho^2/6144 ≤ r := by linarith only [hscale]
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ)<rho^2/6144)
    hratio (by linarith only [he] : -(9*e) ≤ 0)
  have heq : (rho^2/6144)^(-(9*e))=(6144:ℝ)^(9*e)*rho^(-(18*e)) := by
    rw [Real.div_rpow (sq_nonneg rho) (by norm_num),←Real.rpow_natCast,
      ←Real.rpow_mul hrho.le,Real.rpow_neg (by norm_num : (0:ℝ)≤6144),div_inv_eq_mul]
    norm_num only [Nat.cast_ofNat]
    have hexp : (2:ℝ)*(-(9*e))=-(18*e) := by ring
    rw [hexp,mul_comm]
  exact hp.trans_eq heq

/-- A single cutoff, chosen after the finite menu and geometry constants
but before D, pays their full product. The geometry exponent remains in
the power estimate rather than being hidden in this fixed cutoff. -/
theorem exists_source_product_cutoff (budget c A e : ℝ)
    (hb : 0 < budget) (hc : 0 < c) (hA : 0 < A) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀delta : ℝ,0 < delta → delta ≤ delta0 →
      ∀rho r a : ℝ,0 < rho → c^3/8 ≤ a → r ≤ delta^a → rho^2 ≤ 6144*r →
        productCost A e ≤ rho^(-budget) := by
  have hC := productCost_pos hA e
  obtain ⟨delta0,hd0,hd01,H⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < (c^3/8)*(budget/2) by positivity)
    (show 0 ≤ productCost A e*(6144:ℝ)^(budget/2) by positivity)
    (show (0:ℝ)<1 by norm_num)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall rho r a hrho ha hrdelta hscale
  have hd1 := hsmall.trans hd01
  have hrbound : r ≤ delta^(c^3/8) := hrdelta.trans
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 ha)
  have hbound : rho^2 ≤ 6144*delta^(c^3/8) := hscale.trans
    (mul_le_mul_of_nonneg_left hrbound (by norm_num))
  have hp := Real.rpow_le_rpow (sq_nonneg rho) hbound (show 0 ≤ budget/2 by positivity)
  have hleft : (rho^2)^(budget/2)=rho^budget := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hrho.le]
    congr 1
    norm_num
  rw [hleft,Real.mul_rpow (by norm_num) (Real.rpow_nonneg hd.le _),←Real.rpow_mul hd.le] at hp
  have hpaid : productCost A e*rho^budget ≤ 1 := by
    calc
      _ ≤ productCost A e*((6144:ℝ)^(budget/2)*delta^((c^3/8)*(budget/2))) :=
        mul_le_mul_of_nonneg_left hp hC.le
      _ = (productCost A e*(6144:ℝ)^(budget/2))*delta^((c^3/8)*(budget/2)) := by ring
      _ ≤ _ := H delta hd hsmall
  calc
    _ ≤ 1/rho^budget := (le_div_iff₀ (Real.rpow_pos_of_pos hrho _)).mpr hpaid
    _ = _ := by rw [Real.rpow_neg hrho.le,one_div]

/-- The already source-derived retained and X bounds combine with the
literal variable-height map estimate. The geometry tax is 9e at r, or
18e at the squared grain width rho, and the fixed product is spent once. -/
theorem pay_window_and_quotient {rho r A e budget u v Kret KXY CX KY : ℝ}
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hA : 0 < A) (he : 0 ≤ e) (hv : 0 ≤ v)
    (hscale : rho^2 ≤ 6144*r) (hret0 : 0 ≤ Kret) (hxy0 : 0 ≤ KXY)
    (hfixed : productCost A e ≤ rho^(-budget))
    (hret : Kret ≤ rho^(-u)) (hX : CX ≤ rho^(-v))
    (hXY : KXY ≤ coordinateCost A*r^(-(9*e))*Kret)
    (hY : KY ≤ 512000*KXY*max 1 CX) :
    KXY ≤ rho^(-(budget+u+18*e)) ∧ KY ≤ rho^(-(budget+u+v+18*e)) := by
  have hC := coordinateCost_pos hA
  have hgeom := squared_geometry_loss hrho he hscale
  have hbase : 512000*KXY ≤ productCost A e*rho^(-(18*e))*Kret := by
    calc
      _ ≤ 512000*(coordinateCost A*r^(-(9*e))*Kret) :=
        mul_le_mul_of_nonneg_left hXY (by norm_num)
      _ ≤ 512000*(coordinateCost A*((6144:ℝ)^(9*e)*rho^(-(18*e)))*Kret) := by gcongr
      _ = _ := by unfold productCost; ring
  have hpaid : 512000*KXY ≤ rho^(-(budget+u+18*e)) := by
    calc
      _ ≤ productCost A e*rho^(-(18*e))*Kret := hbase
      _ ≤ rho^(-budget)*rho^(-(18*e))*rho^(-u) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hfixed (by positivity)) hret hret0 (by positivity)
      _ = _ := by rw [←Real.rpow_add hrho,←Real.rpow_add hrho]; congr 1; ring
  refine ⟨(by nlinarith only [hpaid,hxy0]),?_⟩
  have hmax : max 1 CX ≤ rho^(-v) := max_le
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrho hrho1 (neg_nonpos.mpr hv)) hX
  calc
    _ ≤ 512000*KXY*max 1 CX := hY
    _ ≤ rho^(-(budget+u+18*e))*rho^(-v) :=
      mul_le_mul hpaid hmax (le_trans (by norm_num) (le_max_left _ _)) (by positivity)
    _ = _ := by rw [←Real.rpow_add hrho]; congr 1; ring

end NativeWindowPowerPayment
