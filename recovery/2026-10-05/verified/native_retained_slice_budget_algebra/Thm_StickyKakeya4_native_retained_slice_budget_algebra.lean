import Theorems.Thm_StickyKakeya4_native_reference_slice_budget_final
import Theorems.Thm_StickyKakeya4_native_weighted_grain_quotient_source
import Theorems.Thm_StickyKakeya4_native_parent_height_graph_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000

noncomputable section
namespace NativeRetainedSliceBudgetAlgebra
open NativeSliceADConstant NativeReferenceSliceBudgetPowers NativeWeightedGrainQuotientSource

def quotientCost (q : ℝ) : ℝ := 4*(⌈quotientCap q⌉₊:ℝ)

lemma quotientCost_pos {q : ℝ} (hq : 0 < q) : 0 < quotientCost q := by
  have hh := (quotientCap_pos hq).trans_le (Nat.le_ceil (quotientCap q))
  unfold quotientCost
  positivity

/-- Exact comparison of the retained and reference constants. The third
core's F3Q3^4 is preserved, while the reference Q^4 already pays its Q^2. -/
theorem retained_constant_le_reference {L U Q B s theta graph quotient F3 Q3 : ℝ}
    (hL : 0 < L) (hU : 0 < U) (hQ : 1 ≤ Q) (hB : 0 < B)
    (htheta : 0 < theta) (hgraph : 0 < graph) (hquotient : 0 < quotient)
    (hF3 : 0 < F3) (hQ3 : 0 < Q3) :
    constant (theta*(L/U)/((graph*quotient*F3)*Q^2*Q3^4)) (Q^4*U/L) B s ≤
      constant (L/(Q^4*U)) (Q^4*U/L) B s * max 1 (graph*quotient*F3*Q3^4/theta) := by
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  let extra := graph*quotient*F3*Q3^4/theta
  let ref := constant (L/(Q^4*U)) (Q^4*U/L) B s
  have hRef1 : 1 ≤ ref := one_le_constant _ _ _ _
  have hRef0 : 0 ≤ ref := by linarith only [hRef1]
  have hbase : (Q^4*(U/L))*B^s ≤ ref := by
    have hh : 729*(Q^4*(U/L))*B^s ≤ ref := by
      dsimp only [ref]
      rw [reference_ad_constant_eq hL hU hQpos hB]
      exact le_max_right _ _
    have hp : 0 ≤ (Q^4*(U/L))*B^s := by positivity
    linarith only [hh,hp]
  have hsmall : Q^2 ≤ Q^4 := pow_le_pow_right₀ hQ (by norm_num)
  have hloweq : B^s/(theta*(L/U)/((graph*quotient*F3)*Q^2*Q3^4))=
      extra*((Q^2*(U/L))*B^s) := by
    dsimp [extra]
    field_simp
  have hlow : B^s/(theta*(L/U)/((graph*quotient*F3)*Q^2*Q3^4)) ≤ ref*max 1 extra := by
    rw [hloweq]
    calc
      _ ≤ extra*((Q^4*(U/L))*B^s) := by gcongr
      _ ≤ extra*ref := mul_le_mul_of_nonneg_left hbase (by dsimp [extra]; positivity)
      _ ≤ (max 1 extra)*ref := mul_le_mul_of_nonneg_right (le_max_right _ _) hRef0
      _ = _ := mul_comm _ _
  have hrefle : ref ≤ ref*max 1 extra := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (le_max_left 1 extra) hRef0
  have hupper : 729*(Q^4*U/L)*B^s ≤ ref :=
    (le_max_right _ _).trans (le_max_right _ _)
  change max 1 (max _ _) ≤ ref*max 1 extra
  exact max_le (hRef1.trans hrefle) (max_le hlow (hupper.trans hrefle))

/-- The exact natural ceiling loss in the selected quotient fiber. -/
lemma quotientCost_le {r q epsilonQ : ℝ} (hr : 0 < r) (hq : 0 < q) (hq1 : q ≤ 1)
    (hqlow : r^(epsilonQ/6)/2 ≤ q) :
    quotientCost q ≤ (32768*(32002:ℝ)^4)*r^(-(2*epsilonQ/3)) := by
  have hfour : 1 ≤ 4/q := (le_div_iff₀ hq).mpr (by linarith only [hq1])
  have hcap : 1 ≤ quotientCap q := by
    have hpow : (1:ℝ) ≤ (4/q)^4 := one_le_pow₀ hfour
    unfold quotientCap
    nlinarith only [hpow]
  have hceil : (⌈quotientCap q⌉₊:ℝ) ≤ 2*quotientCap q := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ quotientCap q by linarith only [hcap])
    linarith only [hh,hcap]
  have hratio : 4/q ≤ 8/r^(epsilonQ/6) := by
    apply (div_le_div_iff₀ hq (Real.rpow_pos_of_pos hr _)).mpr
    linarith only [hqlow]
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ)≤4/q) hratio 4
  have heq : (8/r^(epsilonQ/6))^4=4096*r^(-(2*epsilonQ/3)) := by
    rw [div_pow,←Real.rpow_natCast (r^(epsilonQ/6)),←Real.rpow_mul hr.le]
    have he : (epsilonQ/6)*(4:ℝ)=2*epsilonQ/3 := by ring
    norm_num only [Nat.cast_ofNat]
    rw [he,Real.rpow_neg hr.le]
    ring
  unfold quotientCost
  calc
    _ ≤ 8*quotientCap q := by linarith only [hceil]
    _ = (8*(32002:ℝ)^4)*(4/q)^4 := by unfold quotientCap; ring
    _ ≤ (8*(32002:ℝ)^4)*(4096*r^(-(2*epsilonQ/3))) :=
      mul_le_mul_of_nonneg_left (hpow.trans_eq heq) (by positivity)
    _ = _ := by ring

end NativeRetainedSliceBudgetAlgebra
