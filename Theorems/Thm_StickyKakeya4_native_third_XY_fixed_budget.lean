import Theorems.Thm_StickyKakeya4_native_third_XY_constant_comparison
import Theorems.Thm_StickyKakeya4_native_sharp_X_budget_cutoff
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeThirdXYFixedBudget
open StickyKakeya4 NativeReferenceSliceBudgetCutoff NativeThirdXYConstantComparison

def fixedCost : ℝ := 512000*geometryCost
lemma fixedCost_one_le : 1 ≤ fixedCost := by
  norm_num [fixedCost,geometryCost]

theorem exists_source_cutoff (epsilon c : ℝ) (he : 0 < epsilon) (hc : 0 < c) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀delta : ℝ,0 < delta → delta ≤ delta0 →
      ∀rho r a : ℝ,0 < rho → c^3/8 ≤ a → r ≤ delta^a → rho^2 ≤ 6144*r →
        fixedCost ≤ rho^(-(epsilon/4)) := by
  have hC : 0 < fixedCost := lt_of_lt_of_le (by norm_num) (fixedCost_one_le)
  obtain ⟨delta0,hd0,hd01,H⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < (c^3/8)*epsilon/8 by positivity)
    (show 0 ≤ fixedCost*(6144:ℝ)^(epsilon/8) by positivity)
    (show (0:ℝ)<1 by norm_num)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall rho r a hrho ha hrdelta hscale
  have hd1 := hsmall.trans hd01
  have hrbound : r ≤ delta^(c^3/8) := hrdelta.trans
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 ha)
  have hbound : rho^2 ≤ 6144*delta^(c^3/8) := hscale.trans
    (mul_le_mul_of_nonneg_left hrbound (by norm_num))
  have hp := Real.rpow_le_rpow (sq_nonneg rho) hbound (show 0 ≤ epsilon/8 by positivity)
  have hleft : (rho^2)^(epsilon/8)=rho^(epsilon/4) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hrho.le]
    congr 1
    norm_num
    ring
  rw [hleft,Real.mul_rpow (by norm_num) (Real.rpow_nonneg hd.le _),←Real.rpow_mul hd.le] at hp
  have heq : (c^3/8)*(epsilon/8)=(c^3/8)*epsilon/8 := by ring
  rw [heq] at hp
  have hpaid : fixedCost*rho^(epsilon/4) ≤ 1 := by
    calc
      _ ≤ fixedCost*((6144:ℝ)^(epsilon/8)*delta^((c^3/8)*epsilon/8)) :=
        mul_le_mul_of_nonneg_left hp hC.le
      _ = (fixedCost*(6144:ℝ)^(epsilon/8))*delta^((c^3/8)*epsilon/8) := by ring
      _ ≤ _ := H delta hd hsmall
  calc
    _ ≤ 1/rho^(epsilon/4) := (le_div_iff₀ (Real.rpow_pos_of_pos hrho _)).mpr hpaid
    _ = _ := by rw [Real.rpow_neg hrho.le,one_div]

def sourceCutoff (epsilon c : ℝ) (he : 0 < epsilon) (hc : 0 < c) : ℝ :=
  Classical.choose (exists_source_cutoff epsilon c he hc)

lemma sourceCutoff_pos (epsilon c : ℝ) (he : 0 < epsilon) (hc : 0 < c) :
    0 < sourceCutoff epsilon c he hc := (Classical.choose_spec (exists_source_cutoff epsilon c he hc)).1

lemma sourceCutoff_pays (epsilon c : ℝ) (he : 0 < epsilon) (hc : 0 < c)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ sourceCutoff epsilon c he hc)
    (rho r a : ℝ) (hrho : 0 < rho) (ha : c^3/8 ≤ a) (hrdelta : r ≤ delta^a)
    (hscale : rho^2 ≤ 6144*r) : fixedCost ≤ rho^(-(epsilon/4)) :=
  (Classical.choose_spec (exists_source_cutoff epsilon c he hc)).2.2
    delta hd hsmall rho r a hrho ha hrdelta hscale

lemma sourceCutoff_le_one (epsilon c : ℝ) (he : 0 < epsilon) (hc : 0 < c) :
    sourceCutoff epsilon c he hc ≤ 1 :=
  (Classical.choose_spec (exists_source_cutoff epsilon c he hc)).2.1


/-- The fixed coordinate and quotient constants are paid by a single
pre-source cutoff. The source-derived retained and X costs keep their margins. -/
theorem pay_XY_and_quotient_constants {rho epsilon Kret KXY CX KY : ℝ}
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (he : 0 < epsilon)
    (hret0 : 0 ≤ Kret) (hxy0 : 0 ≤ KXY)
    (hfixed : fixedCost ≤ rho^(-(epsilon/4)))
    (hret : Kret ≤ rho^(-(epsilon/4))) (hX : CX ≤ rho^(-(epsilon/4)))
    (hXY : KXY ≤ geometryCost*Kret)
    (hY : KY ≤ 512000*KXY*max 1 CX) :
    KXY ≤ rho^(-(epsilon/2)) ∧ KY ≤ rho^(-epsilon) := by
  have hgeom : geometryCost ≤ fixedCost := by norm_num [geometryCost,fixedCost]
  have hnum : (512000:ℝ) ≤ fixedCost := by norm_num [geometryCost,fixedCost]
  have hpow : 1 ≤ rho^(-(epsilon/4)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrho hrho1 (by linarith only [he])
  have hmax : max 1 CX ≤ rho^(-(epsilon/4)) := max_le hpow hX
  have hxy : KXY ≤ rho^(-(epsilon/2)) := calc
    _ ≤ geometryCost*Kret := hXY
    _ ≤ rho^(-(epsilon/4))*rho^(-(epsilon/4)) :=
      mul_le_mul (hgeom.trans hfixed) hret hret0 (by positivity)
    _ = _ := by rw [←Real.rpow_add hrho]; congr 1; ring
  refine ⟨hxy,?_⟩
  calc
    KY ≤ 512000*KXY*max 1 CX := hY
    _ ≤ rho^(-(epsilon/4))*rho^(-(epsilon/2))*rho^(-(epsilon/4)) :=
      mul_le_mul (mul_le_mul (hnum.trans hfixed) hxy hxy0 (by positivity)) hmax
        (le_trans (by norm_num) (le_max_left _ _)) (by positivity)
    _ = _ := by rw [←Real.rpow_add hrho,←Real.rpow_add hrho]; congr 1; ring

end NativeThirdXYFixedBudget
