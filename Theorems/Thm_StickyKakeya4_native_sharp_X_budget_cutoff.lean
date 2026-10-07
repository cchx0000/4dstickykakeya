import Theorems.Thm_StickyKakeya4_native_sharp_X_budget_power
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeSharpXBudgetCutoff
open StickyKakeya4 NativeSharpXBudgetPower NativeRankExponentHierarchy
open NativeReferenceSliceBudgetCutoff

theorem exists_source_cutoff (epsilon c : ℝ) (g : ℕ) (he : 0 < epsilon) (hc : 0 < c) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀delta : ℝ,0 < delta → delta ≤ delta0 →
      ∀rho r a : ℝ,0 < rho → c^3/8 ≤ a → r ≤ delta^a → rho^2 ≤ 6144*r →
        sourceConstant g ≤ rho^(-(epsilon/4)) := by
  have hC : 0 < sourceConstant g := lt_of_lt_of_le (by norm_num) (sourceConstant_one_le g)
  obtain ⟨delta0,hd0,hd01,H⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < (c^3/8)*epsilon/8 by positivity)
    (show 0 ≤ sourceConstant g*(6144:ℝ)^(epsilon/8) by positivity)
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
  have hpaid : sourceConstant g*rho^(epsilon/4) ≤ 1 := by
    calc
      _ ≤ sourceConstant g*((6144:ℝ)^(epsilon/8)*delta^((c^3/8)*epsilon/8)) :=
        mul_le_mul_of_nonneg_left hp hC.le
      _ = (sourceConstant g*(6144:ℝ)^(epsilon/8))*delta^((c^3/8)*epsilon/8) := by ring
      _ ≤ _ := H delta hd hsmall
  calc
    _ ≤ 1/rho^(epsilon/4) := (le_div_iff₀ (Real.rpow_pos_of_pos hrho _)).mpr hpaid
    _ = _ := by rw [Real.rpow_neg hrho.le,one_div]

def sourceCutoff (epsilon c : ℝ) (g : ℕ) (he : 0 < epsilon) (hc : 0 < c) : ℝ :=
  Classical.choose (exists_source_cutoff epsilon c g he hc)

lemma sourceCutoff_pos (epsilon c : ℝ) (g : ℕ) (he : 0 < epsilon) (hc : 0 < c) :
    0 < sourceCutoff epsilon c g he hc := (Classical.choose_spec (exists_source_cutoff epsilon c g he hc)).1

lemma sourceCutoff_pays (epsilon c : ℝ) (g : ℕ) (he : 0 < epsilon) (hc : 0 < c)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ sourceCutoff epsilon c g he hc)
    (rho r a : ℝ) (hrho : 0 < rho) (ha : c^3/8 ≤ a) (hrdelta : r ≤ delta^a)
    (hscale : rho^2 ≤ 6144*r) : sourceConstant g ≤ rho^(-(epsilon/4)) :=
  (Classical.choose_spec (exists_source_cutoff epsilon c g he hc)).2.2
    delta hd hsmall rho r a hrho ha hrdelta hscale

lemma sourceCutoff_le_one (epsilon c : ℝ) (g : ℕ) (he : 0 < epsilon) (hc : 0 < c) :
    sourceCutoff epsilon c g he hc ≤ 1 :=
  (Classical.choose_spec (exists_source_cutoff epsilon c g he hc)).2.1

lemma paid_X_lower {rho epsilon dimension C X : ℝ}
    (hrho : 0 < rho) (hX : 0 ≤ X) (H : rho^(-dimension) ≤ C*X) (HC : C ≤ rho^(-epsilon)) :
    rho^epsilon*rho^(-dimension) ≤ X := by
  have hh := mul_le_mul_of_nonneg_left
    (H.trans (mul_le_mul_of_nonneg_right HC hX)) (Real.rpow_pos_of_pos hrho epsilon).le
  have heq : rho^epsilon*(rho^(-epsilon)*X)=X := by
    rw [←mul_assoc,←Real.rpow_add hrho,add_neg_cancel,Real.rpow_zero,one_mul]
  exact hh.trans_eq heq

end NativeSharpXBudgetCutoff
