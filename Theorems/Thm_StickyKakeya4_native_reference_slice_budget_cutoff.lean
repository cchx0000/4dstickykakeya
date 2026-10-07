import Theorems.Thm_StickyKakeya4_native_reference_slice_budget_source
import Theorems.Thm_StickyKakeya4_native_rank_exponent_hierarchy

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeReferenceSliceBudgetCutoff
open StickyKakeya4 NativeReferenceSliceBudgetPowers NativeMiddleWindowBalance NativeRankExponentHierarchy

/-- The finite horizontal count and initial rank tolerance precede tau,
the first-stage menu, and every source. -/
theorem exists_fixed_ad_parameters (epsilon : ℝ) (he : 0 < epsilon) :
    ∃J : ℕ,0 < J ∧ 3/(J:ℝ) ≤ epsilon/4 ∧
      ∃etaMax : ℝ,0 < etaMax ∧ etaMax ≤ 1 ∧ etaMax ≤ epsilon/168 := by
  obtain ⟨J,hJ⟩ := exists_nat_gt (12/epsilon)
  have hJr : (0:ℝ)<J := (div_pos (by norm_num) he).trans hJ
  have hJn : 0 < J := by exact_mod_cast hJr
  refine ⟨J,hJn,?_,min 1 (epsilon/168),lt_min (by norm_num) (by positivity),
    min_le_left _ _,min_le_right _ _⟩
  apply (div_le_iff₀ hJr).mpr
  have hh := (div_lt_iff₀ he).mp hJ
  nlinarith only [hh]

/-- This cutoff is chosen after g but before D. It pays the fixed source
constant simultaneously at every possible rank cutoff, using only the actual
squared-grain upper relation. -/
theorem exists_source_constant_cutoff (epsilon c : ℝ) (g : ℕ) (he : 0 < epsilon) (hc : 0 < c) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀delta : ℝ,0 < delta → delta ≤ delta0 →
      ∀rho r a : ℝ,0 < rho → c^3/8 ≤ a → r ≤ delta^a → rho^2 ≤ 6144*r →
        sourceConstant g ≤ rho^(-(epsilon/2)) := by
  have hC : 0 < sourceConstant g := lt_of_lt_of_le (by norm_num) (sourceConstant_one_le g)
  obtain ⟨delta0,hd0,hd01,H⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < (c^3/8)*epsilon/4 by positivity)
    (show 0 ≤ sourceConstant g*(6144:ℝ)^(epsilon/4) by positivity)
    (show (0:ℝ)<1 by norm_num)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall rho r a hrho ha hrdelta hscale
  have hd1 := hsmall.trans hd01
  have hrbound : r ≤ delta^(c^3/8) := hrdelta.trans
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 ha)
  have hbound : rho^2 ≤ 6144*delta^(c^3/8) := hscale.trans
    (mul_le_mul_of_nonneg_left hrbound (by norm_num))
  have hp := Real.rpow_le_rpow (sq_nonneg rho) hbound (show 0 ≤ epsilon/4 by positivity)
  have hleft : (rho^2)^(epsilon/4)=rho^(epsilon/2) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hrho.le]
    congr 1
    norm_num
    ring
  rw [hleft,Real.mul_rpow (by norm_num) (Real.rpow_nonneg hd.le _),←Real.rpow_mul hd.le] at hp
  have heq : (c^3/8)*(epsilon/4)=(c^3/8)*epsilon/4 := by ring
  rw [heq] at hp
  have hpaid : sourceConstant g*rho^(epsilon/2) ≤ 1 := by
    calc
      _ ≤ sourceConstant g*((6144:ℝ)^(epsilon/4)*delta^((c^3/8)*epsilon/4)) :=
        mul_le_mul_of_nonneg_left hp hC.le
      _ = (sourceConstant g*(6144:ℝ)^(epsilon/4))*delta^((c^3/8)*epsilon/4) := by ring
      _ ≤ _ := H delta hd hsmall
  calc
    _ ≤ 1/rho^(epsilon/2) := (le_div_iff₀ (Real.rpow_pos_of_pos hrho _)).mpr hpaid
    _ = _ := by rw [Real.rpow_neg hrho.le,one_div]

def sourceCutoff (epsilon c : ℝ) (g : ℕ) (he : 0 < epsilon) (hc : 0 < c) : ℝ :=
  Classical.choose (exists_source_constant_cutoff epsilon c g he hc)

lemma sourceCutoff_pos (epsilon c : ℝ) (g : ℕ) (he : 0 < epsilon) (hc : 0 < c) :
    0 < sourceCutoff epsilon c g he hc :=
  (Classical.choose_spec (exists_source_constant_cutoff epsilon c g he hc)).1

lemma sourceCutoff_le_one (epsilon c : ℝ) (g : ℕ) (he : 0 < epsilon) (hc : 0 < c) :
    sourceCutoff epsilon c g he hc ≤ 1 :=
  (Classical.choose_spec (exists_source_constant_cutoff epsilon c g he hc)).2.1

lemma sourceCutoff_pays (epsilon c : ℝ) (g : ℕ) (he : 0 < epsilon) (hc : 0 < c)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ sourceCutoff epsilon c g he hc)
    (rho r a : ℝ) (hrho : 0 < rho) (ha : c^3/8 ≤ a) (hrdelta : r ≤ delta^a)
    (hscale : rho^2 ≤ 6144*r) : sourceConstant g ≤ rho^(-(epsilon/2)) :=
  (Classical.choose_spec (exists_source_constant_cutoff epsilon c g he hc)).2.2
    delta hd hsmall rho r a hrho ha hrdelta hscale

lemma absorb_remaining_power {rho epsilon loss : ℝ} (g : ℕ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hpaid : sourceConstant g ≤ rho^(-(epsilon/2)))
    (hloss : loss ≤ epsilon/2) : sourceConstant g*rho^(-loss) ≤ rho^(-epsilon) := by
  calc
    _ ≤ rho^(-(epsilon/2))*rho^(-loss) := mul_le_mul_of_nonneg_right hpaid (by positivity)
    _ = rho^(-(epsilon/2+loss)) := by rw [←Real.rpow_add hrho]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hrho hrho1 (by linarith only [hloss])

end NativeReferenceSliceBudgetCutoff
