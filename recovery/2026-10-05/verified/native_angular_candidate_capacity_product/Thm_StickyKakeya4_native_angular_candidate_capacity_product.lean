import Theorems.Thm_StickyKakeya4_native_compatible_angular_candidates

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeAngularCandidateCapacityProduct
open Classical Finset StickyKakeya4 NativeCompatibleAngularCandidates
open NativeTwoAxisPowerInterpolation NativeFixedCompactKakeyaExponent
open scoped BigOperators

/-- The fixed, already-derived phase-parent times physical-point menu cost. -/
def costConstant : ℝ := 131^3*2401

lemma costConstant_one_le : 1 ≤ costConstant := by norm_num [costConstant]

lemma depthPower_comp (kappa : ℝ) (a b c : ℕ) :
    depthPower kappa a b*depthPower kappa b c=depthPower kappa a c := by
  unfold depthPower
  rw [←Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 1
  ring

lemma depthPower_pow (kappa : ℝ) (a b ell : ℕ) :
    (depthPower kappa a b)^ell=depthPower (kappa*(ell:ℝ)) a b := by
  unfold depthPower
  rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  congr 1
  ring

/-- Exact cancellation of every interior grain depth. -/
lemma depthPower_product (kappa : ℝ) (d : ℕ → ℕ) (J : ℕ) :
    (∏j∈range J,depthPower kappa (d j) (d (j+1)))=depthPower kappa (d 0) (d J) := by
  induction J with
  | zero => simp [depthPower]
  | succ J ih => rw [prod_range_succ,ih,depthPower_comp]

lemma depthPower_one_le {kappa : ℝ} (hk : 0 ≤ kappa) {m f : ℕ} (hmf : m ≤ f) :
    1 ≤ depthPower kappa m f := by
  apply Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2)
  exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hmf)) hk

/-- The actual ceiling costs at most twice its actual scalar upper. Its
argument is at least one by the native scale and nonnegative loss/exponent. -/
theorem singleCapacity_cast_le {n : ℕ} {D : FiniteScaleSource n}
    {loss kappa : ℝ} (hd : 0 < D.thickness) (hd1 : D.thickness ≤ 1)
    (hloss : 0 ≤ loss) (hk : 0 ≤ kappa) {m f : ℕ} (hmf : m ≤ f) :
    (singleCapacity D loss kappa m f:ℝ) ≤
      (2*costConstant)*D.thickness^(-loss)*depthPower kappa m f := by
  have hdelta : 1 ≤ D.thickness^(-loss) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (neg_nonpos.mpr hloss)
  have hA : 1 ≤ costConstant*D.thickness^(-loss)*depthPower kappa m f :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le costConstant_one_le hdelta) (depthPower_one_le hk hmf)
  unfold singleCapacity
  rw [←depthPower_eq_relative]
  change (⌈costConstant*D.thickness^(-loss)*depthPower kappa m f⌉₊:ℝ) ≤ _
  calc
    _ ≤ costConstant*D.thickness^(-loss)*depthPower kappa m f+1 :=
      (Nat.ceil_lt_add_one (zero_le_one.trans hA)).le
    _ ≤ 2*(costConstant*D.thickness^(-loss)*depthPower kappa m f) := by linarith
    _ = _ := by ring

/-- The exact constructed successor capacities telescope. No independent
product bound or absorption certificate is assumed. -/
theorem successor_capacity_product {n : ℕ} {D : FiniteScaleSource n}
    {loss kappa : ℝ} (hd : 0 < D.thickness) (hd1 : D.thickness ≤ 1)
    (hloss : 0 ≤ loss) (hk : 0 ≤ kappa) (d : ℕ → ℕ) (hmono : Monotone d)
    (J ell : ℕ) :
    ((∏j∈range J,(singleCapacity D loss kappa (d j) (d (j+1)))^ell:ℕ):ℝ) ≤
      (2*costConstant)^(J*ell)*D.thickness^(-loss*((J*ell:ℕ):ℝ))*
        depthPower (kappa*(ell:ℝ)) (d 0) (d J) := by
  have hsingle (j : ℕ) :
      (singleCapacity D loss kappa (d j) (d (j+1)):ℝ)^ell ≤
        ((2*costConstant)*D.thickness^(-loss)*depthPower kappa (d j) (d (j+1)))^ell :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (singleCapacity_cast_le hd hd1 hloss hk (hmono (Nat.le_succ j))) ell
  rw [Nat.cast_prod]
  simp only [Nat.cast_pow]
  calc
    _ ≤ ∏j∈range J,((2*costConstant)*D.thickness^(-loss)*depthPower kappa (d j) (d (j+1)))^ell :=
      prod_le_prod (fun _j _hj => pow_nonneg (Nat.cast_nonneg _) ell) (fun j _hj => hsingle j)
    _ = _ := by
      rw [prod_pow,prod_mul_distrib,prod_const,card_range,depthPower_product,mul_pow,
        ←pow_mul,mul_pow,←Real.rpow_mul_natCast hd.le,depthPower_pow]

lemma selectionBudget_zero {n : ℕ} (D : FiniteScaleSource n) (loss kappa : ℝ)
    (J stop ell : ℕ) : selectionBudget D loss kappa J stop ell 0=(259^3)^ell := if_pos rfl

lemma selectionBudget_succ {n : ℕ} (D : FiniteScaleSource n) (loss kappa : ℝ)
    (J stop ell j : ℕ) : selectionBudget D loss kappa J stop ell (j+1)=
      (singleCapacity D loss kappa (depth J stop j) (depth J stop (j+1)))^ell := by
  simp [selectionBudget]

/-- Separate the fixed root cost from the J genuine successor costs. -/
lemma selectionBudget_product_split {n : ℕ} (D : FiniteScaleSource n) (loss kappa : ℝ)
    (J stop ell : ℕ) :
    ((∏j∈range (J+1),selectionBudget D loss kappa J stop ell j:ℕ):ℝ)=
      ((259:ℝ)^3)^ell*
        ((∏j∈range J,(singleCapacity D loss kappa (depth J stop j) (depth J stop (j+1)))^ell:ℕ):ℝ) := by
  rw [prod_range_succ',selectionBudget_zero]
  simp_rw [selectionBudget_succ]
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat,mul_comm]

/-- Exact actual grain-menu loss, with the root constant kept separate and
all dyadic scale factors reduced to the terminal/root ratio. -/
theorem selectionBudget_product_le {n : ℕ} {D : FiniteScaleSource n}
    {loss kappa : ℝ} (hd : 0 < D.thickness) (hd1 : D.thickness ≤ 1)
    (hloss : 0 ≤ loss) (hk : 0 ≤ kappa) (J stop ell : ℕ) (hJ : 0 < J) :
    ((∏j∈range (J+1),selectionBudget D loss kappa J stop ell j:ℕ):ℝ) ≤
      ((259:ℝ)^3)^ell*((2*costConstant)^(J*ell)*D.thickness^(-loss*((J*ell:ℕ):ℝ))*
        ((64/((2^stop:ℕ):ℝ))/(64/((2^(min 6 stop):ℕ):ℝ)))^(-(kappa*(ell:ℝ)))) := by
  have H := successor_capacity_product hd hd1 hloss hk (depth J stop)
    (fun _i _j hij => depth_mono J stop hij) J ell
  rw [selectionBudget_product_split]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [depth_zero,depth_last J stop hJ,depthPower_eq_relative] using H

/-- The actual master loss is 3*t. When the stopping depth is at least six,
the initial physical grain radius is exactly one. J stays an independent
input, so its explicit exponent can be budgeted before selecting t. -/
theorem native_master_product_bound {n : ℕ} {D : FiniteScaleSource n} {eta t : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (ht : 0 ≤ t)
    (J stop ell : ℕ) (hJ : 0 < J) (hstop : 6 ≤ stop) :
    ((∏j∈range (J+1),selectionBudget D (3*t) extremalExponent J stop ell j:ℕ):ℝ) ≤
      ((259:ℝ)^3)^ell*((2*costConstant)^(J*ell)*D.thickness^(-(3*t)*((J*ell:ℕ):ℝ))*
        (64/((2^stop:ℕ):ℝ))^(-(extremalExponent*(ell:ℝ)))) := by
  have H := selectionBudget_product_le h.1.2.1 h.1.2.2.1
    (show 0 ≤ 3*t by positivity) extremalExponent_nonneg J stop ell hJ
  simpa only [min_eq_left hstop,show ((2^6:ℕ):ℝ)=64 by norm_num,
    div_self (by norm_num : (64:ℝ)≠0),div_one] using H

end NativeAngularCandidateCapacityProduct
