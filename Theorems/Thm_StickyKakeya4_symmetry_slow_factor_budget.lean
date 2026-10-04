import Theorems.Thm_StickyKakeya4_symmetry_chain_uniform_density
import Theorems.Thm_StickyKakeya4_balanced_bsg_polynomial_loss

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

namespace SymmetrySlowFactorBudget

/-- The sole cardinality-ratio loss is its J-th root. Every density loss is
bounded separately by an ordinary fixed power of the common p budget. -/
theorem root_factor_le {p L t d : ℝ} {J : ℕ}
    (hp : 0<p) (hp1 : p≤1) (hL : 1≤L) (hpt : p≤t) (hpd : p≤d) (hJ : 0<J) :
    (L/(t*d))^((J:ℝ)⁻¹) ≤ L^((J:ℝ)⁻¹)/p^2 := by
  have hL0 : 0≤L := zero_le_one.trans hL
  have hp2 : 0<p^2 := sq_pos_of_pos hp
  have htd : p^2≤t*d := by nlinarith [mul_nonneg (sub_nonneg.mpr hpt) (sub_nonneg.mpr hpd)]
  have htdpos : 0<t*d := hp2.trans_le htd
  have hdiv : L/(t*d)≤L/p^2 := div_le_div_of_nonneg_left hL0 hp2 htd
  have he0 : 0≤(J:ℝ)⁻¹ := by positivity
  have hJ1 : 1≤(J:ℝ) := by exact_mod_cast hJ
  have hJp : 0<(J:ℝ) := by exact_mod_cast hJ
  have he1 : (J:ℝ)⁻¹≤1 := (inv_le_one₀ hJp).mpr hJ1
  have hpp : p^2≤1 := by nlinarith
  have hpow : p^2≤(p^2)^((J:ℝ)⁻¹) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hp2 hpp he1
  calc
    _ ≤ (L/p^2)^((J:ℝ)⁻¹) := Real.rpow_le_rpow (div_nonneg hL0 htdpos.le) hdiv he0
    _ = L^((J:ℝ)⁻¹)/(p^2)^((J:ℝ)⁻¹) := Real.div_rpow hL0 hp2.le _
    _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hL0 _) hp2 hpow

theorem balanced_density_lower {p L t d sigma : ℝ} {J : ℕ}
    (hp : 0<p) (hp1 : p≤1) (hL : 1≤L) (hpt : p≤t) (hpd : p≤d)
    (hps : p ≤ sigma) (hJ : 0<J) :
    p^4/L^((J:ℝ)⁻¹) ≤ sigma^2/((L/(t*d))^((J:ℝ)⁻¹)) := by
  have hLpos : 0<L := zero_lt_one.trans_le hL
  have hrootpos : 0<L^((J:ℝ)⁻¹) := Real.rpow_pos_of_pos hLpos _
  have htdpos : 0<t*d := mul_pos (hp.trans_le hpt) (hp.trans_le hpd)
  have hQpos : 0<(L/(t*d))^((J:ℝ)⁻¹) := Real.rpow_pos_of_pos (div_pos hLpos htdpos) _
  have hQ := (le_div_iff₀ (sq_pos_of_pos hp)).mp (root_factor_le hp hp1 hL hpt hpd hJ)
  have hsquare : p^2 ≤ sigma^2 := pow_le_pow_left₀ hp.le hps 2
  apply (div_le_div_iff₀ hrootpos hQpos).mpr
  calc
    _ = p^2*((L/(t*d))^((J:ℝ)⁻¹)*p^2) := by ring
    _ ≤ p^2*L^((J:ℝ)⁻¹) := mul_le_mul_of_nonneg_left hQ (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hsquare hrootpos.le

/-- Actual chain caller: the p budget is derived from original cardinalities. -/
theorem chain_balanced_density_lower
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (Y X : Finset G) {a : ℝ} (ha : 0<a) (hY : Y.Nonempty) (hX : X.Nonempty)
    (he : 2*a*(Y.card : ℝ)*(X.card : ℝ)^2 ≤ (Finset.addEnergy Y X : ℝ))
    (J R : ℕ) (hJ : 0<J) (hXB : X.card≤2^R)
    (hYB : (Y.card : ℝ)/SymmetryDifferenceGrowthChain.threshold a J≤(2:ℝ)^R)
    (i : ℕ) (hi : i≤J) :
    let p := SymmetryDifferenceGrowthChain.threshold a J/(2*(R:ℝ)+1)
    p^4/(SymmetryDifferenceGrowthChain.sizeRatio Y X)^((J:ℝ)⁻¹) ≤
      (SymmetryDifferenceGrowthChain.density Y X a i)^2 /
        SymmetryDifferenceGrowthChain.slowFactor Y X a J := by
  have hr := SymmetryChainUniformDensity.common_threshold_range Y X ha hY hX he J R
  have hd0 := SymmetryChainUniformDensity.common_density_lower Y X ha hY hX he J R hXB hYB 0 (by omega)
  have hdi := SymmetryChainUniformDensity.common_density_lower Y X ha hY hX he J R hXB hYB i hi
  exact balanced_density_lower hr.1 hr.2.1 (le_max_left _ _) (hr.2.2 J le_rfl) hd0 hdi hJ

/-- Polynomial balanced-growth cost, with the slow cardinality ratio paid
only to power 58/J. This cross-multiplied form has no hidden inverse premise. -/
theorem growth_cost_budget {p L kappa : ℝ} {J : ℕ}
    (hp : 0<p) (hL : 0<L) (hkap : 0<kappa) (hkap1 : kappa≤1)
    (hlower : p^4/L^((J:ℝ)⁻¹)≤kappa) :
    BalancedBSGIterationCore.growthConstant kappa * p^232 ≤
      (2:ℝ)^192 * (L^((J:ℝ)⁻¹))^58 := by
  have hroot : 0<L^((J:ℝ)⁻¹) := Real.rpow_pos_of_pos hL _
  have hl := (div_le_iff₀ hroot).mp hlower
  have hpow := pow_le_pow_left₀ (pow_nonneg hp.le 4) hl 58
  have hpow' : p^232 ≤ kappa^58*(L^((J:ℝ)⁻¹))^58 := by
    simpa only [mul_pow, ← pow_mul] using hpow
  have hK0 : 0≤BalancedBSGIterationCore.growthConstant kappa := sq_nonneg _
  calc
    _ ≤ BalancedBSGIterationCore.growthConstant kappa *
        (kappa^58*(L^((J:ℝ)⁻¹))^58) := mul_le_mul_of_nonneg_left hpow' hK0
    _ = (BalancedBSGIterationCore.growthConstant kappa*kappa^58)*
        (L^((J:ℝ)⁻¹))^58 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (BalancedBSGPolynomialLoss.growth_constant_polynomial hkap hkap1) (by positivity)

end SymmetrySlowFactorBudget
