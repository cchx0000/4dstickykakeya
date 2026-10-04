import Theorems.Thm_StickyKakeya4_native_asymmetric_scale_budget
import Theorems.Thm_StickyKakeya4_native_asymmetric_polynomial_retention
import Theorems.Thm_StickyKakeya4_original_real_asymmetric_construction
import Theorems.Thm_StickyKakeya4_separated_dyadic_cardinality
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Filter
open scoped Pointwise BigOperators
noncomputable section
namespace AsymmetricDyadicAbsorption

/-- Every fixed polynomial in the mesh level is eventually smaller than any
positive dyadic exponential. The threshold depends only on C, a, eta. -/
theorem polynomial_absorption (C : ℝ) (a : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      C * ((n : ℝ) + 5)^a ≤ (2 : ℝ)^(eta * (n : ℝ)) := by
  let r : ℝ := Real.log 2 * eta
  have hr : 0 < r := mul_pos (Real.log_pos (by norm_num)) heta
  have hlim : Tendsto (fun n : ℕ =>
      Real.exp (r * ((n : ℝ) + 5)) / ((n : ℝ) + 5)^(a : ℝ)) atTop atTop :=
    (tendsto_exp_mul_div_rpow_atTop (a : ℝ) r hr).comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (eventually_ge_atTop (C * Real.exp (r * 5))))
  refine ⟨n0, fun n hn => ?_⟩
  have hnpos : 0 < (n : ℝ) + 5 := by positivity
  have hb := (le_div_iff₀ (Real.rpow_pos_of_pos hnpos _)).mp (hn0 n hn)
  rw [Real.rpow_natCast, mul_add, Real.exp_add] at hb
  have hb' : C * ((n : ℝ) + 5)^a ≤ Real.exp (r * (n : ℝ)) := by
    apply (mul_le_mul_iff_left₀ (Real.exp_pos (r * 5))).mp
    nlinarith [hb]
  convert hb' using 1
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  dsimp [r]
  ring

/-- The slow chain factor consumes b/J of the dyadic exponent; all
polynomial and constant losses are absorbed by the remaining margin. -/
theorem slow_factor_absorption (C : ℝ) (hC : 0 ≤ C) (a b J : ℕ)
    (hJ : 0 < J) {epsilon : ℝ} (hmargin : (b : ℝ)/(J : ℝ) < epsilon) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ L : ℝ,
      1 ≤ L → L ≤ 3 * (2 : ℝ)^n →
      C * ((n : ℝ) + 5)^a * (L ^ (1 / (J : ℝ)))^b ≤
        (2 : ℝ)^(epsilon * (n : ℝ)) := by
  have hJr : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hbJ : 0 ≤ (b : ℝ)/(J : ℝ) := by positivity
  obtain ⟨n0, hn0⟩ := polynomial_absorption
    (C * (3 : ℝ)^((b : ℝ)/(J : ℝ))) a (sub_pos.mpr hmargin)
  refine ⟨n0, fun n hn L hL hLbound => ?_⟩
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hroot : (L^(1/(J : ℝ)))^b = L^((b : ℝ)/(J : ℝ)) := by
    rw [← Real.rpow_mul_natCast hLp.le]
    congr 1
    ring
  rw [hroot]
  have hLpow := Real.rpow_le_rpow hLp.le hLbound hbJ
  rw [Real.mul_rpow (by norm_num) (by positivity),
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)] at hLpow
  calc
    _ ≤ C * ((n : ℝ)+5)^a *
        ((3 : ℝ)^((b : ℝ)/(J : ℝ)) * (2 : ℝ)^((n : ℝ)*((b : ℝ)/(J : ℝ)))) :=
      mul_le_mul_of_nonneg_left hLpow (mul_nonneg hC (by positivity))
    _ = (C * (3 : ℝ)^((b : ℝ)/(J : ℝ)) * ((n : ℝ)+5)^a) *
        (2 : ℝ)^((n : ℝ)*((b : ℝ)/(J : ℝ))) := by ring
    _ ≤ (2 : ℝ)^((epsilon-(b : ℝ)/(J : ℝ))*(n : ℝ)) *
        (2 : ℝ)^((n : ℝ)*((b : ℝ)/(J : ℝ))) :=
      mul_le_mul_of_nonneg_right (hn0 n hn) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
      congr 1
      ring

/-- A fixed polynomial lower density yields a retained proportion of the
form nu^K times a dyadic epsilon loss, with the mesh cutoff chosen first. -/
theorem polynomial_retention_absorption {c D : ℝ} (hc : 0 < c) (hD : 0 < D)
    (a b d J : ℕ) (hJ : 0 < J) {epsilon : ℝ}
    (hmargin : (b : ℝ)/(J : ℝ) < epsilon) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ nu L p : ℝ,
      0 < nu → 1 ≤ L → L ≤ 3 * (2 : ℝ)^n →
      c * nu^d / ((n : ℝ)+5) ≤ p →
      nu^(d*a) * (2 : ℝ)^(-(epsilon * (n : ℝ))) ≤
        p^a / (D * (L^(1/(J : ℝ)))^b) := by
  obtain ⟨n0, hn0⟩ := slow_factor_absorption (D/c^a) (by positivity)
    a b J hJ hmargin
  refine ⟨n0, fun n hn nu L p hnu hL hLbound hp => ?_⟩
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hnpos : 0 < (n : ℝ)+5 := by positivity
  have hroot : 0 < L^(1/(J : ℝ)) := Real.rpow_pos_of_pos hLp _
  have hden : 0 < D/c^a * ((n : ℝ)+5)^a * (L^(1/(J : ℝ)))^b := by positivity
  have habs := hn0 n hn L hL hLbound
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ c*nu^d/((n : ℝ)+5)) hp a
  calc
    _ = nu^(d*a)/(2 : ℝ)^(epsilon*(n : ℝ)) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]
    _ ≤ nu^(d*a)/(D/c^a * ((n : ℝ)+5)^a * (L^(1/(J : ℝ)))^b) :=
      div_le_div_of_nonneg_left (by positivity) hden habs
    _ = (c*nu^d/((n : ℝ)+5))^a / (D*(L^(1/(J : ℝ)))^b) := by
      rw [div_pow, mul_pow, ← pow_mul]
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hpow (by positivity)

/-- Reciprocal form used for the actual sumset growth cost. -/
theorem polynomial_cost_absorption {c D : ℝ} (hc : 0 < c) (hD : 0 < D)
    (a b d J : ℕ) (hJ : 0 < J) {epsilon : ℝ}
    (hmargin : (b : ℝ)/(J : ℝ) < epsilon) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ nu L p : ℝ,
      0 < nu → 1 ≤ L → L ≤ 3 * (2 : ℝ)^n →
      c * nu^d / ((n : ℝ)+5) ≤ p →
      D * (L^(1/(J : ℝ)))^b / p^a ≤
        (2 : ℝ)^(epsilon * (n : ℝ)) / nu^(d*a) := by
  obtain ⟨n0, hn0⟩ := polynomial_retention_absorption hc hD a b d J hJ hmargin
  refine ⟨n0, fun n hn nu L p hnu hL hLbound hp => ?_⟩
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hh := hn0 n hn nu L p hnu hL hLbound hp
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← div_eq_mul_inv] at hh
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hroot : 0 < L^(1/(J : ℝ)) := Real.rpow_pos_of_pos hLp _
  have hmul := (div_le_div_iff₀ (by positivity) (by positivity)).mp hh
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [hmul]

lemma real_floor_cover_factor (s : ℕ) (hs : 1 ≤ s) :
    (2*(s : ℝ)+3) ≤ (5 : ℝ)^s := by
  have hh : ∀ k : ℕ, 2*(k : ℝ)+5 ≤ (5 : ℝ)^(k+1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      nlinarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  convert hh k using 1
  push_cast
  ring

/-- The native chain density used in the actual asymmetric construction. -/
def nativeDensity (n J : ℕ) (nu : ℝ) : ℝ :=
  SymmetryDifferenceGrowthChain.threshold (nu/10) J /
    (2*(NativeAsymmetricScaleBudget.budget n J nu : ℝ)+1)

def densityCoefficient (J : ℕ) : ℝ :=
  2/((20 : ℝ)^(2^J)*(100*((2 : ℝ)^J+1)))

lemma densityCoefficient_pos (J : ℕ) : 0 < densityCoefficient J := by
  unfold densityCoefficient
  positivity

lemma nativeDensity_lower (n J : ℕ) {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    densityCoefficient J * nu^(2^J+1) / ((n : ℝ)+5) ≤ nativeDensity n J nu := by
  have hh := NativeAsymmetricScaleBudget.density_native_lower n J hnu hnu1
  unfold nativeDensity
  convert hh using 1
  unfold densityCoefficient
  field_simp

lemma choose_depth {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ J : ℕ, 0 < J ∧ (348 : ℝ)/(J : ℝ) < epsilon := by
  obtain ⟨J, hJ⟩ := exists_nat_gt ((348 : ℝ)/epsilon)
  have hJr : 0 < (J : ℝ) := lt_trans (by positivity) hJ
  refine ⟨J, by exact_mod_cast hJr, ?_⟩
  apply (div_lt_iff₀ hJr).mpr
  have hh := (div_lt_iff₀ hepsilon).mp hJ
  nlinarith

/-- Complete numerical absorption for the original X retention, original Y
retention, and every iterated real-grid cover. The chosen mesh threshold
is independent of both the native energy parameter nu and multiplicity s. -/
theorem native_absorption {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ J K n0 : ℕ, 0 < J ∧ 0 < K ∧
      ∀ n : ℕ, n0 ≤ n → ∀ nu L : ℝ,
      0 < nu → nu ≤ 1 → 1 ≤ L → L ≤ 3*(2 : ℝ)^n →
      let p := nativeDensity n J nu
      let H := L^(1/(J : ℝ))
      nu^K*(2 : ℝ)^(-(epsilon*(n : ℝ))) ≤ p^(J+4)/((2 : ℝ)^(J+4)*H) ∧
      nu^K*(2 : ℝ)^(-(epsilon*(n : ℝ))) ≤ p^1394/((2 : ℝ)^1154*H^348) ∧
      ∀ s : ℕ, 1 ≤ s →
        (2*(s : ℝ)+3)*(2 : ℝ)^(961*s)*H^(290*s)/p^(1161*s) ≤
          (2 : ℝ)^(epsilon*(n : ℝ)*(s : ℝ))/nu^(K*s) := by
  obtain ⟨J, hJ, hmargin⟩ := choose_depth hepsilon
  let d := 2^J+1
  let K := d * max (J+4) 1394
  have hc := densityCoefficient_pos J
  have hJr : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hxmargin : (1 : ℝ)/(J : ℝ) < epsilon :=
    (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 348) hJr.le).trans_lt hmargin
  have hcmargin : (290 : ℝ)/(J : ℝ) < epsilon :=
    (div_le_div_of_nonneg_right (by norm_num : (290 : ℝ) ≤ 348) hJr.le).trans_lt hmargin
  obtain ⟨nx, hnx⟩ := polynomial_retention_absorption hc
    (by positivity : 0 < (2 : ℝ)^(J+4)) (J+4) 1 d J hJ (by simpa only [Nat.cast_one] using hxmargin)
  obtain ⟨ny, hny⟩ := polynomial_retention_absorption hc
    (by positivity : 0 < (2 : ℝ)^1154) 1394 348 d J hJ (by simpa only [Nat.cast_ofNat] using hmargin)
  obtain ⟨nc, hnc⟩ := polynomial_cost_absorption hc
    (by positivity : 0 < 5*(2 : ℝ)^961) 1161 290 d J hJ (by simpa only [Nat.cast_ofNat] using hcmargin)
  have hKx : d*(J+4) ≤ K := Nat.mul_le_mul_left d (le_max_left _ _)
  have hKy : d*1394 ≤ K := Nat.mul_le_mul_left d (le_max_right _ _)
  have hKc : d*1161 ≤ K := (Nat.mul_le_mul_left d (by omega : 1161 ≤ 1394)).trans hKy
  refine ⟨J, K, max nx (max ny nc), hJ, ?_, ?_⟩
  · dsimp [K, d]
    positivity
  intro n hn nu L hnu hnu1 hL hLbound
  let p := nativeDensity n J nu
  let H := L^(1/(J : ℝ))
  have hp := nativeDensity_lower n J hnu hnu1
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity :
    0 < densityCoefficient J * nu^(2^J+1)/((n : ℝ)+5)) hp
  have hH : 0 < H := Real.rpow_pos_of_pos (zero_lt_one.trans_le hL) _
  have hnuKx : nu^K ≤ nu^(d*(J+4)) := pow_le_pow_of_le_one hnu.le hnu1 hKx
  have hnuKy : nu^K ≤ nu^(d*1394) := pow_le_pow_of_le_one hnu.le hnu1 hKy
  have hnuKc : nu^K ≤ nu^(d*1161) := pow_le_pow_of_le_one hnu.le hnu1 hKc
  have hx := hnx n (by omega) nu L p hnu hL hLbound hp
  have hy := hny n (by omega) nu L p hnu hL hLbound hp
  have hcost := hnc n (by omega) nu L p hnu hL hLbound hp
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right hnuKx (by positivity)).trans (by simpa only [pow_one] using hx)
  · exact (mul_le_mul_of_nonneg_right hnuKy (by positivity)).trans hy
  intro s hs
  have hcostK : (5*(2 : ℝ)^961)*H^290/p^1161 ≤
      (2 : ℝ)^(epsilon*(n : ℝ))/nu^K :=
    hcost.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hnuKc)
  have hpower := pow_le_pow_left₀ (by positivity :
      0 ≤ (5*(2 : ℝ)^961)*H^290/p^1161) hcostK s
  calc
    _ ≤ (5 : ℝ)^s*(2 : ℝ)^(961*s)*H^(290*s)/p^(1161*s) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (real_floor_cover_factor s hs) (by positivity))
          (by positivity)) (by positivity)
    _ = ((5*(2 : ℝ)^961)*H^290/p^1161)^s := by
      rw [div_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
    _ ≤ ((2 : ℝ)^(epsilon*(n : ℝ))/nu^K)^s := hpower
    _ = _ := by
      rw [div_pow, ← pow_mul, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]

lemma dyadic_mesh_rpow (n : ℕ) (t : ℝ) :
    (((2 : ℝ)^n)⁻¹)^t = (2 : ℝ)^(-(t*(n : ℝ))) := by
  rw [← Real.rpow_neg_eq_inv_rpow,
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- Source-format dyadic epsilon/nu absorption. This is the numerical
interface to the unconditional original-real-subset construction. -/
theorem native_dyadic_absorption {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ J K n0 : ℕ, 0 < J ∧ 0 < K ∧
      ∀ n : ℕ, n0 ≤ n → ∀ nu L : ℝ,
      0 < nu → nu ≤ 1 → 1 ≤ L → L ≤ 3*(2 : ℝ)^n →
      let delta := ((2 : ℝ)^n)⁻¹
      let p := nativeDensity n J nu
      let H := L^(1/(J : ℝ))
      nu^K*delta^epsilon ≤ p^(J+4)/((2 : ℝ)^(J+4)*H) ∧
      nu^K*delta^epsilon ≤ p^1394/((2 : ℝ)^1154*H^348) ∧
      ∀ s : ℕ, 1 ≤ s →
        (2*(s : ℝ)+3)*(2 : ℝ)^(961*s)*H^(290*s)/p^(1161*s) ≤
          delta^(-epsilon*(s : ℝ))/nu^(K*s) := by
  obtain ⟨J, K, n0, hJ, hK, hh⟩ := native_absorption hepsilon
  refine ⟨J, K, n0, hJ, hK, fun n hn nu L hnu hnu1 hL hLbound => ?_⟩
  obtain ⟨hx, hy, hc⟩ := hh n hn nu L hnu hnu1 hL hLbound
  dsimp only
  rw [dyadic_mesh_rpow]
  refine ⟨hx, hy, fun s hs => ?_⟩
  rw [dyadic_mesh_rpow]
  convert hc s hs using 1
  congr 2
  ring

open ActualRoundedAdditiveEnergy SymmetryDifferenceGrowthChain

/-- Native dyadic asymmetric BSG on the ORIGINAL real labels. Neither a
cardinality budget nor a density/sumset estimate is an input: each is
constructed from the bounded separated sources and their literal closed
near-difference energy. The mesh cutoff is uniform in 0 < nu <= 1. -/
theorem original_real_dyadic_bsg {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ K n0 : ℕ, 0 < K ∧ ∀ n : ℕ, n0 ≤ n →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ X Y : Finset ℝ, X.Nonempty → Y.Nonempty →
      (∀ x ∈ X, |x| ≤ 4) → (∀ y ∈ Y, |y| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → ((2 : ℝ)^n)⁻¹ ≤ |x-y|) →
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → ((2 : ℝ)^n)⁻¹ ≤ |x-y|) →
      nu*(X.card : ℝ)^2*(Y.card : ℝ) ≤
        (nearDifferenceEnergy X Y (((2 : ℝ)^n)⁻¹) : ℝ) →
      ∃ X' Y' : Finset ℝ, X' ⊆ X ∧ Y' ⊆ Y ∧
        nu^K * (((2 : ℝ)^n)⁻¹)^epsilon * (X.card : ℝ) ≤ X'.card ∧
        nu^K * (((2 : ℝ)^n)⁻¹)^epsilon * (Y.card : ℝ) ≤ Y'.card ∧
        ∀ u v : ℕ,
          (((Y'+u•X'-v•X').image (rounded (((2 : ℝ)^n)⁻¹))).card : ℝ) ≤
            ((((2 : ℝ)^n)⁻¹)^(-epsilon*((u+v : ℕ) : ℝ))/nu^(K*(u+v)))*
              (Y.card : ℝ) := by
  classical
  obtain ⟨J, K, n0, hJ, hK, habs⟩ := native_dyadic_absorption hepsilon
  refine ⟨K, n0, hK, ?_⟩
  intro n hn nu hnu hnu1 X Y hX hY hXbound hYbound hXsep hYsep he
  let delta : ℝ := ((2 : ℝ)^n)⁻¹
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  let Xbar := X.image (rounded delta)
  let Ybar := Y.image (rounded delta)
  have hXbar : Xbar.Nonempty := hX.image _
  have hYbar : Ybar.Nonempty := hY.image _
  have hXC : Xbar.card = X.card := rounded_card X hdelta hXsep
  have hYC : Ybar.card = Y.card := rounded_card Y hdelta hYsep
  have hXcard := SeparatedDyadicCardinality.original_cardinality_bound X n 4 hXsep hXbound
  have hYcard := SeparatedDyadicCardinality.original_cardinality_bound Y n 1 hYsep (by simpa only [Nat.cast_one] using hYbound)
  have hXbudget : (Xbar.card : ℝ) ≤ 9*(2 : ℝ)^n := by
    rw [hXC]
    exact_mod_cast hXcard
  have hYbudget : (Ybar.card : ℝ) ≤ 3*(2 : ℝ)^n := by
    rw [hYC]
    exact_mod_cast hYcard
  let R := NativeAsymmetricScaleBudget.budget n J nu
  let p := nativeDensity n J nu
  let L := sizeRatio Ybar Xbar
  let H := L^((J : ℝ)⁻¹)
  have hb := NativeAsymmetricScaleBudget.native_card_budget n J hnu hXbudget hYbudget
  have hXB : Xbar.card ≤ 2^R := by exact_mod_cast hb.1
  have hYB : (Ybar.card : ℝ)/threshold (nu/10) J ≤ (2 : ℝ)^R := hb.2
  have ha : 0 < nu/10 := div_pos hnu (by norm_num)
  have hround := rounded_energy_density X Y hdelta hXsep hYsep he
  have he' : 2*(nu/10)*(Ybar.card : ℝ)*(Xbar.card : ℝ)^2 ≤
      (Finset.addEnergy Ybar Xbar : ℝ) := by
    calc
      _ = (nu/5)*(Xbar.card : ℝ)^2*(Ybar.card : ℝ) := by ring
      _ ≤ (Finset.addEnergy Xbar Ybar : ℝ) := hround
      _ = _ := by rw [Finset.addEnergy_comm]
  have hr := SymmetryChainUniformDensity.common_threshold_range Ybar Xbar ha hYbar hXbar he' J R
  have hp0 : 0 < p := hr.1
  have hp1 : p ≤ 1 := hr.2.1
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hH : 0 < H := Real.rpow_pos_of_pos hLpos _
  have hXone : 1 ≤ (Xbar.card : ℝ) := by exact_mod_cast hXbar.card_pos
  have hXpos : 0 < (Xbar.card : ℝ) := zero_lt_one.trans_le hXone
  have hLbudget : L ≤ 3*(2 : ℝ)^n := by
    apply max_le
    · have hpw := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)
      linarith
    · apply (div_le_iff₀ hXpos).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hXone) (by positivity : 0 ≤ 3*(2 : ℝ)^n)]
  obtain ⟨hnumX, hnumY, hnumC⟩ := habs n hn nu L hnu hnu1 hL1 hLbudget
  simp only [one_div] at hnumX hnumY hnumC
  obtain ⟨j, X', Y', hj1, hjJ, hXX, hYY, hkap, hkap1, hC1, htheta,
      _hCcost, hXsize, hYsize, hcover⟩ :=
    OriginalRealAsymmetricConstruction.original_real_subsets X Y hX hY
      hdelta hnu hXsep hYsep he hJ
  let kappa := (density Ybar Xbar (nu/10) j)^2 / slowFactor Ybar Xbar (nu/10) J
  let C := BalancedBSGIterationCore.growthConstant kappa
  let t := threshold (nu/10) (j-1)
  let theta := t/(2*C)
  have hkaplower : p^4/H ≤ kappa :=
    SymmetrySlowFactorBudget.chain_balanced_density_lower Ybar Xbar ha hYbar hXbar he'
      J R hJ hXB hYB j hjJ
  have hcost : C*p^232 ≤ (2 : ℝ)^192*H^58 :=
    SymmetrySlowFactorBudget.growth_cost_budget hp0 hLpos hkap hkap1 hkaplower
  have hpt : p ≤ t := hr.2.2 (j-1) (by omega)
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have ht : 0 < t := hp0.trans_le hpt
  have hproduct : ∀ i < j, p ≤ density Ybar Xbar (nu/10) i := by
    intro i hi
    exact SymmetryChainUniformDensity.common_density_lower Ybar Xbar ha hYbar hXbar he'
      J R hXB hYB i (by omega)
  have hretX := NativeAsymmetricPolynomialRetention.original_x_retention hp0 hp1 hH
    hkaplower (density Ybar Xbar (nu/10)) hjJ hproduct
  have hdenX : (16 : ℝ)*2^J*H = (2 : ℝ)^(J+4)*H := by
    rw [pow_add, show (2 : ℝ)^4 = 16 by norm_num]
    ring
  rw [hdenX] at hretX
  have hretY := NativeAsymmetricPolynomialRetention.original_y_retention hp0 hH
    (by positivity : 0 < (2 : ℝ)^192) hCpos hpt hcost
  have hdenY : 4*((2 : ℝ)^192)^6*H^348 = (2 : ℝ)^1154*H^348 := by
    rw [← pow_mul, show (4 : ℝ) = (2 : ℝ)^2 by norm_num, ← pow_add]
  rw [hdenY] at hretY
  refine ⟨X', Y', hXX, hYY, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (hnumX.trans hretX) (Nat.cast_nonneg _)).trans hXsize
  · exact (mul_le_mul_of_nonneg_right (hnumY.trans hretY) (Nat.cast_nonneg _)).trans hYsize
  intro u v
  by_cases hs0 : u+v = 0
  · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp hs0
    simp only [zero_nsmul, add_zero, sub_zero, Nat.cast_zero, mul_zero,
      Real.rpow_zero, pow_zero, div_one, one_mul]
    exact Nat.cast_le.mpr ((Finset.card_image_le).trans (Finset.card_le_card hYY))
  have hs : 1 ≤ u+v := by omega
  have hiter := NativeAsymmetricPolynomialRetention.iterated_cost_budget hp0 hp1 hC1 hpt hcost (u+v) hs
  have hconst : 2*((2 : ℝ)^192)^(5*(u+v)) ≤ (2 : ℝ)^(961*(u+v)) := by
    calc
      _ = (2 : ℝ)^(960*(u+v)+1) := by
        rw [← pow_mul, show 192*(5*(u+v)) = 960*(u+v) by omega, pow_succ]
        ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hiter' : 2*C^(2*(u+v)+3)/t ≤
      (2 : ℝ)^(961*(u+v))*H^(290*(u+v))/p^(1161*(u+v)) :=
    hiter.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconst (by positivity)) (by positivity))
  have hcosteq : C^(2*(u+v+1))/theta = 2*C^(2*(u+v)+3)/t := by
    have heq : C^(2*(u+v)+3) = C^(2*(u+v+1))*C := by
      rw [← pow_succ]
      congr 1
    rw [heq]
    dsimp [theta]
    field_simp
  have hfloor : ((2*(u+v+1)+1 : ℕ) : ℝ) = 2*((u+v : ℕ) : ℝ)+3 := by
    push_cast
    ring
  have hcover' : (((Y'+u•X'-v•X').image (rounded delta)).card : ℝ) ≤
      (2*((u+v : ℕ) : ℝ)+3)*(2*C^(2*(u+v)+3)/t)*(Y.card : ℝ) := by
    have hh := hcover u v
    change _ ≤ ((2*(u+v+1)+1 : ℕ) : ℝ)*(C^(2*(u+v+1))/theta)*(Y.card : ℝ) at hh
    rw [hcosteq, hfloor] at hh
    exact hh
  calc
    _ ≤ (2*((u+v : ℕ) : ℝ)+3)*(2*C^(2*(u+v)+3)/t)*(Y.card : ℝ) := hcover'
    _ ≤ ((2*((u+v : ℕ) : ℝ)+3)*(2 : ℝ)^(961*(u+v))*H^(290*(u+v))/p^(1161*(u+v)))*
        (Y.card : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hiter' (by positivity : 0 ≤ 2*((u+v : ℕ) : ℝ)+3))
        (Nat.cast_nonneg Y.card)
      simpa only [mul_div_assoc, mul_assoc] using hh
    _ ≤ _ := mul_le_mul_of_nonneg_right (hnumC (u+v) hs) (Nat.cast_nonneg _)

end AsymmetricDyadicAbsorption
