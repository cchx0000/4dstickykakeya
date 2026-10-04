import Theorems.Thm_StickyKakeya4_native_asymmetric_scale_budget
import Theorems.Thm_StickyKakeya4_native_asymmetric_polynomial_retention
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Filter
open scoped Pointwise BigOperators
noncomputable section
namespace PlanarDyadicNumerics

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
    (hJ : 0 < J) {epsilon : ℝ} (hmargin : 2*(b : ℝ)/(J : ℝ) < epsilon) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ L : ℝ,
      1 ≤ L → L ≤ 192 * (2 : ℝ)^(2*n) →
      C * ((n : ℝ) + 5)^a * (L ^ (1 / (J : ℝ)))^b ≤
        (2 : ℝ)^(epsilon * (n : ℝ)) := by
  have hJr : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hbJ : 0 ≤ (b : ℝ)/(J : ℝ) := by positivity
  obtain ⟨n0, hn0⟩ := polynomial_absorption
    (C * (192 : ℝ)^((b : ℝ)/(J : ℝ))) a (sub_pos.mpr hmargin)
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
  push_cast at hLpow
  calc
    _ ≤ C * ((n : ℝ)+5)^a *
        ((192 : ℝ)^((b : ℝ)/(J : ℝ)) * (2 : ℝ)^((2*(n : ℝ))*((b : ℝ)/(J : ℝ)))) :=
      mul_le_mul_of_nonneg_left hLpow (mul_nonneg hC (by positivity))
    _ = (C * (192 : ℝ)^((b : ℝ)/(J : ℝ)) * ((n : ℝ)+5)^a) *
        (2 : ℝ)^((2*(n : ℝ))*((b : ℝ)/(J : ℝ))) := by ring
    _ ≤ (2 : ℝ)^((epsilon-2*(b : ℝ)/(J : ℝ))*(n : ℝ)) *
        (2 : ℝ)^((2*(n : ℝ))*((b : ℝ)/(J : ℝ))) :=
      mul_le_mul_of_nonneg_right (hn0 n hn) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
      congr 1
      ring

/-- A fixed polynomial lower density yields a retained proportion of the
form nu^K times a dyadic epsilon loss, with the mesh cutoff chosen first. -/
theorem polynomial_retention_absorption {c D : ℝ} (hc : 0 < c) (hD : 0 < D)
    (a b d J : ℕ) (hJ : 0 < J) {epsilon : ℝ}
    (hmargin : 2*(b : ℝ)/(J : ℝ) < epsilon) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ nu L p : ℝ,
      0 < nu → 1 ≤ L → L ≤ 192 * (2 : ℝ)^(2*n) →
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
    (hmargin : 2*(b : ℝ)/(J : ℝ) < epsilon) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ nu L p : ℝ,
      0 < nu → 1 ≤ L → L ≤ 192 * (2 : ℝ)^(2*n) →
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

lemma planar_floor_cover_factor (s : ℕ) (hs : 1 ≤ s) :
    (2*(s : ℝ)+3)^2 ≤ (25 : ℝ)^s := by
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 2*(s : ℝ)+3) (real_floor_cover_factor s hs) 2
  calc
    _ ≤ ((5 : ℝ)^s)^2 := hh
    _ = (25 : ℝ)^s := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num

/-- The native chain density used in the actual asymmetric construction. -/
def nativeDensity (n J : ℕ) (nu : ℝ) : ℝ :=
  SymmetryDifferenceGrowthChain.threshold ((5*nu/49)/10) J /
    (2*(NativeAsymmetricScaleBudget.budget (2*n+6) J (5*nu/49) : ℝ)+1)

def densityCoefficient (J : ℕ) : ℝ :=
  (2/((20 : ℝ)^(2^J)*(100*((2 : ℝ)^J+1)))) * (5/49 : ℝ)^(2^J+1)/3

lemma densityCoefficient_pos (J : ℕ) : 0 < densityCoefficient J := by
  unfold densityCoefficient
  positivity

lemma nativeDensity_lower (n J : ℕ) {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    densityCoefficient J * nu^(2^J+1) / ((n : ℝ)+5) ≤ nativeDensity n J nu := by
  have hnu' : 0 < 5*nu/49 := by positivity
  have hnu1' : 5*nu/49 ≤ 1 := by linarith
  have hh := NativeAsymmetricScaleBudget.density_native_lower (2*n+6) J hnu' hnu1'
  unfold nativeDensity
  apply le_trans _ hh
  unfold densityCoefficient
  have hnp : 0 < (n : ℝ)+5 := by positivity
  have hne : 0 < ((2*n+6 : ℕ):ℝ)+5 := by positivity
  have hc : 0 < (20 : ℝ)^(2^J)*(100*((2 : ℝ)^J+1)) := by positivity
  have hpow : (5*nu/49)^(2^J+1) = (5/49 : ℝ)^(2^J+1)*nu^(2^J+1) := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hpow]
  push_cast
  apply (div_le_div_iff₀ hnp (by positivity)).mpr
  field_simp
  nlinarith [show 0 ≤ nu^(2^J+1) by positivity]

lemma choose_depth {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ J : ℕ, 0 < J ∧ (696 : ℝ)/(J : ℝ) < epsilon := by
  obtain ⟨J, hJ⟩ := exists_nat_gt ((696 : ℝ)/epsilon)
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
      0 < nu → nu ≤ 1 → 1 ≤ L → L ≤ 192*(2 : ℝ)^(2*n) →
      let p := nativeDensity n J nu
      let H := L^(1/(J : ℝ))
      nu^K*(2 : ℝ)^(-(epsilon*(n : ℝ))) ≤ p^(J+4)/((2 : ℝ)^(J+4)*H) ∧
      nu^K*(2 : ℝ)^(-(epsilon*(n : ℝ))) ≤ p^1394/((2 : ℝ)^1154*H^348) ∧
      ∀ s : ℕ, 1 ≤ s →
        (2*(s : ℝ)+3)^2*(2 : ℝ)^(961*s)*H^(290*s)/p^(1161*s) ≤
          (2 : ℝ)^(epsilon*(n : ℝ)*(s : ℝ))/nu^(K*s) := by
  obtain ⟨J, hJ, hmargin⟩ := choose_depth hepsilon
  let d := 2^J+1
  let K := d * max (J+4) 1394
  have hc := densityCoefficient_pos J
  have hJr : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hxmargin : (2 : ℝ)/(J : ℝ) < epsilon :=
    (div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 696) hJr.le).trans_lt hmargin
  have hcmargin : (580 : ℝ)/(J : ℝ) < epsilon :=
    (div_le_div_of_nonneg_right (by norm_num : (580 : ℝ) ≤ 696) hJr.le).trans_lt hmargin
  obtain ⟨nx, hnx⟩ := polynomial_retention_absorption hc
    (by positivity : 0 < (2 : ℝ)^(J+4)) (J+4) 1 d J hJ (by norm_num at *; exact hxmargin)
  obtain ⟨ny, hny⟩ := polynomial_retention_absorption hc
    (by positivity : 0 < (2 : ℝ)^1154) 1394 348 d J hJ (by norm_num at *; exact hmargin)
  obtain ⟨nc, hnc⟩ := polynomial_cost_absorption hc
    (by positivity : 0 < 25*(2 : ℝ)^961) 1161 290 d J hJ (by norm_num at *; exact hcmargin)
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
  have hcostK : (25*(2 : ℝ)^961)*H^290/p^1161 ≤
      (2 : ℝ)^(epsilon*(n : ℝ))/nu^K :=
    hcost.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hnuKc)
  have hpower := pow_le_pow_left₀ (by positivity :
      0 ≤ (25*(2 : ℝ)^961)*H^290/p^1161) hcostK s
  calc
    _ ≤ (25 : ℝ)^s*(2 : ℝ)^(961*s)*H^(290*s)/p^(1161*s) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (planar_floor_cover_factor s hs) (by positivity))
          (by positivity)) (by positivity)
    _ = ((25*(2 : ℝ)^961)*H^290/p^1161)^s := by
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
      0 < nu → nu ≤ 1 → 1 ≤ L → L ≤ 192*(2 : ℝ)^(2*n) →
      let delta := ((2 : ℝ)^n)⁻¹
      let p := nativeDensity n J nu
      let H := L^(1/(J : ℝ))
      nu^K*delta^epsilon ≤ p^(J+4)/((2 : ℝ)^(J+4)*H) ∧
      nu^K*delta^epsilon ≤ p^1394/((2 : ℝ)^1154*H^348) ∧
      ∀ s : ℕ, 1 ≤ s →
        (2*(s : ℝ)+3)^2*(2 : ℝ)^(961*s)*H^(290*s)/p^(1161*s) ≤
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

end PlanarDyadicNumerics
