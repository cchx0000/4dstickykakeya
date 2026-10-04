import Theorems.Thm_StickyKakeya4_symmetry_slow_factor_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace NativeAsymmetricPolynomialRetention

lemma retained_product_lower {p : ℝ} (hp : 0<p) (hp1 : p ≤ 1)
    (sigma : ℕ → ℝ) {j J : ℕ} (hj : j ≤ J)
    (hsigma : ∀ i<j, p ≤ sigma i) :
    (p/2)^J  ≤  ∏ i ∈ Finset.range j, sigma i/2 := by
  have hb : 0  ≤  p/2 := by positivity
  have hb1 : p/2  ≤  1 := by linarith
  calc
    _  ≤  (p/2)^j := pow_le_pow_of_le_one hb hb1 hj
    _ = ∏ _i ∈ Finset.range j, p/2 := by simp [div_pow]
    _  ≤  _ := Finset.prod_le_prod (fun _ _ => hb)
      (fun i hi => div_le_div_of_nonneg_right (hsigma i (Finset.mem_range.mp hi)) (by norm_num))

/-- The original X-retention loses the chain depth once, not at every inverse
pullback. All stage densities are those of the actual original chain. -/
theorem original_x_retention {p R kappa : ℝ} (hp : 0<p) (hp1 : p ≤ 1)
    (hR : 0<R) (hk : p^4/R  ≤  kappa)
    (sigma : ℕ → ℝ) {j J : ℕ} (hj : j ≤ J)
    (hsigma : ∀ i<j, p ≤ sigma i) :
    p^(J+4)/((16:ℝ)*2^J*R)  ≤ 
      (kappa/16)*(∏ i ∈ Finset.range j, sigma i/2) := by
  have hprod := retained_product_lower hp hp1 sigma hj hsigma
  have hk0 : 0 ≤ kappa := (by positivity : 0 ≤ p^4/R).trans hk
  calc
    _ = ((p^4/R)/16)*(p/2)^J := by rw [div_pow,pow_add]; field_simp
    _  ≤  (kappa/16)*(p/2)^J :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hk (by norm_num)) (by positivity)
    _  ≤  _ := mul_le_mul_of_nonneg_left hprod (div_nonneg hk0 (by norm_num))

lemma growth_power_budget {p R A K : ℝ} (hp : 0 ≤ p) (hK : 0 ≤ K) (hbound : K*p^232  ≤  A*R^58) (n : ℕ) :
    K^n*p^(232*n)  ≤  A^n*R^(58*n) := by
  have h := pow_le_pow_left₀ (mul_nonneg hK (pow_nonneg hp _)) hbound n
  simpa only [mul_pow,←pow_mul] using h

/-- Retention of the actual original Y set has a fixed polynomial energy
loss; no original-cardinality ratio is paid repeatedly. -/
theorem original_y_retention {p R A K t : ℝ} (hp : 0<p) (hR : 0<R)
    (hA : 0<A) (hK : 0<K) (hpt : p ≤ t) (hbound : K*p^232  ≤  A*R^58) :
    p^1394/(4*A^6*R^348)  ≤  (t/(2*K))^2/K^4 := by
  have hg := growth_power_budget hp.le hK.le hbound 6
  norm_num only [Nat.mul] at hg
  have hsq : p^2 ≤ t^2 := pow_le_pow_left₀ hp.le hpt 2
  have hpowers : p^1394*K^6  ≤  t^2*(A^6*R^348) := by
    calc
      _ = p^2*(K^6*p^1392) := by rw [show (1394:ℕ)=2+1392 by omega,pow_add]; ring
      _  ≤  p^2*(A^6*R^348) := mul_le_mul_of_nonneg_left hg (sq_nonneg p)
      _  ≤  _ := mul_le_mul_of_nonneg_right hsq (by positivity)
  have heq : (t/(2*K))^2/K^4 = t^2/(4*K^6) := by field_simp; ring
  rw [heq]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  convert mul_le_mul_of_nonneg_left hpowers (show (0:ℝ) ≤ 4 by norm_num) using 1 <;> ring

/-- A linear-in-s bound for every s=n+m>=1, with explicit p exponent1161s.
The external real-grid conversion only adds its proved factor2s+3. -/
theorem iterated_cost_budget {p R A K t : ℝ} (hp : 0<p) (hp1 : p ≤ 1)
    (hK1 : 1 ≤ K) (hpt : p ≤ t)
    (hbound : K*p^232  ≤  A*R^58) (s : ℕ) (hs : 1 ≤ s) :
    2*K^(2*s+3)/t  ≤  2*A^(5*s)*R^(290*s)/p^(1161*s) := by
  have hK : 0<K := zero_lt_one.trans_le hK1
  have ht : 0<t := hp.trans_le hpt
  have hg := growth_power_budget hp.le hK.le hbound (5*s)
  have hexp : 2*s+3  ≤  5*s := by omega
  have hkp : K^(2*s+3)  ≤  K^(5*s) := pow_le_pow_right₀ hK1 hexp
  have hps : p^s  ≤  p := by simpa using pow_le_pow_of_le_one hp.le hp1 hs
  have hpow : p^(1161*s)  ≤  t*p^(1160*s) := by
    calc
      _ = p^s*p^(1160*s) := by rw [←pow_add]; congr 1; omega
      _  ≤  _ := mul_le_mul_of_nonneg_right (hps.trans hpt) (by positivity)
  have hh : (2*K^(2*s+3))*p^(1161*s)  ≤  (2*A^(5*s)*R^(290*s))*t := by
    calc
      _  ≤  (2*K^(2*s+3))*(t*p^(1160*s)) := mul_le_mul_of_nonneg_left hpow (by positivity)
      _  ≤  (2*K^(5*s))*(t*p^(1160*s)) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkp (by norm_num)) (by positivity)
      _ = 2*t*(K^(5*s)*p^(232*(5*s))) := by
        rw [show 232*(5*s)=1160*s by omega]
        ring
      _  ≤  2*t*(A^(5*s)*R^(58*(5*s))) := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by
        rw [show 58*(5*s)=290*s by omega]
        ring
  exact (div_le_div_iff₀ ht (by positivity)).mpr hh
end NativeAsymmetricPolynomialRetention
