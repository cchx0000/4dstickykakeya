import Theorems.Thm_StickyKakeya4_native_dyadic_tube_epoch

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace NativeSourceSizeBounds
open NativeDyadicTubeEpoch NativeDyadicTubeStopping DisjointProfileEpochs
open FiniteVoronoiRealADCoarsening
noncomputable section

lemma inv_delta_le_pow {delta : ℝ} {N : ℕ} (hdelta : 0 < delta)
    (htop : (1:ℝ)/128 ≤ delta * (2:ℝ)^N) :
    1/delta ≤ (2:ℝ)^(N+7) := by
  apply (div_le_iff₀ hdelta).mpr
  rw [pow_add]
  norm_num only [show (2:ℝ)^7 = 128 by norm_num]
  nlinarith only [htop]

lemma source_card_le_inv_cube {X : Type*} [PseudoMetricSpace X]
    (A : Finset X) {delta K t eta : ℝ} (hne : A.Nonempty)
    (hdelta : 0 < delta) (hdeltaone : delta ≤ 1) (ht2 : t ≤ 2)
    (hetaone : eta ≤ 1) (hKsmall : K ≤ delta^(-eta))
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1)
    (hAD : ADBounds A delta K t) :
    (A.card:ℝ) ≤ (1/delta)^3 := by
  obtain ⟨c,hc⟩ := hne
  have hunit := (hAD c hc 1 hdeltaone le_rfl).2
  rw [FiniteVoronoiADCoarsening.carrierBall_one_eq A hdiam hc] at hunit
  have hinv : 1 ≤ 1/delta := (le_div_iff₀ hdelta).mpr (by simpa using hdeltaone)
  have hKr : K ≤ (1/delta)^eta := by
    simpa only [Real.rpow_neg_eq_inv_rpow, one_div] using hKsmall
  have hKinv : K ≤ 1/delta := hKr.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hinv hetaone)
  have htp : (1/delta)^t ≤ (1/delta)^(2:ℕ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hinv ht2
  calc
    (A.card:ℝ) ≤ K*(1/delta)^t := hunit
    _ ≤ (1/delta)*(1/delta)^2 := mul_le_mul hKinv htp (by positivity) (by positivity)
    _ = (1/delta)^3 := by ring

lemma source_card_le_pow {X : Type*} [PseudoMetricSpace X]
    (A : Finset X) {delta K t eta : ℝ} {N : ℕ} (hne : A.Nonempty)
    (hdelta : 0 < delta) (hdeltaone : delta ≤ 1) (ht2 : t ≤ 2)
    (hetaone : eta ≤ 1) (hKsmall : K ≤ delta^(-eta))
    (htop : (1:ℝ)/128 ≤ delta * (2:ℝ)^N)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1)
    (hAD : ADBounds A delta K t) : A.card ≤ 2^(3*N+21) := by
  have hbound : (A.card:ℝ) ≤ (2:ℝ)^(3*N+21) := by
    calc
      _ ≤ (1/delta)^3 := source_card_le_inv_cube A hne hdelta hdeltaone ht2 hetaone hKsmall hdiam hAD
      _ ≤ ((2:ℝ)^(N+7))^3 := pow_le_pow_left₀ (by positivity) (inv_delta_le_pow hdelta htop) 3
      _ = (2:ℝ)^(3*N+21) := by rw [← pow_mul]; congr 1; omega
  exact_mod_cast hbound

def radix (n L : ℕ) : ℕ := max 4 ⌈(n:ℝ)^(1/(L:ℝ))⌉₊

lemma radix_four_le (n L : ℕ) : 4 ≤ radix n L := le_max_left _ _

lemma card_le_radix_pow (n : ℕ) {L : ℕ} (hL : 0 < L) : n ≤ radix n L ^ L := by
  have hx : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hx _) (Nat.le_ceil ((n:ℝ)^((L:ℝ)⁻¹))) L
  rw [Real.rpow_inv_natCast_pow hx hL.ne'] at hp
  have hnat : n ≤ ⌈(n:ℝ)^((L:ℝ)⁻¹)⌉₊ ^ L := by exact_mod_cast hp
  exact hnat.trans (Nat.pow_le_pow_left (by simpa only [radix, one_div] using le_max_right 4 ⌈(n:ℝ)^(1/(L:ℝ))⌉₊) L)

lemma radix_le_four_root {n L : ℕ} (hn : 0 < n) :
    (radix n L : ℝ) ≤ 4*(n:ℝ)^(1/(L:ℝ)) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hroot : 1 ≤ (n:ℝ)^(1/(L:ℝ)) := Real.one_le_rpow hn1 (by positivity)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (n:ℝ)^(1/(L:ℝ)) by positivity)
  unfold radix
  rw [Nat.cast_max]
  apply max_le
  · norm_num only [Nat.cast_ofNat]
    nlinarith
  · nlinarith

lemma radix_le_dyadic {n N L : ℕ} (hn : 0 < n) (hL : 0 < L)
    (hnlarge : n ≤ 2^(3*N+21)) :
    (radix n L : ℝ) ≤ (2:ℝ)^23 * (2:ℝ)^(3*(N:ℝ)/(L:ℝ)) := by
  have hLone : (1:ℝ) ≤ L := by exact_mod_cast hL
  have hLp : (0:ℝ) < L := by exact_mod_cast hL
  have hnlargeR : (n:ℝ) ≤ (2:ℝ)^(3*N+21) := by exact_mod_cast hnlarge
  have hr := Real.rpow_le_rpow (Nat.cast_nonneg n) hnlargeR (show 0 ≤ 1/(L:ℝ) by positivity)
  have hexp : ((3*(N:ℝ)+21)/(L:ℝ)) ≤ 21+3*(N:ℝ)/(L:ℝ) := by
    rw [add_div]
    have h := (div_le_iff₀ hLp).mpr (show (21:ℝ) ≤ 21*(L:ℝ) by nlinarith only [hLone])
    linarith only [h]
  calc
    (radix n L:ℝ) ≤ 4*(n:ℝ)^(1/(L:ℝ)) := radix_le_four_root hn
    _ ≤ 4*((2:ℝ)^(3*N+21))^(1/(L:ℝ)) := mul_le_mul_of_nonneg_left hr (by norm_num)
    _ = 4*(2:ℝ)^((3*(N:ℝ)+21)/(L:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 2
      push_cast
      ring
    _ ≤ 4*(2:ℝ)^(21+3*(N:ℝ)/(L:ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by norm_num)
    _ = (2:ℝ)^23*(2:ℝ)^(3*(N:ℝ)/(L:ℝ)) := by
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      norm_num
      ring

lemma K_pow_eighteen_le {delta K eta : ℝ} {N : ℕ}
    (hdelta : 0 < delta) (hK : 0 ≤ K) (heta : 0 ≤ eta) (hetaone : eta ≤ 1)
    (hKsmall : K ≤ delta^(-eta))
    (htop : (1:ℝ)/128 ≤ delta*(2:ℝ)^N) :
    K^18 ≤ (2:ℝ)^126*(2:ℝ)^(18*eta*(N:ℝ)) := by
  have hKr : K ≤ (1/delta)^eta := by
    simpa only [Real.rpow_neg_eq_inv_rpow, one_div] using hKsmall
  have hpow := Real.rpow_le_rpow (show 0 ≤ 1/delta by positivity) (inv_delta_le_pow hdelta htop) heta
  have h1 : K^18 ≤ (((2:ℝ)^(N+7))^eta)^18 :=
    pow_le_pow_left₀ hK (hKr.trans hpow) 18
  calc
    K^18 ≤ (((2:ℝ)^(N+7))^eta)^18 := h1
    _ = (2:ℝ)^(((N:ℝ)+7)*eta*18) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      push_cast
      rfl
    _ ≤ (2:ℝ)^(126+18*eta*(N:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith only [hetaone])
    _ = (2:ℝ)^126*(2:ℝ)^(18*eta*(N:ℝ)) := by
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      norm_num

lemma rank_le_linear {n N : ℕ} (hn : n ≤ 2^(3*N+21)) :
    rank 2 n ≤ 22*(N+1) := by
  have hp : (2:ℕ)^(3*N+21) ≠ 0 := by positivity
  calc
    rank 2 n ≤ rank 2 (2^(3*N+21)) := rank_mono 2 hn
    _ = 3*N+22 := by simp only [rank, hp, ↓reduceIte, Nat.log_pow (by norm_num : 1 < (2:ℕ))]
    _ ≤ 22*(N+1) := by omega

lemma epoch_factor_le {n N : ℕ} (hn : n ≤ 2^(3*N+21)) :
    Fintype.card (NativeDyadicTubeStopping.Index N) *
      (4*(Fintype.card (NativeDyadicTubeStopping.Index N)*rank 2 n)) ≤ 88*(N+1)^5 := by
  have hi := index_card_le N
  have hr := rank_le_linear hn
  calc
    _ ≤ (N+1)^2*(4*((N+1)^2*(22*(N+1)))) := by gcongr
    _ = 88*(N+1)^5 := by ring

lemma epoch_factor_real_le {n N : ℕ} (hn : n ≤ 2^(3*N+21)) :
    (Fintype.card (NativeDyadicTubeStopping.Index N):ℝ) *
      (4*(Fintype.card (NativeDyadicTubeStopping.Index N)*rank 2 n):ℕ) ≤ 88*((N:ℝ)+1)^5 := by
  exact_mod_cast epoch_factor_le hn

lemma index_card_real_one_le (N : ℕ) :
    (1:ℝ) ≤ Fintype.card (NativeDyadicTubeStopping.Index N) := by
  exact_mod_cast index_card_pos N

lemma epoch_cost_one_le {n : ℕ} (hn : 0 < n) (N : ℕ) :
    1 ≤ 4*(Fintype.card (NativeDyadicTubeStopping.Index N)*rank 2 n) := by
  have hi := index_card_pos N
  have hr := rank_pos 2 hn
  have hp := Nat.mul_pos hi hr
  omega

lemma epoch_cost_real_one_le {n : ℕ} (hn : 0 < n) (N : ℕ) :
    (1:ℝ) ≤ (4*(Fintype.card (NativeDyadicTubeStopping.Index N)*rank 2 n):ℕ) := by
  exact_mod_cast epoch_cost_one_le hn N

end
end NativeSourceSizeBounds
