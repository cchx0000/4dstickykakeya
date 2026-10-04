import Theorems.Thm_StickyKakeya4_real_scale_tube_profile_transfer
import Theorems.Thm_StickyKakeya4_dyadic_ad_interpolation

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace RealScalarADInterpolation

open NativeDyadicTubeStopping RealScaleTubeProfileTransfer DyadicAlignmentParameters DyadicADInterpolation

noncomputable section
attribute [local instance] Classical.propDecidable

def ballCount {X : Type*} [PseudoMetricSpace X] (S : Finset X) (x : X) (r : ℝ) : ℝ :=
  ((S.filter (fun y => dist y x ≤ r)).card : ℝ)

lemma ballCount_mono {X : Type*} [PseudoMetricSpace X] (S : Finset X) (x : X) : Monotone (ballCount S x) := by
  intro r u hru
  unfold ballCount
  exact_mod_cast Finset.card_le_card (show S.filter (fun y => dist y x ≤ r) ⊆
    S.filter (fun y => dist y x ≤ u) from fun y hy =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2.trans hru⟩)

lemma ballCount_nonneg {X : Type*} [PseudoMetricSpace X] (S : Finset X) (x : X) (r : ℝ) :
    0 ≤ ballCount S x r := Nat.cast_nonneg _

lemma scalePower_eq (s : ℝ) (n : ℕ) : scalePower s n = ((2 : ℝ) ^ n) ^ s := by
  rw [scalePower, ← Real.rpow_natCast 2 n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- Literal real balls interpolate from the finite working tests. The two
extra factors are explicit: the working-grid gap and the real dyadic bracket. -/
theorem real_ball_interpolation {X : Type*} [PseudoMetricSpace X]
    (S : Finset X) (x : X) (M H : ℕ) (hH : 0 < H)
    {μ s A B r : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hworking : ∀ j ≤ H,
      A * ((2 : ℝ) ^ level M H j) ^ s ≤ ballCount S x (scale μ (level M H j)) ∧
        ballCount S x (scale μ (level M H j)) ≤ B * ((2 : ℝ) ^ level M H j) ^ s)
    (hlo : μ ≤ r) (hhi : r ≤ scale μ M) :
    A * (r / μ) ^ s ≤ ((2 : ℝ) ^ s * scalePower s (gap M H)) * ballCount S x r ∧
      ballCount S x r ≤ ((2 : ℝ) ^ s * scalePower s (gap M H)) * B * (r / μ) ^ s := by
  let f : ℕ → ℝ := fun n => ballCount S x (scale μ n)
  have hf : Monotone f := (ballCount_mono S x).comp (scale_mono hμ.le)
  have hw : ∀ j ≤ H, A * scalePower s (level M H j) ≤ f (level M H j) ∧
      f (level M H j) ≤ B * scalePower s (level M H j) := by
    intro j hj
    simpa only [f, scalePower_eq] using hworking j hj
  obtain ⟨k, _hk0, hkM, hrk, hkr, hmin⟩ :=
    exists_minimal_upper_level hμ 0 M (Nat.zero_le _) (by simpa only [scale_zero] using hlo) hhi
  let i := k - 1
  have hik : i ≤ k := Nat.sub_le _ _
  have hiM : i ≤ M := hik.trans hkM
  have hir : scale μ i ≤ r := by
    by_cases hk : k = 0
    · simpa only [i, hk, Nat.zero_sub, scale_zero] using hlo
    · by_contra hh
      have hrprev : r ≤ scale μ (k - 1) := le_of_not_ge hh
      have hm := hmin (k - 1) (Nat.zero_le _) hiM hrprev
      omega
  have hstep : scale μ k ≤ 2 * scale μ i := by
    by_cases hk : k = 0
    · simp only [i, hk, Nat.zero_sub, scale_zero]
      linarith only [hμ]
    · have he : k = i + 1 := by dsimp only [i]; omega
      simpa only [he, scale_add, pow_one, mul_comm] using (le_refl (2 * scale μ i))
  have hlowratio : r / μ ≤ 2 * (2 : ℝ) ^ i := by
    apply (div_le_iff₀ hμ).mpr
    have hh := hrk.trans hstep
    unfold scale at hh
    nlinarith only [hh]
  have hupratio : (2 : ℝ) ^ k ≤ 2 * (r / μ) := by
    have he : 2 * (r / μ) = (2 * r) / μ := by ring
    rw [he]
    apply (le_div_iff₀ hμ).mpr
    unfold scale at hkr
    nlinarith only [hkr]
  have hr : 0 < r := hμ.trans_le hlo
  have hlpow := Real.rpow_le_rpow (div_nonneg hr.le hμ.le) hlowratio hs
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ (2 : ℝ) ^ i)] at hlpow
  have hupow := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ) ^ k) hupratio hs
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (div_nonneg hr.le hμ.le)] at hupow
  have hlow := (interpolate_working_profile M H hH f hf A B s hA hB hs hw i hiM).1
  have hupp := (interpolate_working_profile M H hH f hf A B s hA hB hs hw k hkM).2
  rw [scalePower_eq s i] at hlow
  rw [scalePower_eq s k] at hupp
  have hgap := scalePower_nonneg s (gap M H)
  have htwo : 0 ≤ (2 : ℝ) ^ s := by positivity
  constructor
  · calc
      _ ≤ A * ((2 : ℝ) ^ s * ((2 : ℝ) ^ i) ^ s) := mul_le_mul_of_nonneg_left hlpow hA
      _ = (2 : ℝ) ^ s * (A * ((2 : ℝ) ^ i) ^ s) := by ring
      _ ≤ (2 : ℝ) ^ s * (scalePower s (gap M H) * f i) := mul_le_mul_of_nonneg_left hlow htwo
      _ ≤ (2 : ℝ) ^ s * (scalePower s (gap M H) * ballCount S x r) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ballCount_mono S x hir) hgap) htwo
      _ = _ := by ring
  · calc
      _ ≤ f k := ballCount_mono S x hrk
      _ ≤ scalePower s (gap M H) * B * ((2 : ℝ) ^ k) ^ s := hupp
      _ ≤ scalePower s (gap M H) * B * ((2 : ℝ) ^ s * (r / μ) ^ s) :=
        mul_le_mul_of_nonneg_left hupow (mul_nonneg hgap hB)
      _ = _ := by ring

/-- Radii above the native endpoint use its valid lower ball and the actual
global cardinality upper bound. No assertion that this endpoint ball contains
the entire set is needed. -/
theorem top_scale_extension {X : Type*} [PseudoMetricSpace X] (S : Finset X) (x : X)
    {μ N r s A B C : ℝ} (hμ : 0 < μ) (hN : 0 < N) (hs : 0 ≤ s)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hlower : A * N ^ s ≤ ballCount S x (μ * N))
    (hglobal : (S.card : ℝ) ≤ B * N ^ s)
    (hrlo : μ * N ≤ r) (hrhi : r ≤ C * (μ * N)) :
    A * (r / μ) ^ s ≤ C ^ s * ballCount S x r ∧
      ballCount S x r ≤ B * (r / μ) ^ s := by
  have hr : 0 < r := (mul_pos hμ hN).trans_le hrlo
  have hratioLo : N ≤ r / μ := (le_div_iff₀ hμ).mpr (by simpa only [mul_comm] using hrlo)
  have hratioHi : r / μ ≤ C * N := (div_le_iff₀ hμ).mpr (by nlinarith only [hrhi])
  have hpowLo := Real.rpow_le_rpow hN.le hratioLo hs
  have hpowHi := Real.rpow_le_rpow (div_nonneg hr.le hμ.le) hratioHi hs
  rw [Real.mul_rpow hC hN.le] at hpowHi
  constructor
  · calc
      _ ≤ A * (C ^ s * N ^ s) := mul_le_mul_of_nonneg_left hpowHi hA
      _ = C ^ s * (A * N ^ s) := by ring
      _ ≤ C ^ s * ballCount S x (μ * N) :=
        mul_le_mul_of_nonneg_left hlower (Real.rpow_nonneg hC _)
      _ ≤ C ^ s * ballCount S x r :=
        mul_le_mul_of_nonneg_left (ballCount_mono S x hrlo) (Real.rpow_nonneg hC _)
  · have hcard : ballCount S x r ≤ (S.card : ℝ) := by
      unfold ballCount
      exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun y => dist y x ≤ r) S)
    exact hcard.trans (hglobal.trans (mul_le_mul_of_nonneg_left hpowLo hB))

end
end RealScalarADInterpolation
