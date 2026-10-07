import Theorems.Thm_StickyKakeya4_real_scalar_ad_interpolation
import Theorems.Thm_StickyKakeya4_finite_voronoi_real_ad_coarsening
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeHalfScaleInterpolation
open Classical Finset RealScalarADInterpolation

/-- Integer tests up to the actual physical half scale, and a separately
proved global count, control every real radius up to one. -/
theorem all_radius_counts {X : Type*} [PseudoMetricSpace X]
    (S : Finset X) (x : X) (N : ℕ) (hN : 1 ≤ N)
    {mu s c U G : ℝ} (hmu : 0 < mu) (hs : 0 ≤ s)
    (hc : 0 ≤ c) (hU : 0 ≤ U) (hG : 0 ≤ G)
    (hscale : mu*(N:ℝ)=1/2)
    (H : ∀R:ℕ,1 ≤ R → R ≤ N →
      c*(R:ℝ)^s ≤ ballCount S x (mu*(R:ℝ)) ∧
      ballCount S x (mu*(R:ℝ)) ≤ U*(R:ℝ)^s)
    (Hglobal : (S.card:ℝ) ≤ G*(N:ℝ)^s)
    (r : ℝ) (hr : mu ≤ r) (hrone : r ≤ 1) :
    c*(r/mu)^s ≤ (2:ℝ)^s*ballCount S x r ∧
      ballCount S x r ≤ (2:ℝ)^s*max U G*(r/mu)^s := by
  have hrpos : 0 < r := hmu.trans_le hr
  have hratio : (1:ℝ) ≤ r/mu := (le_div_iff₀ hmu).mpr (by simpa using hr)
  have hratio0 : 0 ≤ r/mu := by positivity
  have htwo : (1:ℝ) ≤ (2:ℝ)^s := Real.one_le_rpow (by norm_num) hs
  have htwo0 : 0 ≤ (2:ℝ)^s := by positivity
  by_cases hsmall : r ≤ mu*(N:ℝ)
  · have hratioN : r/mu ≤ (N:ℝ) := (div_le_iff₀ hmu).mpr (by simpa [mul_comm] using hsmall)
    let R : ℕ := ⌊r/mu⌋₊
    let V : ℕ := ⌈r/mu⌉₊
    have hR : 1 ≤ R := (Nat.one_le_floor_iff _).mpr hratio
    have hRN : R ≤ N := Nat.floor_le_of_le hratioN
    have hV : 1 ≤ V := (Nat.one_le_ceil_iff).mpr (by positivity)
    have hVN : V ≤ N := Nat.ceil_le.mpr hratioN
    have hRr : mu*(R:ℝ) ≤ r := by
      have hh := Nat.floor_le hratio0
      change (R:ℝ) ≤ r/mu at hh
      simpa only [mul_comm] using (le_div_iff₀ hmu).mp hh
    have hrV : r ≤ mu*(V:ℝ) := by
      have hh : r/mu ≤ (V:ℝ) := Nat.le_ceil _
      simpa only [mul_comm] using (div_le_iff₀ hmu).mp hh
    have hRtwo : r/mu ≤ 2*(R:ℝ) := by
      have hh : r/mu<(R:ℝ)+1 := Nat.lt_floor_add_one _
      have hRr : (1:ℝ) ≤ R := by exact_mod_cast hR
      linarith only [hh,hRr]
    have hVtwo : (V:ℝ) ≤ 2*(r/mu) := by
      have hh : (V:ℝ)<r/mu+1 := Nat.ceil_lt_add_one hratio0
      linarith only [hh,hratio]
    have hlo := (H R hR hRN).1.trans (ballCount_mono S x hRr)
    have hup := (ballCount_mono S x hrV).trans (H V hV hVN).2
    have hlpow := Real.rpow_le_rpow hratio0 hRtwo hs
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg R)] at hlpow
    have hupow := Real.rpow_le_rpow (Nat.cast_nonneg V) hVtwo hs
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hratio0] at hupow
    constructor
    · calc
        _  ≤  c*((2:ℝ)^s*(R:ℝ)^s) := mul_le_mul_of_nonneg_left hlpow hc
        _ = (2:ℝ)^s*(c*(R:ℝ)^s) := by ring
        _  ≤  _ := mul_le_mul_of_nonneg_left hlo htwo0
    · calc
        _  ≤  U*(V:ℝ)^s := hup
        _  ≤  U*((2:ℝ)^s*(r/mu)^s) := mul_le_mul_of_nonneg_left hupow hU
        _ = (2:ℝ)^s*U*(r/mu)^s := by ring
        _  ≤  _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_left U G) htwo0) (by positivity)
  · have htop : mu*(N:ℝ) ≤ r := le_of_not_ge hsmall
    have hNratio : (N:ℝ) ≤ r/mu := (le_div_iff₀ hmu).mpr (by simpa [mul_comm] using htop)
    have hratio2N : r/mu ≤ 2*(N:ℝ) := by
      apply (div_le_iff₀ hmu).mpr
      nlinarith only [hscale,hrone]
    have hlpow := Real.rpow_le_rpow hratio0 hratio2N hs
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg N)] at hlpow
    have hlo := (H N hN le_rfl).1.trans (ballCount_mono S x htop)
    have hupow := Real.rpow_le_rpow (Nat.cast_nonneg N) hNratio hs
    have hcount : ballCount S x r ≤ (S.card:ℝ) := Nat.cast_le.mpr (card_le_card (filter_subset _ _))
    constructor
    · calc
        _  ≤  c*((2:ℝ)^s*(N:ℝ)^s) := mul_le_mul_of_nonneg_left hlpow hc
        _ = (2:ℝ)^s*(c*(N:ℝ)^s) := by ring
        _  ≤  _ := mul_le_mul_of_nonneg_left hlo htwo0
    · calc
        _  ≤  G*(N:ℝ)^s := hcount.trans Hglobal
        _  ≤  G*(r/mu)^s := mul_le_mul_of_nonneg_left hupow hG
        _  ≤  max U G*(r/mu)^s := mul_le_mul_of_nonneg_right (le_max_right U G) (by positivity)
        _  ≤  _ := by
          have hh := mul_le_mul_of_nonneg_right htwo
            (mul_nonneg (hG.trans (le_max_right U G)) (by positivity : 0 ≤ (r/mu)^s))
          simpa only [one_mul,mul_assoc] using hh

def constant (c U G s : ℝ) : ℝ := max 1 (max ((2:ℝ)^s/c) ((2:ℝ)^s*max U G))

lemma constant_one_le (c U G s : ℝ) : 1 ≤ constant c U G s := le_max_left _ _

theorem ADBounds_of_counts {X : Type*} [PseudoMetricSpace X]
    (S : Finset X) {mu s c U G : ℝ} (hmu : 0 < mu) (hc : 0 < c)
    (H : ∀x∈S,∀r:ℝ,mu ≤ r → r ≤ 1 →
      c*(r/mu)^s ≤ (2:ℝ)^s*ballCount S x r ∧
      ballCount S x r ≤ (2:ℝ)^s*max U G*(r/mu)^s) :
    FiniteVoronoiRealADCoarsening.ADBounds S mu (constant c U G s) s := by
  intro x hx r hr hro
  have hh := H x hx r hr hro
  have hrpos : 0 < r := hmu.trans_le hr
  have hC : 0 < constant c U G s := lt_of_lt_of_le (by norm_num) (constant_one_le _ _ _ _)
  have hlo : (2:ℝ)^s/c ≤ constant c U G s := (le_max_left _ _).trans (le_max_right _ _)
  have hup : (2:ℝ)^s*max U G ≤ constant c U G s := (le_max_right _ _).trans (le_max_right _ _)
  change (r/mu)^s/constant c U G s ≤ ballCount S x r ∧ _
  constructor
  · apply (div_le_iff₀ hC).mpr
    have hdiv : (r/mu)^s ≤ ((2:ℝ)^s/c)*ballCount S x r := by
      have he : ((2:ℝ)^s/c)*ballCount S x r=((2:ℝ)^s*ballCount S x r)/c := by ring
      rw [he]
      exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hh.1)
    exact hdiv.trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hlo (ballCount_nonneg S x r))
  · exact hh.2.trans (mul_le_mul_of_nonneg_right hup (by positivity))

end NativeHalfScaleInterpolation
