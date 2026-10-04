import Theorems.Thm_StickyKakeya4_original_separated_point_packing
import Theorems.Thm_StickyKakeya4_native_annular_parameter_budget
import Theorems.Thm_StickyKakeya4_dyadic_original_fiber_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
namespace OriginalSourceLogBudgets
open OriginalSeparatedPointPacking OriginalPairStripGeometry PlanarFrostmanBallConversion
open OriginalPhysicalTubeScaleSelection NativeAnnularParameterBudget DyadicOriginalFiberSelection

/-- The original Euclidean separation controls the actual occupancy-bin
count by the already chosen original dyadic menu depth. -/
theorem original_level_count_le_menu (Pts : Finset Point) (delta : ℝ) (n : ℕ)
    (hd : 0<delta) (hd1 : delta≤1) (hmesh : dyadicRadius n≤2*delta)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hsep : ∀ p∈Pts, ∀ q∈Pts, p≠q → delta≤euclideanDistance p q) :
    levelCount Pts≤2*n+9 := by
  have hpack := original_separated_square_packing Pts delta hd hd1 hbox hsep
  let b : ℝ := 2^n
  have hb : 0<b := by dsimp [b]; positivity
  have hdyadic : dyadicRadius n*b=1 := by
    dsimp [dyadicRadius,b]
    rw [← mul_pow]
    norm_num
  have hmesh' := mul_le_mul_of_nonneg_right hmesh hb.le
  rw [hdyadic] at hmesh'
  have hs : (1:ℝ)≤(2*delta*b)^2 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hmesh' 2
  have h1 := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg Pts.card)
  have h2 := mul_le_mul_of_nonneg_right hpack (show 0≤4*b^2 by positivity)
  have hcard : (Pts.card : ℝ)≤400*b^2 := by nlinarith only [h1,h2]
  have hbpow : b^2=(2:ℝ)^(2*n) := by
    dsimp [b]
    rw [← pow_mul]
    congr 1
    omega
  rw [hbpow] at hcard
  have hnat : Pts.card≤400*2^(2*n) := by exact_mod_cast hcard
  have hbound : Pts.card<2^(2*n+9) := by
    calc
      _ ≤ 400*2^(2*n) := hnat
      _ < 512*2^(2*n) := Nat.mul_lt_mul_of_pos_right (by decide) (by positivity)
      _ = _ := by rw [pow_add]; norm_num; ring
  have hlog := Nat.log_lt_of_lt_pow' (by omega : 2*n+9≠0) hbound
  unfold levelCount
  omega

/-- Any fixed product of actual menu and occupancy logarithms is absorbed
by a positive power, with one cutoff chosen before the original P and n. -/
theorem exists_original_logarithmic_power_cutoff (C : ℝ) (hC : 0≤C)
    (p q : ℕ) (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧
      ∀ delta : ℝ, 0<delta → delta≤delta0 → ∀ n : ℕ,
        delta≤dyadicRadius n → dyadicRadius n≤2*delta →
        ∀ Pts : Finset Point,
          (∀ x∈Pts, |x.1|≤1 ∧ |x.2|≤1) →
          (∀ x∈Pts, ∀ y∈Pts, x≠y → delta≤euclideanDistance x y) →
          C*((n:ℝ)+5)^p*(levelCount Pts : ℝ)^q*delta^epsilon≤1 := by
  let D := p+q+1
  let a := epsilon/(D:ℝ)
  let C' := max 1 (C*(2:ℝ)^q)
  have hD : 0<D := by dsimp [D]; omega
  have hDr : 0<(D:ℝ) := by exact_mod_cast hD
  have ha : 0<a := div_pos hepsilon hDr
  have hC' : 1≤C' := le_max_left _ _
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_original_menu_power_cutoff C'
    (by linarith only [hC']) ha
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall n hmesh hbottom Pts hbox hsep
  have hlin := hcut delta hd hsmall n hmesh hbottom
  have hL := original_level_count_le_menu Pts delta n hd (hsmall.trans hd01) hbottom hbox hsep
  let N : ℝ := (n:ℝ)+5
  have hN : 1≤N := by
    dsimp [N]
    have hn : (0:ℝ)≤n := by positivity
    linarith only [hn]
  have hLreal : (levelCount Pts : ℝ)≤2*N := by
    have hh : (levelCount Pts : ℝ)≤2*(n:ℝ)+9 := by exact_mod_cast hL
    dsimp [N]
    linarith only [hh]
  have hLpow := pow_le_pow_left₀ (Nat.cast_nonneg (levelCount Pts)) hLreal q
  have hCpow : C*(2:ℝ)^q≤C'^D :=
    (le_max_right 1 (C*(2:ℝ)^q)).trans (le_self_pow₀ hC' (Nat.ne_of_gt hD))
  have hNpow : N^(p+q)≤N^D := pow_le_pow_right₀ hN (by dsimp [D]; omega)
  have hpoly : C*N^p*(levelCount Pts : ℝ)^q≤(C'*N)^D := by
    calc
      _ ≤ C*N^p*(2*N)^q := mul_le_mul_of_nonneg_left hLpow (by positivity)
      _ = (C*(2:ℝ)^q)*N^(p+q) := by rw [mul_pow,pow_add]; ring
      _ ≤ C'^D*N^D := mul_le_mul hCpow hNpow (by positivity) (by positivity)
      _ = _ := (mul_pow C' N D).symm
  have hpows := pow_le_pow_left₀ (show 0≤(C'*N)*delta^a by positivity) hlin D
  have hid : a*(D:ℝ)=epsilon := by dsimp [a]; field_simp
  rw [mul_pow,← Real.rpow_mul_natCast hd.le a D,hid,one_pow] at hpows
  exact (mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hd.le epsilon)).trans hpows

end OriginalSourceLogBudgets
