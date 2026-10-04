import Theorems.Thm_StickyKakeya4_original_good_graph_cap_fraction
import Theorems.Thm_StickyKakeya4_original_source_log_budgets
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3400000

noncomputable section
namespace NativeOriginalCapFractionBudget
open OriginalPairStripGeometry PlanarFrostmanBallConversion OriginalSourceLogBudgets
open OriginalPhysicalTubeScaleSelection DyadicOriginalFiberSelection

def capConstant : ℝ := 8*539*110^3*24^2

private theorem dense_population_factor_le (sigma : ℝ) (hsigma : sigma≤1) :
    0≤(2:ℝ)^(sigma+1)*6^sigma ∧ (2:ℝ)^(sigma+1)*6^sigma≤24 := by
  have htwo : (2:ℝ)^(sigma+1)≤4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show sigma+1≤2 by linarith only [hsigma])
    norm_num only [Real.rpow_two,show (2:ℝ)^2=4 by norm_num] at hh
    exact hh
  have hsix : (6:ℝ)^sigma≤6 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ)≤6) hsigma
  refine ⟨by positivity,?_⟩
  have hh := mul_le_mul htwo hsix (Real.rpow_nonneg (by norm_num : (0:ℝ)≤6) sigma)
    (by norm_num : (0:ℝ)≤4)
  nlinarith only [hh]

/-- The exact actual family coefficient is small at a genuine cutoff.
All scale-menu and occupancy logarithms come from original separation. -/
theorem exists_native_original_cap_fraction_budget
    (sigma eta eta' a chi : ℝ) (hsigma : sigma≤1)
    (hmargin : eta/2+8*eta'/a<chi) :
    ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧
      ∀ delta : ℝ, 0<delta → delta≤delta0 → ∀ n : ℕ,
        delta≤dyadicRadius n → dyadicRadius n≤2*delta →
        ∀ Pts : Finset Point,
          (∀ x∈Pts, |x.1|≤1 ∧ |x.2|≤1) →
          (∀ x∈Pts, ∀ y∈Pts, x≠y → delta≤euclideanDistance x y) →
          8*539*(((n+1)*levelCount Pts:ℕ):ℝ)*110^3*(levelCount Pts:ℝ)^2*
              ((2:ℝ)^(sigma+1)*6^sigma)^2*(delta^chi)^2/
                (delta^(eta/2)*(delta^(2*eta'/a))^4)≤delta^chi := by
  let eps := chi-eta/2-8*eta'/a
  have heps : 0<eps := by dsimp [eps]; linarith only [hmargin]
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_original_logarithmic_power_cutoff capConstant
    (by dsimp [capConstant]; positivity) 1 3 eps heps
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall n hmesh hbottom Pts hbox hsep
  let L : ℝ := levelCount Pts
  let D : ℝ := (2:ℝ)^(sigma+1)*6^sigma
  have hL : 0≤L := by dsimp [L]; positivity
  obtain ⟨hD,hD24⟩ := dense_population_factor_le sigma hsigma
  have hDsq : D^2≤24^2 := pow_le_pow_left₀ hD hD24 2
  have hpoly : 8*539*((n:ℝ)+1)*110^3*L^3*D^2≤capConstant*((n:ℝ)+5)*L^3 := by
    calc
      _ ≤ 8*539*((n:ℝ)+1)*110^3*L^3*24^2 :=
        mul_le_mul_of_nonneg_left hDsq (by positivity)
      _ ≤ _ := by
        dsimp [capConstant]
        nlinarith only [show 0≤L^3 by positivity]
  have hpower : (delta^chi)^2/(delta^(eta/2)*(delta^(2*eta'/a))^4)=delta^chi*delta^eps := by
    rw [← Real.rpow_mul_natCast hd.le chi 2,
      ← Real.rpow_mul_natCast hd.le (2*eta'/a) 4,← Real.rpow_add hd,
      ← Real.rpow_sub hd,← Real.rpow_add hd]
    congr 1
    dsimp [eps]
    ring
  have hbudget := hcut delta hd hsmall n hmesh hbottom Pts hbox hsep
  simp only [pow_one] at hbudget
  have he : 8*539*(((n+1)*levelCount Pts:ℕ):ℝ)*110^3*(levelCount Pts:ℝ)^2*
      ((2:ℝ)^(sigma+1)*6^sigma)^2*(delta^chi)^2/
        (delta^(eta/2)*(delta^(2*eta'/a))^4)=
      (8*539*((n:ℝ)+1)*110^3*L^3*D^2)*
        ((delta^chi)^2/(delta^(eta/2)*(delta^(2*eta'/a))^4)) := by
    dsimp [L,D]
    push_cast
    ring
  rw [he,hpower]
  have hh := mul_le_mul_of_nonneg_right hpoly
    (show 0≤delta^chi*delta^eps by positivity)
  have hb := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hd.le chi)
  dsimp [L] at hh
  nlinarith only [hh,hb]

end NativeOriginalCapFractionBudget
