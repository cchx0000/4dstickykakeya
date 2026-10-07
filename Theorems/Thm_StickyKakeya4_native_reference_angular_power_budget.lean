import Theorems.Thm_StickyKakeya4_native_pair_scale_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
namespace NativeReferenceAngularPowerBudget
open StickyKakeya4 NativePairScaleBudget NativeSameSourceMultiplicityBalance

/-- The actual first-stage cost pays the 81Q1^4 angular coefficient, and the
local thickness is at least the original delta. No rank retention is involved. -/
lemma first_cost_angular_factor {delta eta seed sigma budget : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta) (hsigma : delta ≤ sigma)
    (hbudget : 0 ≤ budget) (F Q : ℕ) (hF : 0 < F)
    (hcost : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8))) :
    81*(Q:ℝ)^4*sigma^(-budget) ≤ delta^(-(seed/4+budget)) := by
  have hsigma0 : 0 < sigma := hd.trans_le hsigma
  have hQ := (radix_four_cost hd hd1 heta F Q hF hcost).2
  have hQ81 : 81*(Q:ℝ)^4 ≤ delta^(-(seed/4)) := by
    calc
      _ ≤ 125*(Q:ℝ)^4 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ _ := by
        convert hQ using 1
        congr 1
        ring
  have hSigma := Real.rpow_le_rpow_of_nonpos hd hsigma (neg_nonpos.mpr hbudget)
  calc
    _ ≤ delta^(-(seed/4))*delta^(-budget) := mul_le_mul hQ81 hSigma (by positivity) (by positivity)
    _ = _ := by rw [←Real.rpow_add hd]; congr 1; ring

/-- The exponent is chosen AFTER a positive rank cutoff a. This explicit
inequality is what prevents an uncontrolled earlier e/a loss. -/
lemma relative_power_payment {delta rho a seed budget loss : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hrho : 0 < rho) (hloss : 0 ≤ loss)
    (hrhoCut : rho ≤ delta^a) (hmargin : seed/4+budget ≤ a*loss) :
    delta^(-(seed/4+budget)) ≤ rho^(-loss) := by
  calc
    _ ≤ delta^(-(a*loss)) := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
    _ = (delta^a)^(-loss) := by rw [←Real.rpow_mul hd.le]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hrho hrhoCut (neg_nonpos.mpr hloss)

/-- Independent choices beta≤a*loss/2 and seed≤2a*loss leave the required
margin. K may already be fixed and absorbed into the desired per-round loss. -/
lemma independent_exponent_margin {a loss seed budget : ℝ}
    (hbudget : budget ≤ a*loss/2) (hseed : seed ≤ 2*a*loss) :
    seed/4+budget ≤ a*loss := by linarith

/-- Coherence rounds may have large spatial radius. Only the original rank
radius r is paid against delta; rho uses its actual lower bound by Delta. -/
lemma coherence_radius_payment {r Delta rho epsilon : ℝ}
    (hr : 0 < r) (hDelta : 0 < Delta) (hepsilon : 0 ≤ epsilon)
    (hsquare : r ≤ Delta^2) (hrho : Delta ≤ rho) :
    rho^(-epsilon) ≤ r^(-(epsilon/2)) := by
  have hbase := Real.rpow_le_rpow_of_nonpos hr hsquare (by linarith : -(epsilon/2) ≤ 0)
  have he : (Delta^2)^(-(epsilon/2))=Delta^(-epsilon) := by
    calc
      _ = (Delta^(2:ℝ))^(-(epsilon/2)) := by rw [Real.rpow_two]
      _ = Delta^((2:ℝ)*(-(epsilon/2))) := (Real.rpow_mul hDelta.le _ _).symm
      _ = _ := by congr 1; ring
  rw [he] at hbase
  exact (Real.rpow_le_rpow_of_nonpos hDelta hrho (neg_nonpos.mpr hepsilon)).trans hbase

/-- Fully paid per-round excess factor, uniformly even when rho is close to
one. K fixed rounds therefore pay K*(loss+epsilon/2), not a g(tau) loss. -/
lemma coherence_excess_factor {delta eta seed sigma budget r a loss Delta rho epsilon : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta) (hsigma : delta ≤ sigma)
    (hbudget : 0 ≤ budget) (F Q : ℕ) (hF : 0 < F)
    (hcost : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)))
    (hr : 0 < r) (hloss : 0 ≤ loss) (hrcut : r ≤ delta^a)
    (hmargin : seed/4+budget ≤ a*loss) (hDelta : 0 < Delta) (hepsilon : 0 ≤ epsilon)
    (hsquare : r ≤ Delta^2) (hrho : Delta ≤ rho) :
    81*(Q:ℝ)^4*sigma^(-budget)*rho^(-epsilon) ≤ r^(-(loss+epsilon/2)) := by
  have hfactor := (first_cost_angular_factor hd hd1 heta hsigma hbudget F Q hF hcost).trans
    (relative_power_payment hd hd1 hr hloss hrcut hmargin)
  have hrho0 := hDelta.trans_le hrho
  calc
    _ ≤ r^(-loss)*r^(-(epsilon/2)) := mul_le_mul hfactor
      (coherence_radius_payment hr hDelta hepsilon hsquare hrho) (by positivity) (by positivity)
    _ = _ := by rw [←Real.rpow_add hr]; congr 1; ring

end NativeReferenceAngularPowerBudget
