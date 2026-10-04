import Theorems.Thm_StickyKakeya4_native_radial_densest_graph

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

noncomputable section
namespace NativeRadialScaleConsequences
open OriginalPairStripGeometry OriginalPhysicalPairTube
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl

/-- Solve the proved original maximum-density scale bound, including its
full dyadic factor, to obtain source (217). -/
theorem selected_scale_upper (delta sigma s zeta rho : ℝ)
    (hd : 0<delta) (hsigma : 0<sigma) (hrho : 0≤rho)
    (hscale : delta^(s-sigma-zeta)*rho^sigma≤2^sigma) :
    rho≤2*delta^((zeta-s+sigma)/sigma) := by
  have hA := Real.rpow_pos_of_pos hd (s-sigma-zeta)
  have htarget : 0≤2*delta^((zeta-s+sigma)/sigma) := by positivity
  have heq : delta^(s-sigma-zeta)*(2*delta^((zeta-s+sigma)/sigma))^sigma=2^sigma := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hd.le _),
      ← Real.rpow_mul hd.le,div_mul_cancel₀ _ (ne_of_gt hsigma)]
    calc
      _ = 2^sigma*(delta^(s-sigma-zeta)*delta^(zeta-s+sigma)) := by ring
      _ = 2^sigma*delta^((s-sigma-zeta)+(zeta-s+sigma)) := by rw [← Real.rpow_add hd]
      _ = _ := by ring_nf; rw [Real.rpow_zero,mul_one]
  apply (Real.rpow_le_rpow_iff hrho htarget hsigma).mp
  exact (mul_le_mul_iff_of_pos_left hA).mp (hscale.trans_eq heq.symm)

/-- The source reciprocal-radius form (220), for every actual tau in its
allowed interval and the original physical tubes. -/
theorem original_reciprocal_width_control
    (Pts : Finset Point) (z : Pair) (n : ℕ) (sigma rho tau : ℝ)
    (hsigma : 0≤sigma) (hrho : rho∈scaleMenu n)
    (hmax : ∀ q∈scaleMenu n, score Pts sigma q z≤score Pts sigma rho z)
    (htlow : rho≤tau) (hthigh : tau≤1) :
    ((physicalPairTube Pts (rho/tau) z).card : ℝ)≤
      2^sigma*tau^(-sigma)*(physicalPairTube Pts rho z).card := by
  have hrhopos := ((scale_menu_bounds n).2.2 rho hrho).1
  have htpos : 0<tau := hrhopos.trans_le htlow
  have hRlow : rho≤rho/tau := (le_div_iff₀ htpos).mpr (by nlinarith)
  have hRhigh : rho/tau≤1 := (div_le_iff₀ htpos).mpr (by simpa only [one_mul] using htlow)
  have h := original_larger_width_control Pts z n sigma rho (rho/tau) hsigma hrho hmax hRlow hRhigh
  have heq : rho/tau/rho=tau⁻¹ := by field_simp
  rw [heq,Real.inv_rpow htpos.le sigma,← Real.rpow_neg htpos.le sigma] at h
  exact h

end NativeRadialScaleConsequences
