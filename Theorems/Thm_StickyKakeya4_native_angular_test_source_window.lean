import Theorems.Thm_StickyKakeya4_native_angular_test_scale
import Theorems.Thm_StickyKakeya4_native_general_rank_scalar_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8500000

noncomputable section
namespace NativeAngularTestSourceWindow
open NativeAngularTestScale NativeMiddleGrainParentBudget NativeQuarterScaleParameters
open NativeRankExponentHierarchy NativeActualMesoscopicRankConfiguration NativeAllTwoScaleConfiguration

/-- The actual stopping identity puts every angular depth between m and
2m into the existing E1 master window. The proof uses the selected original
rank radius and its dyadic level, not an additional profile assumption. -/
theorem original_angular_depth_window {delta r a tau : ℝ}
    (hd : 0< delta) (ha : 0≤ a) (htau : 0< tau) (htauHalf : tau≤ 1/2)
    (level stop s : ℕ) (hdy : delta=(2:ℝ)⁻¹^level)
    (hstop6 : 6≤ stop) (hstopCap : stop≤ level/4)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1) (hrdelta : r≤ delta^a)
    (hsmall : delta^(a/2)≤ 1/48) (htauCut : tau≤ 4*a)
    (hs6 : 6≤ s) (hsm : s≤ middleDepth stop) :
    middleDepth stop+s-3≤ level ∧
      rankWindow tau*(level:ℝ)≤ ((middleDepth stop+s-3:ℕ):ℝ) ∧
      ((middleDepth stop+s-3:ℕ):ℝ)≤ (1-rankWindow tau)*(level:ℝ) := by
  have hlo := NativeGeneralRankScalarBudget.middle_lower hd ha level stop hdy hidentity hrdelta hsmall htauCut
  have hboundary : boundaryWindow tau=tau/1000 := min_eq_left (by linarith only [htauHalf])
  have hw : 2*rankWindow tau≤ boundaryWindow tau := by
    have hh : rankWindow tau≤ (tau/16)/1000 := min_le_right _ _
    rw [hboundary]
    linarith only [hh,htau]
  obtain ⟨hm6,hms,_hphaseLow,_hphaseHigh⟩ := middle_depth_bounds stop hstop6
  have hstopm : stop≤ 2*middleDepth stop := by dsimp [middleDepth]; omega
  have hN : middleDepth stop+s-3≤ 2*stop := by omega
  have hNm : middleDepth stop≤ middleDepth stop+s-3 := by omega
  have hcap : 4*stop≤ level := by omega
  have hstopmR : (stop:ℝ)≤ 2*(middleDepth stop:ℝ) := by exact_mod_cast hstopm
  have hNR : ((middleDepth stop+s-3:ℕ):ℝ)≤ 2*(stop:ℝ) := by exact_mod_cast hN
  have hNmR : (middleDepth stop:ℝ)≤ ((middleDepth stop+s-3:ℕ):ℝ) := by exact_mod_cast hNm
  have hcapR : 4*(stop:ℝ)≤ (level:ℝ) := by exact_mod_cast hcap
  have hwindowHalf : rankWindow tau≤ 1/2 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (by norm_num))
  have hlevel0 := Nat.cast_nonneg (α:=ℝ) level
  refine ⟨by omega,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hw hlevel0
    nlinarith only [hh,hlo,hstopmR,hNmR]
  · have hh := mul_le_mul_of_nonneg_right hwindowHalf hlevel0
    nlinarith only [hNR,hcapR,hh]

/-- One cutoff, fixed after c and epsilon and before D, pays both the
original stopping-window constant and the normalized affine error at all
four possible ranks. -/
theorem exists_original_test_cutoff (c epsilon : ℝ) (hc : 0< c) (hc1 : c≤ 1)
    (he : 0< epsilon) (he9 : epsilon≤ 1/9) :
    ∃delta0 : ℝ,0< delta0 ∧ delta0≤ 1/8 ∧
      ∀delta r tau : ℝ,0< delta → delta≤ delta0 → 0< r → r≤ 1 →
      ∀rank : Fin 4,r≤ delta^(cutoff c rank) → 0< tau → tau≤ 1/2 → tau≤ 4*cutoff c rank →
      ∀level stop : ℕ,delta=(2:ℝ)⁻¹^level → 6≤ stop → stop≤ level/4 →
        48*((2^stop:ℕ):ℝ)*r=1 →
      ∃s : ℕ,6≤ s ∧ s≤ middleDepth stop ∧ middleDepth stop+s-3≤ level ∧
        rankWindow tau*(level:ℝ)≤ ((middleDepth stop+s-3:ℕ):ℝ) ∧
        ((middleDepth stop+s-3:ℕ):ℝ)≤ (1-rankWindow tau)*(level:ℝ) ∧
        (5/4:ℝ)*((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))^(1-2*epsilon)≤ (64/((2^s:ℕ):ℝ))/8 ∧
        (64:ℝ)/((2^s:ℕ):ℝ)≤ 160*r^(1/3:ℝ) := by
  let amin : ℝ := c^3/8
  have ha : 0< amin := by dsimp [amin]; positivity
  obtain ⟨d0,hd0,_hd01,hPower⟩ := exists_small_power_cutoff (show 0< amin*epsilon/2 by positivity)
    (by norm_num : (0:ℝ)< 1/800)
  obtain ⟨d1,hd1,_hd11,hStop⟩ := exists_small_power_cutoff (show 0< amin/2 by positivity)
    (by norm_num : (0:ℝ)< 1/48)
  refine ⟨min (1/8) (min d0 d1),lt_min (by norm_num) (lt_min hd0 hd1),min_le_left _ _,?_⟩
  intro delta r tau hd hsmall hr hr1 rank hrdelta htau htauHalf htauCut level stop hdy hstop6 hstopCap hidentity
  have hd1' : delta≤ 1 := (hsmall.trans (min_le_left _ _)).trans (by norm_num)
  have hdelta0 := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdelta1 := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hapos,_haUpper,haLow⟩ := cutoff_bounds hc hc1 rank
  have hstopSmall : delta^(cutoff c rank/2)≤ 1/48 :=
    (Real.rpow_le_rpow_of_exponent_ge hd hd1' (by dsimp [amin]; linarith only [haLow])).trans
      (hStop delta hd hdelta1)
  have hroot := middle_scale_root_bound hr stop hstop6 hidentity
  have hD := (middle_scale_bounds stop hstop6 r hidentity).1
  have hDeltaSmall : ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))^epsilon≤ 1/10 := by
    have h1 := Real.rpow_le_rpow hD.le hroot he.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤ 80) (Real.rpow_nonneg hr.le _),←Real.rpow_mul hr.le] at h1
    have h80 : (80:ℝ)^epsilon≤ 80 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1:ℝ)≤ 80) (show epsilon≤ 1 by linarith only [he9])
    have hrPower := Real.rpow_le_rpow hr.le hrdelta (show 0≤ (1/2:ℝ)*epsilon by positivity)
    rw [←Real.rpow_mul hd.le] at hrPower
    have hdeltaPower : delta^(cutoff c rank*((1/2:ℝ)*epsilon))≤ delta^(amin*epsilon/2) :=
      Real.rpow_le_rpow_of_exponent_ge hd hd1' (by
        have hh := mul_le_mul_of_nonneg_right haLow he.le
        dsimp [amin]
        nlinarith only [hh])
    have hh := h1.trans (mul_le_mul h80 (hrPower.trans hdeltaPower)
      (Real.rpow_nonneg hr.le _) (by norm_num))
    have hcut := hPower delta hd hdelta0
    nlinarith only [hh,hcut]
  obtain ⟨s,hs,hsm,_hLower,_hUpper,hError,hRho⟩ := exists_actual_test_scale (middleDepth stop)
    (middle_depth_bounds stop hstop6).1 hr hr1 he he9 hDeltaSmall hroot
  obtain ⟨hf,hlo,hhi⟩ := original_angular_depth_window hd hapos.le htau htauHalf level stop s hdy
    hstop6 hstopCap hidentity hrdelta hstopSmall htauCut hs hsm
  exact ⟨s,hs,hsm,hf,hlo,hhi,hError,hRho⟩

end NativeAngularTestSourceWindow
