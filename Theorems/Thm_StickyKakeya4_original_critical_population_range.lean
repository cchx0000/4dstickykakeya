import Theorems.Thm_StickyKakeya4_original_critical_cap_parameter_transfer
import Theorems.Thm_StickyKakeya4_native_original_shading_width_cutoff
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

noncomputable section
namespace OriginalCriticalPopulationRange
open OriginalPairStripGeometry OriginalCriticalWidthBound OriginalCriticalCapParameterTransfer
open OriginalClippedUnitTube OriginalArbitraryStripCapCharge NativeQuarterScaleParameters

/-- The actual critical physical query bounds the population of the same
family at its actual coarse scale 3rho. -/
theorem original_query_population_upper
    (S : Finset Pair) (delta rho eps1 C0 : ℝ)
    (hd : 0<delta) (hrho : 0<rho) (hmesh : delta≤rho) (heps : 0≤eps1) (hC0 : 0≤C0)
    (hquery : 432*criticalWidth rho S+16*rho≤C0*delta^(4*eps1)) :
    (S.card : ℝ)≤(C0/432)^2*(3*rho)^(-2+8*eps1) := by
  have hr : 0<3*rho := by positivity
  have hpow : delta^(4*eps1)≤(3*rho)^(4*eps1) := Real.rpow_le_rpow hd.le
    (by linarith only [hmesh,hrho]) (by positivity)
  have hW : criticalWidth rho S≤(C0/432)*(3*rho)^(4*eps1) := by
    have hh := mul_le_mul_of_nonneg_left hpow hC0
    nlinarith only [hquery,hrho,hh]
  have hsquared := pow_le_pow_left₀
    (show 0≤criticalWidth rho S by dsimp [criticalWidth]; positivity) hW 2
  have hid : (3*rho)^2*((C0/432)^2*(3*rho)^(-2+8*eps1))=
      ((C0/432)*(3*rho)^(4*eps1))^2 := by
    rw [mul_pow (C0/432) ((3*rho)^(4*eps1)) 2,← Real.rpow_mul_natCast hr.le (4*eps1) 2]
    calc
      _ = (C0/432)^2*((3*rho)^(2:ℝ)*(3*rho)^(-2+8*eps1)) := by rw [Real.rpow_two]; ring
      _ = _ := by rw [← Real.rpow_add hr]; congr 2; ring
  apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hr)).mp
  rw [hid]
  simpa only [criticalWidth,mul_pow,Real.sq_sqrt (Nat.cast_nonneg S.card)] using hsquared

/-- Fixed coefficients are absorbed using the genuine original upper
scale rho≤delta^kappa; the cutoff precedes S and rho. -/
theorem exists_original_population_upper_cutoff (eps1 kappa C0 : ℝ)
    (heps : 0<eps1) (hkappa : 0<kappa) (hC0 : 0≤C0) :
    ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧
      ∀ delta : ℝ, 0<delta → delta≤delta0 →
      ∀ (rho : ℝ) (S : Finset Pair), delta≤rho → rho≤delta^kappa →
        432*criticalWidth rho S+16*rho≤C0*delta^(4*eps1) →
        0<3*rho ∧ 3*rho≤1/2 ∧ (S.card : ℝ)≤(3*rho)^(-2+7*eps1) := by
  let A := (C0/432)^2
  let B := max 1 (A*3^eps1)
  have hB : 1≤B := le_max_left _ _
  have hBp : 0<B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨d1,hd1,hd11,hcut1⟩ := exists_small_power_cutoff (mul_pos hkappa heps)
    (show 0<1/B by positivity)
  obtain ⟨d2,hd2,_hd21,hcut2⟩ := exists_small_power_cutoff hkappa
    (by norm_num : (0:ℝ)<1/6)
  refine ⟨min d1 d2,lt_min hd1 hd2,(min_le_left _ _).trans hd11,?_⟩
  intro delta hd hsmall rho S hmesh hdecay hquery
  have hrho : 0<rho := hd.trans_le hmesh
  have hr : 0<3*rho := by positivity
  have hscale := hcut2 delta hd (hsmall.trans (min_le_right _ _))
  have hsmallr : 3*rho≤1/2 := by linarith only [hdecay,hscale]
  have hcut := hcut1 delta hd (hsmall.trans (min_le_left _ _))
  have hpow : (3*rho)^eps1≤3^eps1*delta^(kappa*eps1) := by
    have hh := Real.rpow_le_rpow hr.le (mul_le_mul_of_nonneg_left hdecay (by norm_num : (0:ℝ)≤3)) heps.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤3) (Real.rpow_nonneg hd.le kappa),
      ← Real.rpow_mul hd.le] at hh
    exact hh
  have habsorb : A*(3*rho)^eps1≤1 := by
    have h1 := mul_le_mul_of_nonneg_left hpow (show 0≤A by dsimp [A]; positivity)
    have h2 := mul_le_mul_of_nonneg_right (le_max_right 1 (A*3^eps1))
      (Real.rpow_nonneg hd.le (kappa*eps1))
    have h3 := mul_le_mul_of_nonneg_left hcut hBp.le
    have he : B*(1/B)=1 := by field_simp
    rw [he] at h3
    nlinarith only [h1,h2,h3]
  have hupper := original_query_population_upper S delta rho eps1 C0 hd hrho hmesh heps.le hC0 hquery
  refine ⟨hr,hsmallr,?_⟩
  have hid : A*(3*rho)^(-2+8*eps1)=
      (A*(3*rho)^eps1)*(3*rho)^(-2+7*eps1) := by
    rw [mul_assoc,← Real.rpow_add hr]
    congr 1
    ring
  change (S.card : ℝ)≤_ at hupper
  change (S.card : ℝ)≤A*(3*rho)^(-2+8*eps1) at hupper
  rw [hid] at hupper
  have hh := mul_le_mul_of_nonneg_right habsorb (Real.rpow_nonneg hr.le (-2+7*eps1))
  exact hupper.trans (by simpa only [one_mul] using hh)

/-- Actual lower and upper populations determine the exact effective
exponent in a fixed compact interval. This does not assert a uniform A.3
gain merely from compactness of that interval. -/
theorem original_effective_family_exponent
    (S : Finset Pair) (r chi eps1 : ℝ) (hr : 0<r) (hr1 : r<1)
    (hchi : 0<chi) (heps : 0<eps1) (hS : S.Nonempty)
    (hlower : r^(-chi)≤(S.card : ℝ)) (hupper : (S.card : ℝ)≤r^(-2+7*eps1)) :
    ∃ tbar : ℝ, r^(-tbar)=(S.card : ℝ) ∧ chi≤tbar ∧ tbar≤2-7*eps1 ∧
      0<tbar ∧ tbar<2 ∧
      0<min (chi/2) (7*eps1/2) ∧ min (chi/2) (7*eps1/2)≤min tbar (2-tbar) := by
  have hN : 0<(S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hlog : Real.log r≠0 := ne_of_lt (Real.log_neg hr hr1)
  let tbar := -(Real.log (S.card : ℝ)/Real.log r)
  have heq : r^(-tbar)=(S.card : ℝ) := by
    apply (Real.mul_log_eq_log_iff hr hN).mp
    dsimp [tbar]
    field_simp
  have hlo : chi≤tbar := by
    rw [← heq] at hlower
    have hh := (Real.rpow_le_rpow_left_iff_of_base_lt_one hr hr1).mp hlower
    linarith only [hh]
  have hhi : tbar≤2-7*eps1 := by
    rw [← heq] at hupper
    have hh := (Real.rpow_le_rpow_left_iff_of_base_lt_one hr hr1).mp hupper
    linarith only [hh]
  refine ⟨tbar,heq,hlo,hhi,hchi.trans_le hlo,by linarith only [hhi,heps],
    lt_min (by positivity) (by positivity),?_⟩
  apply le_min
  · exact (min_le_left _ _).trans (by linarith only [hlo,hchi])
  · exact (min_le_right _ _).trans (by linarith only [hhi,heps])

end OriginalCriticalPopulationRange
