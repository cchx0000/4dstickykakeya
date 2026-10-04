import Theorems.Thm_StickyKakeya4_native_original_concentrated_slice_closure
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

noncomputable section
namespace OriginalThreeDimensionalOwnerScaleCutoff
open OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeFrostman
open NativeQuarterScaleParameters

/-- The ORIGINAL rich-tube gain and two-Frostman law make the real owner
perturbation small. The cutoff is uniform over eta<=zeta/100 and precedes
all original sources and selected physical radii. -/
theorem exists_original_owner_scale_cutoff (zeta A epsilon C : ℝ)
    (hzeta : 0 < zeta) (hzeta1 : zeta < 1) (hA : 0 < A)
    (_hepsilon : 0 < epsilon) (hepsmall : epsilon ≤ zeta/100) (hC : 0 < C) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ zeta/100 →
      ∀ (P : Finset Point3) (z : Pair3) (rho : ℝ),
        P.Nonempty → delta ≤ rho → rho ≤ 1 →
        (∀ p∈P, ∀ j, |p j| ≤ 1) →
        (∀ p∈P, ∀ R : ℝ, delta ≤ R → R ≤ 1 →
          ((P.filter (fun q => distance3 p q ≤ R)).card : ℝ) ≤ delta^(-eta)*R^2*P.card) →
        delta^(-(zeta-zeta/100))*rho^(2-zeta/100)*P.card ≤
          A*(physicalPairTube3 P rho z).card →
        let r := delta^(2*eta)
        let Delta := 54*rho/r
        delta ≤ Delta/32 ∧ Delta/32 ≤ delta^(zeta/5) ∧
          C*Delta/r ≤ delta^((51/50:ℝ)*epsilon) := by
  let kappa := (zeta-zeta/100)/(4*(1-zeta/100))
  let a := (51/50:ℝ)*epsilon
  have hg : zeta/100 < 1 := by linarith only [hzeta1]
  have hgap : zeta/100 < zeta := by linarith only [hzeta]
  have hk : (99/400:ℝ)*zeta ≤ kappa := by
    dsimp [kappa]
    apply (le_div_iff₀ (show 0 < 4*(1-zeta/100) by linarith only [hg])).mpr
    nlinarith only [sq_nonneg zeta]
  let b0 := kappa-zeta/50-zeta/5
  let b1 := kappa-zeta/25-a
  have hb0 : 0 < b0 := by dsimp [b0]; linarith only [hk,hzeta]
  have hb1 : 0 < b1 := by dsimp [b1,a]; linarith only [hk,hzeta,hepsmall]
  obtain ⟨dR,hdR,hdR1,hR⟩ := exists_original_rich_tube_scale_cutoff zeta (zeta/100) A hgap hg hA
  obtain ⟨d0,hd0,_hd01,h0⟩ := exists_small_power_cutoff hb0 (by norm_num : (0:ℝ) < 32/54)
  obtain ⟨d1,hd1,_hd11,h1⟩ := exists_small_power_cutoff hb1 (show 0 < 1/(54*C) by positivity)
  refine ⟨min dR (min d0 d1),lt_min hdR (lt_min hd0 hd1),(min_le_left _ _).trans hdR1,?_⟩
  intro delta hd hsmall eta heta hetaMax P z rho hP hquery hrho1 hbox hfrostman hgain
  have hsmallR := hsmall.trans (min_le_left _ _)
  have hsmall0 := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall1 := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdOne : delta ≤ 1 := hsmallR.trans hdR1
  have hrho : 0 < rho := hd.trans_le hquery
  have hdecay := hR delta hd hsmallR eta heta
    (show eta ≤ (zeta-zeta/100)/2 by linarith only [hetaMax,hzeta]) P z rho hP hquery hrho1 hbox hfrostman hgain
  change rho ≤ delta^kappa at hdecay
  let r := delta^(2*eta)
  let Delta := 54*rho/r
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := Real.rpow_le_one hd.le hdOne (by linarith only [heta])
  have hD : 0 < Delta := by dsimp [Delta]; positivity
  have hDr : Delta*r=54*rho := by dsimp [Delta]; field_simp
  have hlower : delta ≤ Delta/32 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 32)).mpr
    have hh := mul_le_mul_of_nonneg_left hr1 hD.le
    rw [hDr,mul_one] at hh
    linarith only [hh,hquery,hd]
  have hDpower : Delta ≤ 54*delta^(kappa-2*eta) := by
    rw [Real.rpow_sub hd]
    change 54*rho/r ≤ 54*(delta^kappa/r)
    have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdecay hr.le) (by norm_num : (0:ℝ) ≤ 54)
    simpa only [mul_div_assoc] using hh
  have hDworst : Delta ≤ 54*delta^(kappa-zeta/50) :=
    hDpower.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hd hdOne (by linarith only [hetaMax])) (by norm_num))
  have hm0 := mul_le_mul_of_nonneg_right (h0 delta hd hsmall0) (Real.rpow_nonneg hd.le (zeta/5))
  have he0 : delta^b0*delta^(zeta/5)=delta^(kappa-zeta/50) := by
    rw [← Real.rpow_add hd]
    congr 1
    dsimp [b0]
    ring
  rw [he0] at hm0
  have hupper : Delta/32 ≤ delta^(zeta/5) := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 32)).mpr
    nlinarith only [hm0,hDworst]
  have hDRpower : Delta/r ≤ 54*delta^(kappa-4*eta) := by
    have hh := div_le_div_of_nonneg_right hDpower hr.le
    have he : delta^(kappa-2*eta)/r=delta^(kappa-4*eta) := by
      dsimp [r]
      rw [← Real.rpow_sub hd]
      congr 1
      ring
    simpa only [mul_div_assoc,he] using hh
  have hDRworst : Delta/r ≤ 54*delta^(kappa-zeta/25) :=
    hDRpower.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hd hdOne (by linarith only [hetaMax])) (by norm_num))
  have hm1 := mul_le_mul_of_nonneg_right (h1 delta hd hsmall1) (Real.rpow_nonneg hd.le a)
  have he1 : delta^b1*delta^a=delta^(kappa-zeta/25) := by
    rw [← Real.rpow_add hd]
    congr 1
    dsimp [b1]
    ring
  rw [he1] at hm1
  have hscaled := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ 54*C by positivity)
  have heC : (54*C)*(1/(54*C)*delta^a)=delta^a := by field_simp
  rw [heC] at hscaled
  have hfinal := mul_le_mul_of_nonneg_left hDRworst hC.le
  refine ⟨hlower,hupper,?_⟩
  change C*Delta/r ≤ delta^a
  calc
    C*Delta/r = C*(Delta/r) := mul_div_assoc C Delta r
    _ ≤ C*(54*delta^(kappa-zeta/25)) := hfinal
    _ = 54*C*delta^(kappa-zeta/25) := by ring
    _ ≤ delta^a := hscaled

end OriginalThreeDimensionalOwnerScaleCutoff
