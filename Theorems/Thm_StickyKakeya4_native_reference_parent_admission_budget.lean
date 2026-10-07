import Theorems.Thm_StickyKakeya4_native_normalized_population_admission_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000

noncomputable section
namespace NativeReferenceParentAdmissionBudget
open StickyKakeya4 NativeNormalizedPopulationAdmissionBudget

/-- Once the local exponents are chosen AFTER the rank cutoff, only seed
needs to be small. This cutoff uses no rank loss, rank radius, or history. -/
theorem exists_first_stage_admission_cutoff (localEta profileExp sigma0 : ℝ)
    (hlocal : 0 < localEta) (hprofile : 0 < profileExp) (hsigma0 : 0 < sigma0) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/8 ∧
      ∀delta Delta eta zeta seed : ℝ,
        0 < delta → delta ≤ delta0 → 0 < Delta → delta ≤ Delta^2 →
        eta ≤ seed/8 → zeta ≤ seed/256 → seed ≤ localEta → seed ≤ profileExp →
        let sigma := delta/Delta
        sigma ≤ sigma0 ∧
        (2048:ℝ)^3*sigma^localEta ≤ delta^zeta ∧
        (373248*512^4:ℝ)*sigma^localEta ≤ delta^(eta+zeta) ∧
        (1024*175616*NativeOriginalPrunedMass.volumeConstant)*sigma^localEta ≤ delta^(seed/8+2*zeta) ∧
        (64:ℝ)^3*sigma^profileExp ≤ delta^zeta := by
  let C : ℝ := max ((2048:ℝ)^3) (max (373248*512^4:ℝ) (1024*175616*NativeOriginalPrunedMass.volumeConstant))
  have hC : 0 ≤ C := le_trans (by positivity) (le_max_left _ _)
  obtain ⟨dA,hdA,hdA1,HA⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < localEta/4 by positivity) hC (show (0:ℝ)<1 by norm_num)
  obtain ⟨dP,hdP,_hdP1,HP⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < profileExp/4 by positivity) (show (0:ℝ) ≤ 64^3 by positivity) (show (0:ℝ)<1 by norm_num)
  obtain ⟨dS,hdS,_hdS1,HS⟩ := exists_positive_rpow_absorption_threshold
    (show (0:ℝ)<1/2 by norm_num) (show (0:ℝ)≤1 by norm_num) hsigma0
  let delta0 := min (1/8) (min dA (min dP dS))
  refine ⟨delta0,lt_min (by norm_num) (lt_min hdA (lt_min hdP hdS)),min_le_left _ _,?_⟩
  intro delta Delta eta zeta seed hd hsmall hDelta hsquare heta hzeta hseedLocal hseedProfile
  have hdA' : delta ≤ dA := (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hdP' : delta ≤ dP := ((hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hdS' : delta ≤ dS := ((hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hd1 := hdA'.trans hdA1
  have hroot := local_scale_root hd hDelta hsquare
  have hSigma : 0 ≤ delta/Delta := by positivity
  have hAll := HA delta hd hdA'
  have hAd : (2048:ℝ)^3*delta^(localEta/4) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hAll
  have hCW : (373248*512^4:ℝ)*delta^(localEta/4) ≤ 1 :=
    (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (by positivity)).trans hAll
  have hDen : (1024*175616*NativeOriginalPrunedMass.volumeConstant)*delta^(localEta/4) ≤ 1 :=
    (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)).trans hAll
  have hVolume := NativeOriginalPrunedMass.volumeConstant_pos
  refine ⟨hroot.trans (by simpa only [one_mul] using HS delta hd hdS'),?_,?_,?_,?_⟩
  · exact pay_local_root hd hd1 hSigma hlocal.le (by positivity) hroot
      (by linarith only [hzeta,hseedLocal,hlocal]) hAd
  · exact pay_local_root hd hd1 hSigma hlocal.le (by positivity) hroot
      (by linarith only [heta,hzeta,hseedLocal,hlocal]) hCW
  · exact pay_local_root hd hd1 hSigma hlocal.le (by positivity) hroot
      (by linarith only [hzeta,hseedLocal,hlocal]) hDen
  · exact pay_local_root hd hd1 hSigma hprofile.le (by positivity) hroot
      (by linarith only [hzeta,hseedProfile,hprofile]) (HP delta hd hdP')

end NativeReferenceParentAdmissionBudget
