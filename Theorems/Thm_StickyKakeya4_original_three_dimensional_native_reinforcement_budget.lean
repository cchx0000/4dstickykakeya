import Theorems.Thm_StickyKakeya4_native_original_concentrated_slice_closure
import Theorems.Thm_StickyKakeya4_original_three_dimensional_marked_slice_witness
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

noncomputable section
namespace OriginalThreeDimensionalNativeReinforcementBudget
open OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalAveragedSliceEnergy OriginalThreeDimensionalRegularizedMarkedSlice
open OriginalThreeDimensionalSliceParameterChoice OriginalPhysicalTubeScaleSelection
open NativeQuarterScaleParameters

/-- The actual selected energy-to-edge ratio pays for reinforcement with
one E/L loss, including the actual half-graph chart choice. All masses are original point or original pair populations. -/
theorem original_selected_ratio_reinforcement_budget
    (Q S : Finset Point3) (GG GP : Finset Pair3) (delta rho Delta zeta E L : ℝ)
    (hd : 0 < delta) (hrho : 0 < rho) (hDelta : 0 ≤ Delta)
    (hE : 0 ≤ E) (hL : 0 < L) (hSQ : S⊆Q)
    (hselected : L*sliceEnergy Q Delta ≤ E*GG.card)
    (hretained : (GG.card : ℝ) ≤ 2*GP.card)
    (hsmall : 960000*(E/L)*(Delta/rho)^2*delta^(5*zeta/12) ≤ 1) :
    480000*sliceEnergy Q Delta*(delta^(-zeta/8)*Delta*S.card)^2 ≤
      (delta^(-zeta/3)*rho*Q.card)^2*GP.card := by
  have hdiv : 960000*(E/L)*(Delta/rho)^2*delta^(5*zeta/12)=
      (960000*E*Delta^2*delta^(5*zeta/12))/(L*rho^2) := by
    field_simp
  rw [hdiv] at hsmall
  have hsmall' := (div_le_one (show 0 < L*rho^2 by positivity)).mp hsmall
  have hpow : delta^(5*zeta/12)*(delta^(-zeta/3))^2=(delta^(-zeta/8))^2 := by
    rw [← Real.rpow_mul_natCast hd.le,← Real.rpow_mul_natCast hd.le,← Real.rpow_add hd]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right hsmall'
    (show 0 ≤ (delta^(-zeta/3))^2*(Q.card : ℝ)^2 by positivity)
  have hscalarQ : 960000*E*(delta^(-zeta/8)*Delta*Q.card)^2 ≤
      L*(delta^(-zeta/3)*rho*Q.card)^2 := by
    calc
      _ = (960000*E*Delta^2)*(delta^(5*zeta/12)*(delta^(-zeta/3))^2)*(Q.card : ℝ)^2 := by
        rw [hpow]
        ring
      _ ≤ (L*rho^2)*((delta^(-zeta/3))^2*(Q.card : ℝ)^2) := by nlinarith only [hm]
      _ = _ := by ring
  have hcard : (S.card : ℝ) ≤ Q.card := Nat.cast_le.mpr (Finset.card_le_card hSQ)
  have hell : (delta^(-zeta/8)*Delta*S.card)^2 ≤ (delta^(-zeta/8)*Delta*Q.card)^2 := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left hcard (by positivity)
  have hscalar := (mul_le_mul_of_nonneg_left hell (show 0 ≤ 960000*E by positivity)).trans hscalarQ
  have hratio := hselected.trans (mul_le_mul_of_nonneg_left hretained hE)
  have hfirst := mul_le_mul_of_nonneg_right hratio
    (show 0 ≤ 480000*(delta^(-zeta/8)*Delta*S.card)^2 by positivity)
  have hlast := mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg GP.card)
  apply (mul_le_mul_iff_of_pos_left hL).mp
  nlinarith only [hfirst,hlast]

/-- Original graph density, the actual original mesh menu and the explicit
slice-energy budget pay the numerical reinforcement condition at a true
source-independent cutoff. Both occurrences of Delta/rho remain explicit. -/
theorem exists_original_native_reinforcement_cutoff (zeta eta B : ℝ)
    (heta : 0 < eta) (hmargin : (B+10)*eta < 5*zeta/12) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
      ∀ (P : Finset Point3) (G : Finset Pair3) (rho : ℝ) (n : ℕ),
        P.Nonempty → 0 < rho → delta ≤ dyadicRadius n →
        delta^(B*eta)*(P.card : ℝ)^2 ≤ G.card →
        let Delta := 54*rho/delta^(2*eta)
        let E := energyBudget P rho Delta (delta^(-eta)) n
        let L := (1/(8*rho))*(G.card : ℝ)
        960000*(E/L)*(Delta/rho)^2*delta^(5*zeta/12) ≤ 1 := by
  let C : ℝ := 188073993830400000000
  let b := 5*zeta/12-(B+10)*eta
  have hb : 0 < b := by dsimp [b]; linarith only [hmargin]
  obtain ⟨dM,hdM,hdM1,hM⟩ := exists_original_coarse_menu_cutoff eta heta
  obtain ⟨dC,hdC,_hdC1,hC⟩ := exists_small_power_cutoff hb (show 0 < 1/C by dsimp [C]; norm_num)
  refine ⟨min dM dC,lt_min hdM hdC,(min_le_left _ _).trans hdM1,?_⟩
  intro delta hd hsmall P G rho n hP hrho hquery hG
  have hmenu := hM delta hd (hsmall.trans (min_le_left _ _)) n hquery
  have hpower : C*delta^b ≤ 1 := by
    have hh := (le_div_iff₀ (show 0 < C by dsimp [C]; norm_num)).mp
      (hC delta hd (hsmall.trans (min_le_right _ _)))
    nlinarith only [hh]
  have hpc : 0 < (P.card : ℝ) := by exact_mod_cast hP.card_pos
  have hgc : 0 < (G.card : ℝ) := (show 0 < delta^(B*eta)*(P.card : ℝ)^2 by positivity).trans_le hG
  let r := delta^(2*eta)
  let Delta := 54*rho/r
  let E := energyBudget P rho Delta (delta^(-eta)) n
  let L := (1/(8*rho))*(G.card : ℝ)
  have hr : 0 < r := by dsimp [r]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have he : 960000*E*Delta^2*delta^(5*zeta/12)=
      (C/8)*(rho*(P.card : ℝ)^2)*(((n:ℝ)+1)*delta^(-eta))*
        (delta^(5*zeta/12)/(r^4)) := by
    dsimp [E,energyBudget,Delta,C]
    field_simp
    ring
  have hmenu' := mul_le_mul_of_nonneg_right hmenu (Real.rpow_nonneg hd.le (-eta))
  have hleft := mul_le_mul_of_nonneg_left hmenu'
    (show 0 ≤ (C/8)*(rho*(P.card : ℝ)^2)*(delta^(5*zeta/12)/(r^4)) by positivity)
  have hexp : delta^(-eta)*delta^(-eta)*(delta^(5*zeta/12)/(r^4))=
      delta^b*delta^(B*eta) := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast hd.le,← Real.rpow_sub hd]
    repeat rw [← Real.rpow_add hd]
    congr 1
    dsimp [b]
    ring
  have hleft' : 960000*E*Delta^2*delta^(5*zeta/12) ≤
      (C*delta^b)*(delta^(B*eta)*rho*(P.card : ℝ)^2/8) := by
    rw [he]
    calc
      _ ≤ (C/8)*(rho*(P.card : ℝ)^2)*(delta^(-eta)*delta^(-eta)*(delta^(5*zeta/12)/(r^4))) := by
        nlinarith only [hleft]
      _ = _ := by rw [hexp]; ring
  have hpaid := hleft'.trans (mul_le_mul_of_nonneg_right hpower
    (show 0 ≤ delta^(B*eta)*rho*(P.card : ℝ)^2/8 by positivity))
  have hdense := mul_le_mul_of_nonneg_right hG (show 0 ≤ rho/8 by positivity)
  have hscalar : 960000*E*Delta^2*delta^(5*zeta/12) ≤ L*rho^2 := by
    have hident : L*rho^2=(G.card : ℝ)*(rho/8) := by dsimp [L]; field_simp
    rw [hident]
    nlinarith only [hpaid,hdense]
  have hident : 960000*(E/L)*(Delta/rho)^2*delta^(5*zeta/12)=
      (960000*E*Delta^2*delta^(5*zeta/12))/(L*rho^2)  := by field_simp
  change 960000*(E/L)*(Delta/rho)^2*delta^(5*zeta/12) ≤ 1
  rw [hident]
  exact (div_le_one (show 0 < L*rho^2 by positivity)).mpr hscalar

end OriginalThreeDimensionalNativeReinforcementBudget
