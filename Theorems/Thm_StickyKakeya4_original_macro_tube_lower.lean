import Theorems.Thm_StickyKakeya4_original_macro_height_incidence_density
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace OriginalMacroTubeLower
open Classical Finset TwoTubePathCollisionCount OriginalWWitnessCounts
variable {P T : Type*} [DecidableEq P] [DecidableEq T]
/-- The other tube-count side of Eq146 follows from the SAME macro point
 mass, original angular degree and literal tube-height occupancy. -/
theorem original_macro_tube_lower (I : Finset (P × T)) (height : P → ℝ) (Z : Finset ℝ)
    (hZ : Z.Nonempty) {delta q kappa CP Cocc c : ℝ}
    (hd : 0 < delta) (hq : 0 < q) (hCP : 0 < CP) (hCocc : 0 < Cocc) (hc : 0 ≤ c)
    (hheight : ∀ p ∈ points I, height p ∈ Z)
    (hpoint : q^(3-kappa)*(Z.card:ℝ) ≤ CP*delta^(3-kappa)*(points I).card)
    (hdegree : c*(points I).card ≤ delta^kappa*(I.card:ℝ))
    (hocc : ∀ t z, ((pointsAt I height t z).card:ℝ) ≤ Cocc) :
    (c/(CP*Cocc))*(q/delta)^3 ≤ q^kappa*(tubes I).card := by
  have hZ0 : (0:ℝ) < Z.card := Nat.cast_pos.mpr hZ.card_pos
  have hdCancel : delta^(3-kappa)*delta^kappa=delta^3 := by
    rw [←Real.rpow_add hd,show (3-kappa)+kappa=(3:ℝ) by ring]
    norm_num
  have hqCancel : q^kappa*q^(3-kappa)=q^3 := by
    rw [←Real.rpow_add hq,show kappa+(3-kappa)=(3:ℝ) by ring]
    norm_num
  have hmass : c*q^(3-kappa)*(Z.card:ℝ) ≤ CP*delta^3*(I.card:ℝ) := by
    calc
      _ = c*(q^(3-kappa)*(Z.card:ℝ)) := by ring
      _ ≤ c*(CP*delta^(3-kappa)*(points I).card) := mul_le_mul_of_nonneg_left hpoint hc
      _ = (CP*delta^(3-kappa))*(c*(points I).card) := by ring
      _ ≤ (CP*delta^(3-kappa))*(delta^kappa*(I.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hdegree (by positivity)
      _ = CP*(delta^(3-kappa)*delta^kappa)*(I.card:ℝ) := by ring
      _ = _ := by rw [hdCancel]
  have htotal := OriginalIncidenceHeightPopulation.original_incidence_height_product I height Z hCocc.le hheight hocc
  have hcancel : c*q^(3-kappa) ≤ CP*Cocc*delta^3*(tubes I).card := by
    apply (mul_le_mul_iff_left₀ hZ0).mp
    calc
      _ ≤ CP*delta^3*(I.card:ℝ) := hmass
      _ ≤ CP*delta^3*(Cocc*(Z.card:ℝ)*(tubes I).card) :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left hcancel (Real.rpow_pos_of_pos hq kappa).le
  have hfinal : c*q^3 ≤ (CP*Cocc*delta^3)*(q^kappa*(tubes I).card) := by
    calc
      _ = q^kappa*(c*q^(3-kappa)) := by rw [←hqCancel]; ring
      _ ≤ q^kappa*(CP*Cocc*delta^3*(tubes I).card) := hh
      _ = _ := by ring
  have hdivide : (c*q^3)/(CP*Cocc*delta^3) ≤ q^kappa*(tubes I).card :=
    (div_le_iff₀ (show 0 < CP*Cocc*delta^3 by positivity)).mpr
      (by simpa only [mul_comm] using hfinal)
  calc
    _ = (c*q^3)/(CP*Cocc*delta^3) := by field_simp
    _ ≤ _ := hdivide
end OriginalMacroTubeLower
