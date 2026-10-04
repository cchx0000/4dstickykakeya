import Theorems.Thm_StickyKakeya4_working_scale_profile_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

namespace NativeAlignmentScaleSeparation
open NativeDyadicTubeStopping NativeAngularChartSelection CoverProfileStopping

lemma top_bracket_lower {delta x : ℝ} (hdelta : 0 < delta) (hx : 0 ≤ x)
    (hsmall : delta ≤ (128:ℝ)⁻¹^2) (htop : (128:ℝ)⁻¹ ≤ delta*x) :
    delta^(-(1:ℝ)/2) ≤ x := by
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ (128:ℝ)⁻¹) htop 2
  have hsq : delta ≤ delta^2*x^2 := by nlinarith only [hsmall,hs]
  have hb : 1 ≤ delta*x^2 := by
    apply (mul_le_mul_iff_left₀ hdelta).mp
    nlinarith only [hsq]
  have hinv : delta⁻¹ ≤ x^2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hdelta).mpr
    nlinarith only [hb]
  have heq : (delta^(-(1:ℝ)/2))^2 = delta⁻¹ := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hdelta.le]
    norm_num [Real.rpow_neg_one]
  have hz : 0 < delta^(-(1:ℝ)/2) := Real.rpow_pos_of_pos hdelta _
  nlinarith

lemma root_of_nat_power {b out e : ℝ} (hb : 0 ≤ b) (hout : 0 ≤ out)
    {m : ℕ} (hm : 0 < m) (h : b^e ≤ out^m) : b^(e/(m:ℝ)) ≤ out := by
  have hmR : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  calc
    _ = (b^e)^((m:ℝ)⁻¹) := by rw [←Real.rpow_mul hb]; congr 1
    _ ≤ (out^m)^((m:ℝ)⁻¹) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hb _) h (by positivity)
    _ = out := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hout,mul_inv_cancel₀ hmR.ne',Real.rpow_one]

/-- The selected adjacent scales have a genuine positive power gap relative
 to the ORIGINAL delta. This is independent of later profile-loss absorption. -/
theorem original_delta_output_separation {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (p : alpha → Plane) {delta epsilon K t : ℝ} {Nold : ℕ} {E : Finset alpha}
    (D : StoppedProfile p delta epsilon K t Nold E)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hsmall : delta ≤ (128:ℝ)⁻¹^2)
    (htop : (128:ℝ)⁻¹ ≤ scale delta Nold)
    (k : ℕ) {m : ℕ} (hm : 0 < m) :
    0 < separationExponent epsilon/(2*(m:ℝ)) ∧
    delta^(- (separationExponent epsilon/(2*(m:ℝ)))) ≤
      64*(scale delta (workingLevel D.pair.1 (D.pair.2-D.pair.1) m (k+1)) /
        scale delta (workingLevel D.pair.1 (D.pair.2-D.pair.1) m k)) := by
  let R := scale delta (workingLevel D.pair.1 (D.pair.2-D.pair.1) m (k+1)) /
        scale delta (workingLevel D.pair.1 (D.pair.2-D.pair.1) m k)
  have hR : 0 < R := div_pos (scale_pos hdelta _) (scale_pos hdelta _)
  have he := separationExponent_pos epsilon hepsilon
  have hmR : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  refine ⟨by positivity,?_⟩
  have hworking := WorkingScaleProfileBudget.old_ratio_le_working_ratio hdelta
    D.pair.1 (D.pair.2-D.pair.1) k hm
  rw [Nat.add_sub_of_le D.valid.1] at hworking
  have hbig : ((2:ℝ)^Nold)^separationExponent epsilon ≤ (64*R)^m := by
    calc
      _ ≤ _ := D.separation
      _ ≤ (2:ℝ)^m*R^m := hworking
      _ = (2*R)^m := (mul_pow _ _ _).symm
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by nlinarith) m
  have hroot := root_of_nat_power (by positivity : 0 ≤ (2:ℝ)^Nold)
    (by positivity : 0 ≤ 64*R) hm hbig
  have htop' := top_bracket_lower hdelta (by positivity : 0 ≤ (2:ℝ)^Nold) hsmall htop
  calc
    _ = (delta^(-(1:ℝ)/2))^(separationExponent epsilon/(m:ℝ)) := by
      rw [←Real.rpow_mul hdelta.le]
      congr 1
      field_simp
    _ ≤ ((2:ℝ)^Nold)^(separationExponent epsilon/(m:ℝ)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hdelta.le _) htop' (div_nonneg he.le hmR.le)
    _ ≤ _ := hroot
end NativeAlignmentScaleSeparation
