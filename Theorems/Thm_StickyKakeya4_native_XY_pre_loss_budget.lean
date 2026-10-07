import Theorems.Thm_StickyKakeya4_native_actual_XY_budget_comparison
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeXYPreLossBudget
open NativeSliceADConstant NativeThirdXYData NativeFixedCompactKakeyaExponent

lemma constant_pre_loss {l u B s r : ℝ} (hl : 0 < l) (hr : 0 < r) (hB : 0 ≤ B) :
    constant (l/r) u B s ≤ max 1 r*constant l u B s := by
  have hK : 1 ≤ constant l u B s := one_le_constant _ _ _ _
  have hM : 1 ≤ max 1 r := le_max_left _ _
  have hLo : B^s/l ≤ constant l u B s := (le_max_left _ _).trans (le_max_right _ _)
  have hUp : 729*u*B^s ≤ constant l u B s := (le_max_right _ _).trans (le_max_right _ _)
  have h0 : 0 ≤ B^s/l := div_nonneg (Real.rpow_nonneg hB _) hl.le
  apply max_le (by nlinarith only [hK,hM])
  apply max_le
  · calc
      B^s/(l/r) = r*(B^s/l) := by field_simp
      _ ≤ max 1 r*(B^s/l) := mul_le_mul_of_nonneg_right (le_max_right _ _) h0
      _ ≤ _ := mul_le_mul_of_nonneg_left hLo (hM.trans' (by norm_num))
  · exact hUp.trans (le_mul_of_one_le_left (by linarith only [hK]) hM)

/-- The pre-third coherence loss is retained explicitly and changes only the
lower-count term of the actual XY constant. -/
theorem xyConstant_pre_loss {delta zeta population PL PU lambda G Cbase Cpre : ℝ}
    (Qref Q3 J m F3 : ℕ)
    (hd : 0 < delta) (hpop : 0 < population) (hPL : 0 < PL) (hPU : 0 < PU)
    (hlambda : 0 < lambda) (hG : 0 < G) (hbase : 0 < Cbase) (hpre : 0 < Cpre)
    (hF3 : 0 < F3) (hQ : 0 < Qref) (hQ3 : 0 < Q3) :
    xyConstant delta zeta population PL PU lambda (G*Cpre*F3) Qref Q3 J m ≤
      max 1 (Cpre/Cbase)*xyConstant delta zeta population PL PU lambda (G*Cbase*F3) Qref Q3 J m := by
  let low := NativeReferenceColumnExponents.lowerCountCoefficient delta zeta population PU
  let up := NativeReferenceColumnExponents.upperCountCoefficient delta zeta PL
  let Ci : ℝ := ((201^3:ℕ):ℝ)
  let Cf : ℝ := ((1201^3:ℕ):ℝ)
  let l := lambda*(low/up)/((G*Cbase*F3)*(Qref:ℝ)^2*Ci*Cf*(Q3:ℝ)^4)
  obtain ⟨hLow,hUp⟩ := NativeReferenceColumnExponents.count_coefficients_pos (zeta:=zeta) hd hpop hPL hPU
  have hFr : (0:ℝ)<F3 := by exact_mod_cast hF3
  have hQr : (0:ℝ)<Qref := by exact_mod_cast hQ
  have hQ3r : (0:ℝ)<Q3 := by exact_mod_cast hQ3
  have hl : 0 < l := by dsimp [l,low,up,Ci,Cf]; positivity
  have heq : lambda*(low/up)/((G*Cpre*F3)*(Qref:ℝ)^2*Ci*Cf*(Q3:ℝ)^4)=l/(Cpre/Cbase) := by
    dsimp [l]
    field_simp
  dsimp only [xyConstant]
  change constant (lambda*(low/up)/((G*Cpre*F3)*(Qref:ℝ)^2*Ci*Cf*(Q3:ℝ)^4)) _ _ _ ≤
    max 1 (Cpre/Cbase)*constant l _ _ _
  rw [heq]
  exact constant_pre_loss hl (div_pos hpre hbase) (by positivity)

end NativeXYPreLossBudget
