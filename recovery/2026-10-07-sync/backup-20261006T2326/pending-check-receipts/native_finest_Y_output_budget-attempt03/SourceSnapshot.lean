import Theorems.Thm_StickyKakeya4_native_new_cut_output_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeFinestYOutputBudget
open NativeRetentionOutputPower

/-- The literal integer coarsening and final contraction cost is quadratic
in the original fine-Y constant. This is the finest-height route only. -/
theorem coarsening_constant_le (K s : ℝ) (hs : s ≤ 2) :
    512^s*169*(81*(169*K)^2*12^s) ≤
      (81*13^6*6144^2:ℝ)*K^2 := by
  have hpow : (512:ℝ)^s*(12:ℝ)^s=(6144:ℝ)^s := by
    rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 512) (by norm_num : (0:ℝ) ≤ 12)]
    norm_num
  have hsquare : (6144:ℝ)^s ≤ (6144:ℝ)^2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 6144) hs
  have heq : (512:ℝ)^s*169*(81*(169*K)^2*12^s)=
      (81*13^6:ℝ)*K^2*((512:ℝ)^s*(12:ℝ)^s) := by ring
  rw [heq,hpow]
  calc
    _ ≤ (81*13^6:ℝ)*K^2*(6144:ℝ)^2 :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = _ := by norm_num only [Real.rpow_two]; ring

/-- The same original source cut multiplier pays the squared fine-Y
constant. Its fourth power is explicit; no lower AD bound is transferred
across a new cut by this scalar statement. -/
theorem source_cost_at_output {M C r rho Delta nu paid K s : ℝ}
    (hM : 0 ≤ M) (_hC : 0 ≤ C) (hr : 0 < r) (hrho : 0 < rho)
    (hD : 0 < Delta) (hnu : 0 ≤ nu) (hnuHalf : nu ≤ 1/2)
    (hpaid : 0 ≤ paid) (hK : 0 ≤ K) (hs : s ≤ 2)
    (hshape : Delta^2 ≤ rho) (hstop : rho^2 ≤ 6144*r)
    (hcost : M ≤ C*r^(-nu))
    (hFine : K ≤ M^2*rho^(-paid)) :
    512^s*169*(81*(169*K)^2*12^s) ≤
      ((81*13^6*6144^2:ℝ)*(6144*C^2)^2)*
        Delta^(-(16*nu+4*paid)) := by
  have hf : K ≤ C^2*r^(-(2*nu))*rho^(-paid)*Delta^(-(0:ℝ)) := by
    calc
      K ≤ M^2*rho^(-paid) := hFine
      _ ≤ (C*r^(-nu))^2*rho^(-paid) := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM hcost 2)
          (Real.rpow_nonneg hrho.le _)
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast hr.le]
        norm_num only [Nat.cast_ofNat,neg_zero,Real.rpow_zero,mul_one]
        congr 2
        ring
  have hk := total_retention_at_output (F:=K) (C:=C^2) (r:=r) (rho:=rho)
    (Delta:=Delta) (nu:=2*nu) (A:=paid) (zeta:=0) (sq_nonneg C) hD hrho.le
    (by positivity) (by linarith only [hnuHalf]) hpaid hshape hstop hf
  have hexp : 4*(2*nu)+2*paid+0=8*nu+2*paid := by ring
  rw [hexp] at hk
  have hsq := pow_le_pow_left₀ hK hk 2
  calc
    _ ≤ (81*13^6*6144^2:ℝ)*K^2 := coarsening_constant_le K s hs
    _ ≤ (81*13^6*6144^2:ℝ)*((6144*C^2)*Delta^(-(8*nu+2*paid)))^2 := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hD.le]
      norm_num only [Nat.cast_ofNat]
      have he : -(8*nu+2*paid)*2=-(16*nu+4*paid) := by ring
      rw [he]
      ring

/-- The cutoff is fixed before the source and every permitted output.
The explicit cost uses 16 nu + 4 paid, so this does not reuse the cheaper
window-route allocation or hide the fourth power of the new-cut multiplier. -/
theorem exists_finest_Y_output_cutoff (C eta53 : ℝ) (hC : 0 < C)
    (heta : 0 < eta53) :
    ∃D0 : ℝ,0 < D0 ∧ D0 ≤ 1 ∧ ∀ M r rho Delta deltaY nu paid K s : ℝ,
      0 ≤ M → 0 < r → 0 < rho → 0 < deltaY → deltaY ≤ Delta → Delta ≤ D0 →
      0 ≤ nu → nu ≤ 1/2 → 0 ≤ paid → 0 ≤ K → s ≤ 2 →
      Delta^2 ≤ rho → rho^2 ≤ 6144*r → M ≤ C*r^(-nu) →
      K ≤ M^2*rho^(-paid) → 16*nu+4*paid ≤ eta53/2 →
      512^s*169*(81*(169*K)^2*12^s) ≤ deltaY^(-eta53) := by
  let A : ℝ := (81*13^6*6144^2:ℝ)*(6144*C^2)^2
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨D0,hD0,hD01,H⟩ := exists_uniform_retention_cutoff (32*eta53) A
    (by positivity) hA
  refine ⟨D0,hD0,hD01,?_⟩
  intro M r rho Delta deltaY nu paid K s hM hr hrho hY hYD hsmall
    hnu hnuHalf hpaid hK hs hshape hstop hcost hFine hmargin
  have hD : 0 < Delta := hY.trans_le hYD
  have hF := source_cost_at_output hM hC.le hr hrho hD hnu hnuHalf hpaid hK hs
    hshape hstop hcost hFine
  have hout := H Delta (512^s*169*(81*(169*K)^2*12^s)) (16*nu+4*paid)
    hD hsmall (by linarith only [hmargin]) hF
  have he : (32*eta53)/32=eta53 := by ring
  rw [he] at hout
  exact hout.trans (Real.rpow_le_rpow_of_nonpos hY hYD (by linarith only [heta]))

end NativeFinestYOutputBudget
