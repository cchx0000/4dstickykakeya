import Theorems.Thm_StickyKakeya4_native_conditional_angular_power_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeRichAngularRankPayment

/-- The actual third cost pays its needed edge-retention/point-radix
factor in stopping r; the surplus Q3² is discarded using Q3≥1. -/
lemma third_cost {delta r power rankLoss : ℝ} (hd : 0< delta) (hr : 0< r)
    (ha : 0< power) (hl : 0≤ rankLoss) (hscale : r≤ delta^power)
    (F3 Q3 : ℕ) (hQ : 1≤ Q3)
    (H : (F3:ℝ)*(Q3:ℝ)^4≤ delta^(-(power*rankLoss/4))) :
    (F3:ℝ)*(Q3:ℝ)^2≤ r^(-(rankLoss/4)) := by
  have hQr : (1:ℝ)≤ Q3 := by exact_mod_cast hQ
  have hQ24 : (Q3:ℝ)^2≤ (Q3:ℝ)^4 := by nlinarith only [hQr,sq_nonneg ((Q3:ℝ)^2-1)]
  have hh := (mul_le_mul_of_nonneg_left hQ24 (Nat.cast_nonneg F3)).trans H
  have hp := NativeConditionalAngularPowerBudget.original_loss_to_rank hd hr ha
    (show 0≤ power*rankLoss/4 by positivity) hscale
  have he : (power*rankLoss/4)/power=rankLoss/4 := by field_simp
  rw [he] at hp
  exact hh.trans hp

/-- The rich sigma-class lower and the common spatial-cell union upper
cancel their actual angular scale powers. All quantities count distinct
labels, while their source inequalities retain the original edge weights. -/
theorem cancel_rich_class {r rho sigma kappa rankLoss loss C U J P Nsig Nfine : ℝ}
    (hr : 0< r) (hr1 : r≤ 1) (hrho : 0< rho) (hsigma : 0< sigma)
    (hl : 0≤ rankLoss) (hC : 0≤ C) (hU : 0≤ U) (hJ : 0≤ J) (_hP : 0≤ P)
    (hn : 0≤ Nsig) (hf : 0≤ Nfine)
    (Hlower : rho^(-kappa)≤ C*r^(-(9*rankLoss))*P*(2*J*Nsig)*Nfine)
    (Hupper : Nsig≤ U*r^(-loss)*sigma^(-kappa))
    (Hthird : P≤ r^(-(rankLoss/4))) :
    (sigma/rho)^kappa≤ (2*C*U*J)*r^(-(10*rankLoss+loss))*Nfine := by
  have hPbound := mul_le_mul Hthird Hupper hn (Real.rpow_nonneg hr.le _)
  have hCombined : rho^(-kappa)≤
      (2*C*U*J)*r^(-(9*rankLoss))*r^(-(rankLoss/4))*r^(-loss)*sigma^(-kappa)*Nfine := by
    apply Hlower.trans
    have hh := mul_le_mul_of_nonneg_left hPbound
      (show 0≤ C*r^(-(9*rankLoss))*(2*J)*Nfine by positivity)
    convert hh using 1 <;> ring
  have hCancel := mul_le_mul_of_nonneg_right hCombined (Real.rpow_nonneg hsigma.le kappa)
  have hSigma : sigma^(-kappa)*sigma^kappa=1 := by
    rw [←Real.rpow_add hsigma]; simp
  have hR : r^(-(9*rankLoss))*r^(-(rankLoss/4))*r^(-loss)=r^(-(9*rankLoss+rankLoss/4+loss)) := by
    rw [←Real.rpow_add hr,←Real.rpow_add hr]
    congr 1
    ring
  have hScale : rho^(-kappa)*sigma^kappa=(sigma/rho)^kappa := by
    rw [Real.rpow_neg hrho.le,Real.div_rpow hsigma.le hrho.le]
    ring
  rw [hScale] at hCancel
  have hPaid : r^(-(9*rankLoss))*r^(-(rankLoss/4))*r^(-loss)≤ r^(-(10*rankLoss+loss)) := by
    rw [hR]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith only [hl])
  calc
    _ ≤ _ := hCancel
    _ = (2*C*U*J)*(r^(-(9*rankLoss))*r^(-(rankLoss/4))*r^(-loss))*Nfine := by
      calc
        _ = (2*C*U*J)*(r^(-(9*rankLoss))*r^(-(rankLoss/4))*r^(-loss))*Nfine*
            (sigma^(-kappa)*sigma^kappa) := by ring
        _ = _ := by rw [hSigma,mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPaid (by positivity)) hf

end NativeRichAngularRankPayment
