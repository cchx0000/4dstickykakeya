import Theorems.Thm_StickyKakeya4_native_retention_output_power
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_points

/- Auxiliary configured-base gap measured at the rank stopping radius.
The current window-Lipschitz payment uses the stronger existing fourth-power
comparison and does not require this module's extra fixed cutoff.
Originally drafted without verification; consult current receipts. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeActualBaseRankGap

/-- The upper half of the actual base chooser is enough; its fixed
coefficient leaves eps below the unmultiplied reference power. -/
lemma base_envelope_le_power {R eps e : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (he : 0 ≤ e)
    (hshape : 64*eps ≤ 2*max ((5/4:ℝ)*R^(1-2*e)) R) :
    eps ≤ R^(1-2*e) := by
  have hp := Real.rpow_pos_of_pos hR (1-2*e)
  have hRP : R ≤ R^(1-2*e) := by
    calc
      R = R^(1:ℝ) := (Real.rpow_one R).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hR hR1 (by linarith only [he])
  have hleft : R ≤ (5/4:ℝ)*R^(1-2*e) := by linarith only [hRP,hp]
  rw [max_eq_left hleft] at hshape
  linarith only [hshape,hp]

/-- The source's true R-squared bound becomes a fourth-power bound after
one fixed smallness cutoff on the same rank radius. -/
lemma reference_fourth_le_rank {R r : ℝ} (hr : 0 ≤ r)
    (hscale : R^2 ≤ 6144*r) (hsmall : r ≤ 1/(6144:ℝ)^2) : R^4 ≤ r := by
  have hcost : (6144:ℝ)^2*r ≤ 1 := by
    have hh := (le_div_iff₀ (by norm_num : (0:ℝ)<(6144:ℝ)^2)).mp hsmall
    nlinarith only [hh]
  have hpow := pow_le_pow_left₀ (sq_nonneg R) hscale 2
  have hrpow : (6144:ℝ)^2*r^2 ≤ r := by
    have hh := mul_le_mul_of_nonneg_right hcost hr
    nlinarith only [hh]
  nlinarith only [hpow,hrpow]

/-- The actual base upper is paid at rStop directly, with exponent1/8.
The parent-source thickness and its c-cubed power window do not occur. -/
theorem base_le_rank_eighth {R r eps e : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hr : 0 < r)
    (he : 0 ≤ e) (he4 : e ≤ 1/4)
    (hscale : R^2 ≤ 6144*r) (hsmall : r ≤ 1/(6144:ℝ)^2)
    (hshape : 64*eps ≤ 2*max ((5/4:ℝ)*R^(1-2*e)) R) :
    eps ≤ r^(1/8:ℝ) := by
  have hfour := reference_fourth_le_rank hr.le hscale hsmall
  have hroot : R^(1/2:ℝ) ≤ r^(1/8:ℝ) := by
    have hh := Real.rpow_le_rpow (pow_nonneg hR.le 4) hfour (by norm_num : (0:ℝ)≤1/8)
    rw [←Real.rpow_natCast R 4,←Real.rpow_mul hR.le] at hh
    norm_num at hh
    exact hh
  exact (base_envelope_le_power hR hR1 he hshape).trans
    ((Real.rpow_le_rpow_of_exponent_ge hR hR1 (by linarith only [he4] : (1/2:ℝ)≤1-2*e)).trans hroot)

/-- The actual Lemma5.3 sigma gap now has a rank-radius exponent depending
on chi alone. The literal sigma remains32768*rhoPlanar/tauPlanar. -/
theorem sigma_le_rank_power {R r eps e sigma chi : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hr : 0 < r) (heps : 0 < eps)
    (he : 0 ≤ e) (he4 : e ≤ 1/4) (hchi : 0 ≤ chi)
    (hscale : R^2 ≤ 6144*r) (hsmall : r ≤ 1/(6144:ℝ)^2)
    (hshape : 64*eps ≤ 2*max ((5/4:ℝ)*R^(1-2*e)) R)
    (hSigma : sigma ≤ eps^(chi/2)) :
    eps ≤ r^(1/8:ℝ) ∧ sigma ≤ r^(chi/16) := by
  have hbase := base_le_rank_eighth hR hR1 hr he he4 hscale hsmall hshape
  refine ⟨hbase,?_⟩
  have hh := Real.rpow_le_rpow heps.le hbase (div_nonneg hchi (by norm_num))
  rw [←Real.rpow_mul hr.le] at hh
  apply hSigma.trans (hh.trans_eq ?_)
  congr 1
  ring

/-- This cutoff is chosen before the original source. Its existing actual
rStop<=delta^power and power>=amin fields supply the fixed rank-radius cutoff. -/
theorem exists_source_cutoff (amin : ℝ) (hamin : 0 < amin) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀delta r power : ℝ,0 < delta → delta ≤ delta0 → amin ≤ power → r ≤ delta^power →
        r ≤ 1/(6144:ℝ)^2 := by
  obtain ⟨delta0,hdelta0,hdelta1,Hcut⟩ :=
    NativeQuarterScaleParameters.exists_small_power_cutoff hamin
      (by norm_num : (0:ℝ)<1/(6144:ℝ)^2)
  refine ⟨delta0,hdelta0,hdelta1,?_⟩
  intro delta r power hd hd0 hpower hr
  exact hr.trans ((Real.rpow_le_rpow_of_exponent_ge hd (hd0.trans hdelta1) hpower).trans
    (Hcut delta hd hd0))

end NativeActualBaseRankGap
