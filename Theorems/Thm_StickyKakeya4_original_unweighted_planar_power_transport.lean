import Theorems.Thm_StickyKakeya4_original_three_dimensional_owner_coefficient_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000

noncomputable section
namespace OriginalUnweightedPlanarPowerTransport

/-- The actual endpoint-owner displacement costs r=delta^(2eta). The
proved fiber bound and fixed numerical slack preserve a zeta/9 rich gain
at the genuine query width 50Delta/r. -/
theorem original_owner_richness_power (delta eta zeta Delta A : ℝ)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hDelta : 0 ≤ Delta)
    (heta : eta ≤ zeta/1000) (hzeta : 0 < zeta)
    (hA : A ≤ delta^(-2*eta)) (hconst : 4096*delta^eta ≤ 1) :
    A*delta^(-zeta/9)*(50*Delta/delta^(2*eta)) ≤ delta^(-zeta/8)*Delta := by
  have hconst50 : 50*delta^eta ≤ 1 :=
    (mul_le_mul_of_nonneg_right (by norm_num : (50:ℝ) ≤ 4096) (Real.rpow_nonneg hd.le eta)).trans hconst
  have habsorb : 50*delta^(-zeta/9-4*eta) ≤ delta^(-zeta/9-5*eta) := by
    have hh := mul_le_mul_of_nonneg_right hconst50 (Real.rpow_nonneg hd.le (-zeta/9-5*eta))
    have he : delta^eta*delta^(-zeta/9-5*eta)=delta^(-zeta/9-4*eta) := by
      rw [← Real.rpow_add hd]
      congr 1
      ring
    simpa only [mul_assoc,he,one_mul] using hh
  have hexp : -zeta/8 ≤ -zeta/9-5*eta := by linarith only [heta,hzeta]
  have hpower := habsorb.trans (Real.rpow_le_rpow_of_exponent_ge hd hd1 hexp)
  calc
    _ ≤ delta^(-2*eta)*delta^(-zeta/9)*(50*Delta/delta^(2*eta)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hd.le _)) (by positivity)
    _ = (50*delta^(-zeta/9-4*eta))*Delta := by
      have he : delta^(-2*eta)*delta^(-zeta/9)/delta^(2*eta)=delta^(-zeta/9-4*eta) := by
        rw [← Real.rpow_add hd,← Real.rpow_sub hd]
        congr 1
        ring
      calc
        _ = 50*(delta^(-2*eta)*delta^(-zeta/9)/delta^(2*eta))*Delta := by ring
        _ = _ := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_right hpower hDelta

/-- Actual selected-slice nonconcentration survives all proved owner
normalizations at a fixed positive power. The internal eta ceiling is
chosen after e2, and the displayed constant condition is later supplied
by a true cutoff depending only on fixed zeta and e2. -/
theorem original_owner_cap_power (delta eta zeta e2 Delta A R : ℝ)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hzeta : 0 < zeta) (he2 : 0 < e2)
    (hDelta : 0 ≤ Delta) (hdecay : Delta ≤ 32*delta^(zeta/5))
    (heta : eta ≤ zeta*e2/10000)
    (hcoefficient : 32*A*R ≤ delta^(-12*eta))
    (hconstant : (32:ℝ)^e2*delta^(zeta*e2/10) ≤ 1) :
    (32*A*R)*Delta^e2 ≤ delta^(zeta*e2/20) := by
  have hwidth : Delta^e2 ≤ (32:ℝ)^e2*delta^(zeta*e2/5) := by
    have hh := Real.rpow_le_rpow hDelta hdecay he2.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 32) (Real.rpow_nonneg hd.le _),← Real.rpow_mul hd.le] at hh
    convert hh using 1
    congr 2
    ring
  have hproduct : delta^(-12*eta)*((32:ℝ)^e2*delta^(zeta*e2/5))=
      ((32:ℝ)^e2*delta^(zeta*e2/10))*delta^(zeta*e2/10-12*eta) := by
    have h1 : delta^(-12*eta)*delta^(zeta*e2/5)=delta^(zeta*e2/5-12*eta) := by
      rw [← Real.rpow_add hd]
      congr 1
      ring
    have h2 : delta^(zeta*e2/10)*delta^(zeta*e2/10-12*eta)=delta^(zeta*e2/5-12*eta) := by
      rw [← Real.rpow_add hd]
      congr 1
      ring
    calc
      _ = (32:ℝ)^e2*(delta^(-12*eta)*delta^(zeta*e2/5)) := by ring
      _ = (32:ℝ)^e2*(delta^(zeta*e2/10)*delta^(zeta*e2/10-12*eta)) := by rw [h1,h2]
      _ = _ := by ring
  have hexp : zeta*e2/20 ≤ zeta*e2/10-12*eta := by
    have hp := mul_pos hzeta he2
    linarith only [heta,hp]
  calc
    _ ≤ delta^(-12*eta)*Delta^e2 :=
      mul_le_mul_of_nonneg_right hcoefficient (Real.rpow_nonneg hDelta e2)
    _ ≤ delta^(-12*eta)*((32:ℝ)^e2*delta^(zeta*e2/5)) :=
      mul_le_mul_of_nonneg_left hwidth (Real.rpow_nonneg hd.le _)
    _ = ((32:ℝ)^e2*delta^(zeta*e2/10))*delta^(zeta*e2/10-12*eta) := hproduct
    _ ≤ delta^(zeta*e2/10-12*eta) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hconstant
        (Real.rpow_nonneg hd.le (zeta*e2/10-12*eta))
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 hexp

end OriginalUnweightedPlanarPowerTransport
