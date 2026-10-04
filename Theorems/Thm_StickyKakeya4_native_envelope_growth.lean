import Theorems.Thm_StickyKakeya4_native_common_envelope
import Theorems.Thm_StickyKakeya4_native_alignment_parameter_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option exponentiation.threshold 1000
set_option maxHeartbeats 1400000

namespace NativeEnvelopeGrowth
open NativeCommonEnvelope NativeAlignmentParameterBudget
open NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeAngularChartSelection CoverProfileStopping

noncomputable section

def growthCoefficient (F1 F2 : ℝ) (m : ℕ) (epsilon : ℝ) : ℝ :=
  fixedCoefficient m epsilon * F1 ^ 2 * F2 * 88 * (2 : ℝ) ^ 356

lemma powers_expand (n L1 L2 : ℕ) (eta : ℝ) :
    ((2 : ℝ) ^ 23 * (2 : ℝ) ^ (3 * (n : ℝ) / (L1 : ℝ))) ^ 8 *
      ((2 : ℝ) ^ 23 * (2 : ℝ) ^ (3 * (n : ℝ) / (L2 : ℝ))) ^ 2 *
      ((2 : ℝ) ^ 126 * (2 : ℝ) ^ (18 * eta * (n : ℝ))) =
      (2 : ℝ) ^ 356 * (2 : ℝ) ^ ((18 * eta + 24 / (L1 : ℝ) + 6 / (L2 : ℝ)) * (n : ℝ)) := by
  have h1 : ((2 : ℝ) ^ (3 * (n : ℝ) / (L1 : ℝ))) ^ 8 =
      (2 : ℝ) ^ (24 * (n : ℝ) / (L1 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  have h2 : ((2 : ℝ) ^ (3 * (n : ℝ) / (L2 : ℝ))) ^ 2 =
      (2 : ℝ) ^ (6 * (n : ℝ) / (L2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  rw [mul_pow, mul_pow, h1, h2]
  have hp : (2 : ℝ) ^ (24 * (n : ℝ) / (L1 : ℝ)) *
      (2 : ℝ) ^ (6 * (n : ℝ) / (L2 : ℝ)) * (2 : ℝ) ^ (18 * eta * (n : ℝ)) =
      (2 : ℝ) ^ ((18 * eta + 24 / (L1 : ℝ) + 6 / (L2 : ℝ)) * (n : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    _ = (2 : ℝ) ^ 356 * ((2 : ℝ) ^ (24 * (n : ℝ) / (L1 : ℝ)) *
      (2 : ℝ) ^ (6 * (n : ℝ) / (L2 : ℝ)) * (2 : ℝ) ^ (18 * eta * (n : ℝ))) := by
        norm_num
        ring
    _ = _ := by rw [hp]

lemma envelope_le_growth {I E F1 F2 Q1 Q2 K R eta epsilon : ℝ} (n m H L1 L2 : ℕ)
    (_hI : 0 ≤ I) (_hE : 0 ≤ E) (_hF1 : 0 ≤ F1) (hF2 : 0 ≤ F2)
    (hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hIE : I * E ≤ 88 * ((n : ℝ) + 1) ^ 5)
    (hq1 : Q1 ≤ (2 : ℝ) ^ 23 * (2 : ℝ) ^ (3 * (n : ℝ) / (L1 : ℝ)))
    (hq2 : Q2 ≤ (2 : ℝ) ^ 23 * (2 : ℝ) ^ (3 * (n : ℝ) / (L2 : ℝ)))
    (hK18 : K ^ 18 ≤ (2 : ℝ) ^ 126 * (2 : ℝ) ^ (18 * eta * (n : ℝ))) :
    envelope I E F1 F2 Q1 Q2 K R m H epsilon ≤
      growthCoefficient F1 F2 m epsilon * ((n : ℝ) + 5) ^ 5 *
        (2 : ℝ) ^ ((18 * eta + 24 / (L1 : ℝ) + 6 / (L2 : ℝ)) * (n : ℝ)) *
        R ^ (3 * (m : ℝ) * epsilon + 1 / (m : ℝ) + 2 / (H : ℝ)) := by
  have hC := fixedCoefficient_nonneg m epsilon
  have hp1 := pow_le_pow_left₀ hQ1 hq1 8
  have hp2 := pow_le_pow_left₀ hQ2 hq2 2
  have hbound := mul_le_mul (mul_le_mul hp1 hp2 (pow_nonneg hQ2 _) (by positivity)) hK18
    (pow_nonneg hK _) (by positivity)
  rw [powers_expand] at hbound
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  have hpoly : ((n : ℝ) + 1) ^ 5 ≤ ((n : ℝ) + 5) ^ 5 :=
    pow_le_pow_left₀ hn (by linarith) 5
  have hIE' := hIE.trans (mul_le_mul_of_nonneg_left hpoly (by norm_num))
  calc
    _ = (fixedCoefficient m epsilon * F1 ^ 2 * F2) * (I * E) *
      (Q1 ^ 8 * Q2 ^ 2 * K ^ 18) *
      R ^ (3 * (m : ℝ) * epsilon + 1 / (m : ℝ) + 2 / (H : ℝ)) := by unfold envelope; ring
    _ ≤ (fixedCoefficient m epsilon * F1 ^ 2 * F2) * (88 * ((n : ℝ) + 5) ^ 5) *
      ((2 : ℝ) ^ 356 * (2 : ℝ) ^ ((18 * eta + 24 / (L1 : ℝ) + 6 / (L2 : ℝ)) * (n : ℝ))) *
      R ^ (3 * (m : ℝ) * epsilon + 1 / (m : ℝ) + 2 / (H : ℝ)) := by gcongr
    _ = _ := by unfold growthCoefficient; ring

/-- Stopping and adjacent-scale partitioning give exactly the lower bound
needed by parameter absorption, uniformly in the actual winning index. -/
lemma output_extent_lower {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (p : alpha → Plane) {delta epsilon K t : ℝ} {Nold : ℕ} {E : Finset alpha}
    (D : StoppedProfile p delta epsilon K t Nold E)
    (hdelta : 0 < delta) (k m : ℕ) (hm : 0 < m) :
    (2 : ℝ) ^ ((separationExponent epsilon / (m : ℝ)) * (Nold : ℝ)) ≤
      ((2 ^ (workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (k + 1) -
        workingLevel D.pair.1 (D.pair.2 - D.pair.1) m k + 6) : ℕ) : ℝ) := by
  let ia := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m k
  let ib := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (k + 1)
  let R := scale delta ib / scale delta ia
  have hR : 0 < R := div_pos (scale_pos hdelta _) (scale_pos hdelta _)
  have hworking := WorkingScaleProfileBudget.old_ratio_le_working_ratio hdelta
    D.pair.1 (D.pair.2 - D.pair.1) k hm
  rw [Nat.add_sub_of_le D.valid.1] at hworking
  have hbig : ((2 : ℝ) ^ Nold) ^ separationExponent epsilon ≤ (64 * R) ^ m := by
    calc
      _ ≤ _ := D.separation
      _ ≤ (2 : ℝ) ^ m * R ^ m := hworking
      _ = (2 * R) ^ m := (mul_pow _ _ _).symm
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by nlinarith) m
  have hr := NativeAlignmentScaleSeparation.root_of_nat_power (by positivity : 0 ≤ (2 : ℝ) ^ Nold)
    (by positivity : 0 ≤ 64 * R) hm hbig
  have heq : (64 : ℝ) * R = ((2 ^ (ib - ia + 6) : ℕ) : ℝ) := by
    dsimp [R]
    rw [scale_ratio hdelta (workingLevel_mono _ _ _ (Nat.le_succ k))]
    push_cast
    rw [pow_add]
    norm_num
    ring
  rw [heq] at hr
  convert hr using 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

end
end NativeEnvelopeGrowth
