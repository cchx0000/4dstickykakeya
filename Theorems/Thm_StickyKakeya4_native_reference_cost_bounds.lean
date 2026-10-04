import Theorems.Thm_StickyKakeya4_native_parameter_constants
import Theorems.Thm_StickyKakeya4_working_scale_profile_budget

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace NativeReferenceCostBounds

open NativeParameterConstants NativeSelectedParentPreparation NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeParentSpines
open NativeContactFractionalComposition NativeFractionalReferenceComposition
open NativeAngularChartSelection WorkingScaleProfileBudget
open ShearedGridADReference

noncomputable section

lemma spatial_cost_upper {K t : ℝ} (ht : t ≤ 2) :
    spatialConstant K t ≤ (81 * 36 : ℝ) * K ^ 2 := by
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6) ht
  norm_num at hp
  unfold spatialConstant
  nlinarith only [mul_le_mul_of_nonneg_right hp (sq_nonneg K)]

lemma ad_cost_upper {K t : ℝ} (ht : t ≤ 2) :
    adConstant K t ≤ (513 ^ 2 * 81 * 36 : ℝ) * K ^ 2 := by
  have h := spatial_cost_upper (K := K) ht
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 513 ^ 2)
  simpa only [adConstant, referenceFactor, spatialConstant, mul_assoc] using hh

lemma column_cost_upper (N m Q L : ℕ) (hm : 0 < m) (hQ : 0 < Q)
    {K H t : ℝ} (hK : 1 ≤ K) (hH : 0 < H) (ht : t ≤ 2) :
    contactColumnConstant 2 K H t (spineConstant N m Q L K t H) ≤
      (3081 * 525 * 400 * (81 * 36) ^ 2 : ℝ) * (Fintype.card (Index N) : ℝ) *
        (refinementCost m L : ℝ) * (Q : ℝ) ^ 2 * K ^ 6 * H ^ 2 := by
  rw [column_cost_expand N m Q L hm hQ hK hH]
  have hs0 := (spatialConstant_pos (t := t) hK).le
  have hs := pow_le_pow_left₀ hs0 (spatial_cost_upper (K := K) ht) 2
  have hc : 0 ≤ (3081 * 525 * 400 : ℝ) * (Fintype.card (Index N) : ℝ) *
      (refinementCost m L : ℝ) * (Q : ℝ) ^ 2 * H ^ 2 * K ^ 2 := by positivity
  have hh := mul_le_mul_of_nonneg_left hs hc
  nlinarith only [hh]

lemma density_cost_upper (A : Finset Plane) (N m Q L lo hi : ℕ) {K t : ℝ}
    (hK : 1 ≤ K) (ht : t ≤ 2) :
    8192 * K * (64 : ℝ) ^ t * sourceMassCost A N m Q L lo hi K t ≤
      (8192 * 4096 * (81 * 36) : ℝ) * (epochCost A N : ℝ) * (refinementCost (m + 1) L : ℝ) *
        (Q : ℝ) ^ 6 * (angularCost lo hi m : ℝ) * K ^ 4 := by
  rw [density_cost_expand]
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 64) ht
  norm_num at hp
  have hsp := (spatialConstant_pos (t := t) hK).le
  have hboth : (64 : ℝ) ^ t * spatialConstant K t ≤ 4096 * ((81 * 36 : ℝ) * K ^ 2) :=
    mul_le_mul hp (spatial_cost_upper (K := K) ht) hsp (by norm_num)
  have hc : 0 ≤ 8192 * (epochCost A N : ℝ) * (refinementCost (m + 1) L : ℝ) *
      (Q : ℝ) ^ 6 * (angularCost lo hi m : ℝ) * K ^ 2 := by positivity
  have hh := mul_le_mul_of_nonneg_left hboth hc
  nlinarith only [hh]

/-- The old-span profile loss is bounded directly in the ACTUAL output
extent with exponent m*epsilon. No delta^(-epsilon) or epsilon/chi loss occurs. -/
theorem stopped_loss_le_output_extent {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Plane) {δ ε K t : ℝ} {Nold : ℕ} {E : Finset α}
    (D : StoppedProfile p δ ε K t Nold E) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (k : ℕ) {m : ℕ} (hm : 0 < m) (ht : t ≤ 2) :
    let ia := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m k
    let ib := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (k + 1)
    D.loss ≤ (72 * 81 * 324 : ℝ) * (2 : ℝ) ^ ((m : ℝ) * ε) * K ^ 2 *
      (((2 ^ (ib - ia + 6) : ℕ) : ℝ) ^ ((m : ℝ) * ε)) := by
  dsimp only
  let lo := D.pair.1
  let M := D.pair.2 - D.pair.1
  let ia := workingLevel lo M m k
  let ib := workingLevel lo M m (k + 1)
  have hratio : scale δ ib / scale δ ia ≤ ((2 ^ (ib - ia + 6) : ℕ) : ℝ) := by
    have hab : ia ≤ ib := workingLevel_mono _ _ _ (Nat.le_succ k)
    rw [scale_ratio hδ hab]
    push_cast
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hexp : 0 ≤ (m : ℝ) * ε := mul_nonneg (Nat.cast_nonneg m) hε
  have hpow := Real.rpow_le_rpow (div_nonneg (scale_pos hδ _).le (scale_pos hδ _).le) hratio hexp
  have hp18 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 18) ht
  norm_num at hp18
  have hAD : adProfileConstant K t ≤ (81 * 324 : ℝ) * K ^ 2 := by
    unfold adProfileConstant
    nlinarith only [mul_le_mul_of_nonneg_right hp18 (sq_nonneg K)]
  have hC : 72 * adProfileConstant K t * (2 : ℝ) ^ ((m : ℝ) * ε) ≤
      (72 * 81 * 324 : ℝ) * (2 : ℝ) ^ ((m : ℝ) * ε) * K ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hAD
      (show 0 ≤ 72 * (2 : ℝ) ^ ((m : ℝ) * ε) by positivity)
    nlinarith only [hh]
  have hr0 : 0 ≤ scale δ ib / scale δ ia := div_nonneg (scale_pos hδ _).le (scale_pos hδ _).le
  exact (stopped_loss_le_adjacent p D hδ hε k hm).trans
    (mul_le_mul hC hpow (Real.rpow_nonneg hr0 _) (by positivity))

end
end NativeReferenceCostBounds
