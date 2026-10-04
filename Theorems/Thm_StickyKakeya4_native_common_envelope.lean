import Theorems.Thm_StickyKakeya4_native_angular_cost_bound
import Theorems.Thm_StickyKakeya4_native_interpolation_cost_bound
import Theorems.Thm_StickyKakeya4_native_reference_cost_bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace NativeCommonEnvelope
open NativeSelectedParentPreparation NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeParentSpines
open NativeContactFractionalComposition NativeFractionalReferenceComposition NativeReferenceCostBounds
open NativeAngularChartSelection NativeAngularCostBound NativeInterpolationCostBound
open SmallFiberAlignment FractionalFiberAlignment ActualScalarADProfiles

noncomputable section

def profileCoefficient (m : ℕ) (epsilon : ℝ) : ℝ :=
  (72 * 81 * 324 : ℝ) * (2 : ℝ) ^ ((m : ℝ) * epsilon)
def profileBound (m : ℕ) (epsilon K R : ℝ) : ℝ :=
  profileCoefficient m epsilon * K ^ 2 * R ^ ((m : ℝ) * epsilon)
def ambientBound (K : ℝ) : ℝ := (513 ^ 2 * 81 * 36 : ℝ) * K ^ 2
def columnBound (I F Q K T : ℝ) : ℝ :=
  (3081 * 525 * 400 * (81 * 36) ^ 2 : ℝ) * I * F * Q ^ 2 * K ^ 6 * T ^ 2
def tubeBound (T : ℝ) : ℝ := (513 : ℝ) ^ 2 * T
def densityBound (E F Q K R : ℝ) (m : ℕ) : ℝ :=
  (8192 * 4096 * (81 * 36) * 2 : ℝ) * E * F * Q ^ 6 * R ^ ((m : ℝ)⁻¹) * K ^ 4
def interpolationBound (R : ℝ) (H : ℕ) : ℝ := 4096 * R ^ (2 / (H : ℝ))
def comparisonBound (F Q : ℝ) : ℝ := F * Q ^ 2

def productBound (I E F1 F2 Q1 Q2 K R : ℝ) (m H : ℕ) (epsilon : ℝ) : ℝ :=
  (9 * 128 ^ 2 : ℝ) * interpolationBound R H * comparisonBound F2 Q2 *
    columnBound I F1 Q1 K (profileBound m epsilon K R) * ambientBound K *
    tubeBound (profileBound m epsilon K R) * densityBound E F1 Q1 K R m

def fixedCoefficient (m : ℕ) (epsilon : ℝ) : ℝ :=
  (9 * 128 ^ 2 : ℝ) * 4096 * (3081 * 525 * 400 * (81 * 36) ^ 2) *
    (513 ^ 2 * 81 * 36) * 513 ^ 2 * (8192 * 4096 * (81 * 36) * 2) *
      (profileCoefficient m epsilon) ^ 3

def envelope (I E F1 F2 Q1 Q2 K R : ℝ) (m H : ℕ) (epsilon : ℝ) : ℝ :=
  fixedCoefficient m epsilon * I * E * F1 ^ 2 * F2 * Q1 ^ 8 * Q2 ^ 2 * K ^ 18 *
    R ^ (3 * (m : ℝ) * epsilon + 1 / (m : ℝ) + 2 / (H : ℝ))

/-- Exact expansion of the literal worst quotient constant, after the actual
source column, density, angular and interpolation estimates. -/
lemma productBound_eq_envelope (I E F1 F2 Q1 Q2 K R : ℝ) (m H : ℕ) (epsilon : ℝ)
    (hR : 0 < R) :
    productBound I E F1 F2 Q1 Q2 K R m H epsilon =
      envelope I E F1 F2 Q1 Q2 K R m H epsilon := by
  have hp : (R ^ ((m : ℝ) * epsilon)) ^ 3 * R ^ ((m : ℝ)⁻¹) * R ^ (2 / (H : ℝ)) =
      R ^ (3 * (m : ℝ) * epsilon + 1 / (m : ℝ) + 2 / (H : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le, ← Real.rpow_add hR,
      ← Real.rpow_add hR]
    congr 1
    push_cast
    ring
  calc
    _ = (fixedCoefficient m epsilon * I * E * F1 ^ 2 * F2 * Q1 ^ 8 * Q2 ^ 2 * K ^ 18) *
      ((R ^ ((m : ℝ) * epsilon)) ^ 3 * R ^ ((m : ℝ)⁻¹) * R ^ (2 / (H : ℝ))) := by
        unfold productBound interpolationBound comparisonBound columnBound profileBound ambientBound
          tubeBound densityBound fixedCoefficient
        ring
    _ = _ := by rw [hp]; rfl

lemma profileCoefficient_ge_one (m : ℕ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    1 ≤ profileCoefficient m epsilon := by
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ ((m : ℝ) * epsilon) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hepsilon)
  unfold profileCoefficient
  nlinarith only [hp]

lemma profileBound_ge_one (m : ℕ) {epsilon K R : ℝ}
    (hepsilon : 0 ≤ epsilon) (hK : 1 ≤ K) (hR : 1 ≤ R) :
    1 ≤ profileBound m epsilon K R := by
  unfold profileBound
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (profileCoefficient_ge_one m hepsilon) (one_le_pow₀ hK))
    (Real.one_le_rpow hR (mul_nonneg (Nat.cast_nonneg _) hepsilon))

lemma ambientBound_ge_one {K : ℝ} (hK : 1 ≤ K) : 1 ≤ ambientBound K := by
  exact one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hK)

lemma columnBound_ge_one {I F Q K T : ℝ}
    (hI : 1 ≤ I) (hF : 1 ≤ F) (hQ : 1 ≤ Q) (hK : 1 ≤ K) (hT : 1 ≤ T) :
    1 ≤ columnBound I F Q K T := by
  unfold columnBound
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le (by norm_num) hI) hF)
        (one_le_pow₀ hQ)) (one_le_pow₀ hK)) (one_le_pow₀ hT)

lemma tubeBound_ge_one {T : ℝ} (hT : 1 ≤ T) : 1 ≤ tubeBound T := by
  exact one_le_mul_of_one_le_of_one_le (by norm_num) hT

lemma densityBound_ge_one {E F Q K R : ℝ} (m : ℕ)
    (hE : 1 ≤ E) (hF : 1 ≤ F) (hQ : 1 ≤ Q) (hK : 1 ≤ K) (hR : 1 ≤ R) :
    1 ≤ densityBound E F Q K R m := by
  unfold densityBound
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le (by norm_num) hE) hF)
        (one_le_pow₀ hQ)) (Real.one_le_rpow hR (by positivity))) (one_le_pow₀ hK)

lemma interpolationBound_ge_one {R : ℝ} (H : ℕ) (hR : 1 ≤ R) :
    1 ≤ interpolationBound R H := by
  exact one_le_mul_of_one_le_of_one_le (by norm_num) (Real.one_le_rpow hR (by positivity))

lemma comparisonBound_ge_one {F Q : ℝ} (hF : 1 ≤ F) (hQ : 1 ≤ Q) :
    1 ≤ comparisonBound F Q :=
  one_le_mul_of_one_le_of_one_le hF (one_le_pow₀ hQ)

lemma refinementCost_ge_one (m L : ℕ) (hm : 0 < m) :
    1 ≤ (refinementCost m L : ℝ) := by
  have hn : 1 ≤ refinementCost m L := by
    unfold refinementCost
    have hp : 1 ≤ (4 * (m + (m + m))) ^ ((m + (m + m)) * L) :=
      Nat.one_le_pow _ _ (by omega)
    omega
  exact_mod_cast hn

lemma retentionCost_ge_one (d L : ℕ) (hd : 0 < d) :
    1 ≤ (retentionCost d L : ℝ) := by
  have hn : 1 ≤ retentionCost d L := by
    unfold retentionCost
    have hp : 1 ≤ (4 * d) ^ (d * L) := Nat.one_le_pow _ _ (by omega)
    omega
  exact_mod_cast hn

lemma fixedCoefficient_nonneg (m : ℕ) (epsilon : ℝ) : 0 ≤ fixedCoefficient m epsilon := by
  unfold fixedCoefficient profileCoefficient
  positivity

/-- Actual constructed source constants, all controlled with the SAME output
extent. Neither angular nor stopped-profile losses use the original delta. -/
theorem actual_cost_bounds {A : Finset Plane} {delta epsilon K t : ℝ} {Nold : ℕ}
    {E0 : Finset A} (D : StoppedProfile (position A) delta epsilon K t Nold E0)
    (hdelta : 0 < delta) (hepsilon : 0 ≤ epsilon) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (k m Q1 L1 H : ℕ) (hm : 0 < m) (hQ1 : 0 < Q1) :
    let ia := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m k
    let ib := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (k + 1)
    let R : ℝ := (2 ^ (ib - ia + 6) : ℕ)
    let T := profileBound m epsilon K R
    D.loss ≤ T ∧
    adConstant K t ≤ ambientBound K ∧
    contactColumnConstant 2 K D.loss t (spineConstant Nold (m + 1) Q1 L1 K t D.loss) ≤
      columnBound (Fintype.card (Index Nold)) (refinementCost (m + 1) L1) Q1 K T ∧
    tubeConstant D.loss ≤ tubeBound T ∧
    8192 * K * (64 : ℝ) ^ t * sourceMassCost A Nold m Q1 L1 D.pair.1 D.pair.2 K t ≤
      densityBound (epochCost A Nold) (refinementCost (m + 1) L1) Q1 K R m ∧
    (∀ v : ℝ, 0 ≤ v → v ≤ 2 → fullInterpolationLoss (ib - ia + 6) H v ≤ interpolationBound R H) ∧
    (∀ v : ℝ, 0 ≤ v → v ≤ 2 → realInterpolationLoss (ib - ia + 6) H v ≤ interpolationBound R H) := by
  dsimp only
  let ia := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m k
  let ib := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (k + 1)
  let R : ℝ := (2 ^ (ib - ia + 6) : ℕ)
  let T := profileBound m epsilon K R
  have hloss : D.loss ≤ T := stopped_loss_le_output_extent (position A) D hdelta hepsilon k hm ht2
  have hloss0 : 0 ≤ D.loss := zero_le_one.trans (D.loss_ge_one hdelta hepsilon hK ht)
  have hlosspos := zero_lt_one.trans_le (D.loss_ge_one hdelta hepsilon hK ht)
  refine ⟨hloss, ad_cost_upper ht2, ?_, ?_, ?_, ?_, ?_⟩
  · apply (column_cost_upper Nold (m + 1) Q1 L1 (by omega) hQ1 hK hlosspos ht2).trans
    unfold columnBound
    gcongr
  · unfold tubeConstant tubeBound
    exact mul_le_mul_of_nonneg_left hloss (by norm_num)
  · have hang := angularCost_le_extent_root D.pair.1 D.pair.2 k hm
    apply (density_cost_upper A Nold m Q1 L1 D.pair.1 D.pair.2 hK ht2).trans
    have hmul := mul_le_mul_of_nonneg_left hang
      (show 0 ≤ (8192 * 4096 * (81 * 36) : ℝ) * (epochCost A Nold : ℝ) *
        (refinementCost (m + 1) L1 : ℝ) * (Q1 : ℝ) ^ 6 * K ^ 4 by positivity)
    convert hmul using 1
    · ring
    · unfold densityBound
      ring
  · intro v hv hv2
    simpa only [interpolationBound, Nat.cast_pow, Nat.cast_ofNat] using
      full_interpolation_cost_upper (ib - ia + 6) H hv hv2
  · intro v hv hv2
    apply (show realInterpolationLoss (ib - ia + 6) H v ≤ fullInterpolationLoss (ib - ia + 6) H v from le_max_left _ _).trans
    simpa only [interpolationBound, Nat.cast_pow, Nat.cast_ofNat] using
      full_interpolation_cost_upper (ib - ia + 6) H hv hv2

lemma retention_le_comparison_density {E F1 F2 Q1 Q2 K R angular : ℝ} (m : ℕ)
    (hE : 0 ≤ E) (hF1 : 0 ≤ F1) (hF2 : 0 ≤ F2) (hQ1 : 1 ≤ Q1)
    (hQ2 : 1 ≤ Q2) (hK : 1 ≤ K) (hR : 0 ≤ R)
    (hangular : angular ≤ 2 * R ^ ((m : ℝ)⁻¹)) :
    E * F1 * Q1 ^ 2 * Q1 ^ 2 * angular * (64 ^ 2 * F2) * 260 ^ 2 ≤
      comparisonBound F2 Q2 * densityBound E F1 Q1 K R m := by
  have hQ10 := zero_le_one.trans hQ1
  have hq : Q1 ^ 4 ≤ Q1 ^ 6 := pow_le_pow_right₀ hQ1 (by omega)
  have hq2 : (1 : ℝ) ≤ Q2 ^ 2 := one_le_pow₀ hQ2
  have hk4 : (1 : ℝ) ≤ K ^ 4 := one_le_pow₀ hK
  have hc : (64 ^ 2 * 260 ^ 2 * 2 : ℝ) ≤ (8192 * 4096 * (81 * 36) * 2 : ℝ) := by norm_num
  calc
    _ ≤ E * F1 * Q1 ^ 2 * Q1 ^ 2 * (2 * R ^ ((m : ℝ)⁻¹)) * (64 ^ 2 * F2) * 260 ^ 2 := by gcongr
    _ = (64 ^ 2 * 260 ^ 2 * 2 : ℝ) * (E * F1 * F2) * Q1 ^ 4 * 1 * 1 * R ^ ((m : ℝ)⁻¹) := by ring
    _ ≤ (8192 * 4096 * (81 * 36) * 2 : ℝ) * (E * F1 * F2) * Q1 ^ 6 * Q2 ^ 2 * K ^ 4 * R ^ ((m : ℝ)⁻¹) := by gcongr
    _ = _ := by unfold comparisonBound densityBound; ring

lemma product_dominates_comparison_density {I E F1 F2 Q1 Q2 K R epsilon : ℝ} (m H : ℕ)
    (hI : 1 ≤ I) (hE : 1 ≤ E) (hF1 : 1 ≤ F1) (hF2 : 1 ≤ F2)
    (hQ1 : 1 ≤ Q1) (hQ2 : 1 ≤ Q2) (hK : 1 ≤ K) (hR : 1 ≤ R) (hepsilon : 0 ≤ epsilon) :
    comparisonBound F2 Q2 * densityBound E F1 Q1 K R m ≤
      productBound I E F1 F2 Q1 Q2 K R m H epsilon := by
  have hT := profileBound_ge_one m hepsilon hK hR
  have hJ := interpolationBound_ge_one H hR
  have hcol := columnBound_ge_one hI hF1 hQ1 hK hT
  have hbad := ambientBound_ge_one hK
  have htu := tubeBound_ge_one hT
  have hcmp := comparisonBound_ge_one hF2 hQ2
  have hden := densityBound_ge_one m hE hF1 hQ1 hK hR
  calc
    _ = (1 * 1 * 1 * 1 * 1 : ℝ) * (comparisonBound F2 Q2 * densityBound E F1 Q1 K R m) := by ring
    _ ≤ ((9 * 128 ^ 2 : ℝ) * interpolationBound R H *
        columnBound I F1 Q1 K (profileBound m epsilon K R) * ambientBound K *
        tubeBound (profileBound m epsilon K R)) *
        (comparisonBound F2 Q2 * densityBound E F1 Q1 K R m) := by gcongr; norm_num
    _ = _ := by unfold productBound; ring

lemma product_dominates_tube {I E F1 F2 Q1 Q2 K R epsilon s : ℝ} (m H : ℕ)
    (hI : 1 ≤ I) (hE : 1 ≤ E) (hF1 : 1 ≤ F1) (hF2 : 1 ≤ F2)
    (hQ1 : 1 ≤ Q1) (hQ2 : 1 ≤ Q2) (hK : 1 ≤ K) (hR : 1 ≤ R)
    (hepsilon : 0 ≤ epsilon) (hs : s ≤ 1) :
    170100 * profileBound m epsilon K R * (2 : ℝ) ^ s ≤
      productBound I E F1 F2 Q1 Q2 K R m H epsilon := by
  have hT := profileBound_ge_one m hepsilon hK hR
  have hJ := interpolationBound_ge_one H hR
  have hcol := columnBound_ge_one hI hF1 hQ1 hK hT
  have hbad := ambientBound_ge_one hK
  have hcmp := comparisonBound_ge_one hF2 hQ2
  have hden := densityBound_ge_one m hE hF1 hQ1 hK hR
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs
  norm_num at hpow
  have hsmall : 170100 * profileBound m epsilon K R * (2 : ℝ) ^ s ≤
      (9 * 128 ^ 2 : ℝ) * tubeBound (profileBound m epsilon K R) := by
    unfold tubeBound
    nlinarith only [hT, mul_le_mul_of_nonneg_left hpow (show 0 ≤ profileBound m epsilon K R from zero_le_one.trans hT)]
  apply hsmall.trans
  calc
    _ = (9 * 128 ^ 2 : ℝ) * 1 * 1 * 1 * 1 * tubeBound (profileBound m epsilon K R) * 1 := by ring
    _ ≤ _ := by
      unfold productBound
      have hJ0 := zero_le_one.trans hJ
      have hcmp0 := zero_le_one.trans hcmp
      have hcol0 := zero_le_one.trans hcol
      have hbad0 := zero_le_one.trans hbad
      have htu0 := zero_le_one.trans (tubeBound_ge_one hT)
      have hden0 := zero_le_one.trans hden
      gcongr

end
end NativeCommonEnvelope
