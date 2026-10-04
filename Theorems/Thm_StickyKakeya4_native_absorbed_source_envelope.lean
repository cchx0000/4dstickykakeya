import Theorems.Thm_StickyKakeya4_native_envelope_growth
import Theorems.Thm_StickyKakeya4_native_source_size_bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

namespace NativeAbsorbedSourceEnvelope
open NativeCommonEnvelope NativeEnvelopeGrowth NativeAlignmentParameterBudget NativeSourceSizeBounds
open NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeSelectedParentPreparation NativeParentSpines
open NativeAngularChartSelection SmallFiberAlignment FiniteVoronoiRealADCoarsening

noncomputable section

/-- The actual worst coefficient is absorbed from original AD alone: both
radices are the prescribed ceiling roots of the original source cardinality. -/
theorem source_envelope_absorbed {zeta : ℝ} (hzeta : 0 < zeta) (B : Choice zeta) :
    ∃ n0 : ℕ, ∀ (A : Finset Plane) (delta K t : ℝ) (Nold : ℕ), n0 ≤ Nold →
      A.Nonempty → 0 < delta → delta ≤ 1 → 1 ≤ K → K ≤ delta ^ (-B.eta) → t ≤ 2 →
      (1 : ℝ) / 128 ≤ scale delta Nold →
      (∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) → ADBounds A delta K t →
      ∀ {E0 : Finset A} (D : StoppedProfile (position A) delta B.epsilon K t Nold E0) (k : ℕ),
      let ia := workingLevel D.pair.1 (D.pair.2 - D.pair.1) B.m k
      let ib := workingLevel D.pair.1 (D.pair.2 - D.pair.1) B.m (k + 1)
      let R : ℝ := (2 ^ (ib - ia + 6) : ℕ)
      envelope (Fintype.card (Index Nold)) (epochCost A Nold)
        (refinementCost (B.m + 1) B.L1) (retentionCost ((B.H + 1) + ((B.H + 1) + 1)) B.L2)
        (radix A.card B.L1) (radix A.card B.L2) K R B.m B.H B.epsilon ≤ R ^ zeta := by
  let F1 : ℝ := refinementCost (B.m + 1) B.L1
  let F2 : ℝ := retentionCost ((B.H + 1) + ((B.H + 1) + 1)) B.L2
  have hF1 : 0 ≤ F1 := Nat.cast_nonneg _
  have hF2 : 0 ≤ F2 := Nat.cast_nonneg _
  have hC : 0 ≤ growthCoefficient F1 F2 B.m B.epsilon := by
    unfold growthCoefficient
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (fixedCoefficient_nonneg _ _) (sq_nonneg _)) hF2) (by norm_num)) (by positivity)
  obtain ⟨n0, hn0⟩ := absorb_common_envelope hzeta B (growthCoefficient F1 F2 B.m B.epsilon) hC
  refine ⟨n0, ?_⟩
  intro A delta K t Nold hn hne hdelta hdeltaone hK hKsmall ht2 htop hdiam hAD E0 D k
  dsimp only
  let ia := workingLevel D.pair.1 (D.pair.2 - D.pair.1) B.m k
  let ib := workingLevel D.pair.1 (D.pair.2 - D.pair.1) B.m (k + 1)
  let R : ℝ := (2 ^ (ib - ia + 6) : ℕ)
  have hcard : A.card ≤ 2 ^ (3 * Nold + 21) :=
    source_card_le_pow A hne hdelta hdeltaone ht2 B.eta_one hKsmall htop hdiam hAD
  have hIE : (Fintype.card (Index Nold) : ℝ) * (epochCost A Nold : ℝ) ≤
      88 * ((Nold : ℝ) + 1) ^ 5 := epoch_factor_real_le hcard
  have hq1 := radix_le_dyadic hne.card_pos B.L1_pos hcard
  have hq2 := radix_le_dyadic hne.card_pos B.L2_pos hcard
  have hk := K_pow_eighteen_le hdelta (zero_le_one.trans hK) B.eta_pos.le B.eta_one hKsmall htop
  have hbound := envelope_le_growth (I := (Fintype.card (Index Nold) : ℝ)) (E := (epochCost A Nold : ℝ))
    (F1 := F1) (F2 := F2) (Q1 := (radix A.card B.L1 : ℝ)) (Q2 := (radix A.card B.L2 : ℝ))
    (K := K) (R := R) (eta := B.eta) (epsilon := B.epsilon) Nold B.m B.H B.L1 B.L2
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hF1 hF2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (zero_le_one.trans hK) (Nat.cast_nonneg _) hIE hq1 hq2 hk
  exact hbound.trans (hn0 Nold hn R (output_extent_lower (position A) D hdelta k B.m B.m_pos))

end
end NativeAbsorbedSourceEnvelope
