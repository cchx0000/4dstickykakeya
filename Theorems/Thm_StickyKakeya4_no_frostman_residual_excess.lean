import Theorems.Thm_StickyKakeya4_no_frostman_weighted_residual_decay

/-!
# Arbitrarily fine full residual excess from a strict dimension deficit

For the fixed positive actual source, a strict upper dimension bound rules
out every eventual codimension-two residual power bound. The full original
inverse-secant weight has a finite integral, so a small-radius power bound
would extend to all radii below one. The existing source-faithful energy
criterion would then contradict the assumed strict dimension deficit.

The resulting excess occurs in the full weighted residual content. It does
not assert a fixed-angle graph, a quantitative determinant cutoff, or a
positive lower bound independent of the collision radius.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4.NoFrostmanResidualExcess

/-- The literal residual content is uniformly bounded by its inverse-secant
envelope, without changing its source or collision-time window. -/
theorem weightedResidualContent_le_inverse_secant_integral
    (σ : Measure E3) (b : E3 → E3) (J : Set ℝ) (r : ℝ) :
    weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
      (fun p => b p.1 - b p.2) J r ≤
        ∫⁻ p : E3 × E3, (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹ ∂σ.prod σ := by
  apply lintegral_mono
  intro p
  classical
  dsimp only
  unfold residualContentWeight
  split_ifs <;> simp

/-- A bounded function's local positive power bound extends to all radii
below one, with an explicitly finite enlarged coefficient. -/
theorem extend_small_radius_power_bound
    (Z : ℝ → ℝ≥0∞) (q δ : ℝ) (hq : 0 ≤ q) (hδ : 0 < δ)
    (B C : ℝ≥0∞) (hB : B ≠ ⊤) (hC : C ≠ ⊤)
    (hbound : ∀ r : ℝ, Z r ≤ B)
    (hlocal : ∀ r : ℝ, 0 < r → r < δ → r < 1 →
      Z r ≤ C * (ENNReal.ofReal r) ^ q) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ r : ℝ, 0 < r → r < 1 →
      Z r ≤ K * (ENNReal.ofReal r) ^ q := by
  have hδ0 : ENNReal.ofReal δ ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
  have hδpow : (ENNReal.ofReal δ) ^ (-q) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hδ0 ENNReal.ofReal_ne_top
  let K : ℝ≥0∞ := C + B * (ENNReal.ofReal δ) ^ (-q)
  have hK : K ≠ ⊤ := by dsimp [K]; finiteness
  refine ⟨K, hK, ?_⟩
  intro r hr hr1
  by_cases hrδ : r < δ
  · exact (hlocal r hr hrδ hr1).trans
      (mul_le_mul' (show C ≤ K from le_add_right le_rfl) le_rfl)
  · have hδr : δ ≤ r := le_of_not_gt hrδ
    calc
      Z r ≤ B := hbound r
      _ = (B * (ENNReal.ofReal δ) ^ (-q)) * (ENNReal.ofReal δ) ^ q := by
        rw [mul_assoc, ← ENNReal.rpow_add _ _ hδ0 ENNReal.ofReal_ne_top,
          neg_add_cancel, ENNReal.rpow_zero, mul_one]
      _ ≤ (B * (ENNReal.ofReal δ) ^ (-q)) * (ENNReal.ofReal r) ^ q :=
        mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hδr) hq)
      _ ≤ K * (ENNReal.ofReal r) ^ q :=
        mul_le_mul' (show B * (ENNReal.ofReal δ) ^ (-q) ≤ K from le_add_left le_rfl) le_rfl

/-- Any global full residual power bound forces the corresponding dimension
lower bound on the literally supported original front. -/
theorem front_dimH_ge_of_residual_power_bound
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ) (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v d η t : ℝ) (huv : u < v) (hd : 0 < d)
    (hη : 0 ≤ η) (hη3 : η < 3) (ht : 0 < t) (htt : t < 4 - η)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hres : ∀ r : ℝ, 0 < r → r < 1 →
      weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
        (fun p => b p.1 - b p.2) (Icc (u - d) (v + d)) r ≤
          C * (ENNReal.ofReal r) ^ (2 - η)) :
    ENNReal.ofReal t ≤ dimH (unitFront ambient) := by
  have henergy := OriginalResidualCriterion.sourceFrontMeasure_finite_energy
    σ hσ b hb hslopes u v d η t hd hη hη3 ht htt C hC hres
  let tNN : NNReal := ⟨t, ht.le⟩
  have htNN : 0 < tNN := by exact ht
  have hdim := EnergyDimension.le_dimH_of_supported_finite_energy
    (OriginalResidualCriterion.sourceFrontMeasure σ b u v)
    (OriginalResidualCriterion.sourceFrontMeasure_ne_zero σ hσpos b hb u v huv)
    (unitFront ambient)
    (OriginalResidualCriterion.sourceFrontMeasure_supported σ b hb u v _
      (StickyKakeya4.IsCompact.unitFront hcompact).measurableSet hsupport)
    tNN htNN henergy
  change ENNReal.ofReal (tNN : ℝ) ≤ dimH (unitFront ambient)
  simpa only [ENNReal.ofReal_coe_nnreal] using hdim

/-- A strict dimension deficit forces arbitrarily fine violations of every
finite codimension-two power coefficient in the full original residual
content. No excessive graph or residual lower bound is assumed. -/
theorem arbitrarily_fine_residual_excess_of_dimH_lt
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ) (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v d η t : ℝ) (huv : u < v) (hd : 0 < d)
    (hη : 0 < η) (hη2 : η < 2) (ht : 0 < t) (htt : t < 4 - η)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hdim : dimH (unitFront ambient) < ENNReal.ofReal t)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < min ρ₀ 1 ∧
      C * (ENNReal.ofReal ρ) ^ (2 - η) <
        weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
          (fun p => b p.1 - b p.2) (Icc (u - d) (v + d)) ρ := by
  by_contra hn
  push Not at hn
  let Z : ℝ → ℝ≥0∞ := fun r => weightedResidualContent (σ.prod σ)
    (fun p => p.1 - p.2) (fun p => b p.1 - b p.2) (Icc (u - d) (v + d)) r
  let B : ℝ≥0∞ := ∫⁻ p : E3 × E3, (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹ ∂σ.prod σ
  have hB : B ≠ ⊤ := (NoFrostmanWeightedResidualDecay.finite_inverse_secant_integral σ hσ).ne
  obtain ⟨K, hK, hglobal⟩ := extend_small_radius_power_bound Z (2 - η) ρ₀
    (by linarith) hρ₀ B C hB hC
    (fun r => weightedResidualContent_le_inverse_secant_integral σ b _ r)
    (fun r hr hrρ hr1 => hn r hr (lt_min hrρ hr1))
  exact (not_le_of_gt hdim) (front_dimH_ge_of_residual_power_bound ambient hcompact
    σ hσpos hσ b hb hslopes u v d η t huv hd hη.le (by linarith)
    ht htt hsupport K hK hglobal)

/-- A strict sub-four dimension bound contains a positive residual-exponent
gap and a positive intermediate energy exponent. -/
theorem exists_residual_exponent_gap_of_dimH_lt_four
    {X : Type*} [MetricSpace X] (s : Set X) (hdim : dimH s < (4 : ℝ≥0∞)) :
    ∃ η t : ℝ, 0 < η ∧ η < 2 ∧ 0 < t ∧ t < 4 - η ∧
      dimH s < ENNReal.ofReal t := by
  have htop : dimH s ≠ ⊤ := ne_top_of_lt
    (hdim.trans (by norm_num : (4 : ℝ≥0∞) < ⊤))
  have hreal : (dimH s).toReal < 4 := by
    simpa using (ENNReal.toReal_lt_toReal htop (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)).2 hdim
  have hnonneg : 0 ≤ (dimH s).toReal := ENNReal.toReal_nonneg
  refine ⟨(4 - (dimH s).toReal) / 4, ((dimH s).toReal + 4) / 2,
    by linarith, by linarith, by linarith, by linarith, ?_⟩
  apply (ENNReal.toReal_lt_toReal htop ENNReal.ofReal_ne_top).1
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ ((dimH s).toReal + 4) / 2)]
  linarith

/-- Under a strict dimension deficit the full weighted residual content tends
to zero, yet exceeds every fixed `ρ^(2-η)` coefficient at arbitrarily fine
radii for some positive η. Both statements concern the same actual source. -/
theorem full_residual_decay_and_excess_of_dimH_lt_four
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ) (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v d : ℝ) (huv : u < v) (hd : 0 < d)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hdim : dimH (unitFront ambient) < (4 : ℝ≥0∞)) :
    Tendsto (fun r : ℝ => weightedResidualContent (σ.prod σ)
      (fun p => p.1 - p.2) (fun p => b p.1 - b p.2) (Icc (u - d) (v + d)) r)
      (𝓝[>] 0) (𝓝 0) ∧
    ∃ η : ℝ, 0 < η ∧ η < 2 ∧ ∀ C : ℝ≥0∞, C ≠ ⊤ →
      ∀ ρ₀ : ℝ, 0 < ρ₀ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < min ρ₀ 1 ∧
        C * (ENNReal.ofReal ρ) ^ (2 - η) <
          weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
            (fun p => b p.1 - b p.2) (Icc (u - d) (v + d)) ρ := by
  constructor
  · apply NoFrostmanWeightedResidualDecay.no_front_frostman_tendsto_weightedResidualContent_zero
      ambient hcompact σ hσ b hb hslopes u v huv hsupport
      (fun hf => (not_le_of_gt hdim) (dimH_ge_four_of_front_frostman_measures ambient hf))
      (Icc (u - d) (v + d)) measurableSet_Icc
  · obtain ⟨η, t, hη, hη2, ht, htt, hdimt⟩ :=
      exists_residual_exponent_gap_of_dimH_lt_four (unitFront ambient) hdim
    refine ⟨η, hη, hη2, ?_⟩
    intro C hC ρ₀ hρ₀
    exact arbitrarily_fine_residual_excess_of_dimH_lt ambient hcompact σ hσpos hσ
      b hb hslopes u v d η t huv hd hη hη2 ht htt hsupport hdimt C hC ρ₀ hρ₀

end StickyKakeya4.NoFrostmanResidualExcess
