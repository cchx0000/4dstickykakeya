import Theorems.Thm_StickyKakeya4_vector_bush_frostman
import Theorems.Thm_StickyKakeya4_compact_front_frostman_limit
import Theorems.Thm_StickyKakeya4_frostman_mass_distribution

/-!
# The original synchronized vector-family Frostman escape

This is the compact-front completion of the original manuscript's Theorem
8.11, conditional on its actual synchronized vector-cap hypothesis.  At each
scale we retain the entire finite bush family, normalize its total mass, and
use the proved physical family ball estimate.  The total mass may tend to
zero and no individual bush is required to have a mass bounded below.

One uniform coefficient and shrinking lower scales permit Prokhorov
compactness.  The limit is a probability carried by the literal original
compact unit front, with exponent `d+1`; the mass distribution principle
then gives the corresponding Hausdorff lower bound.

The original open-cap convention is retained by the final endpoint; a proved
radius-doubling argument converts it to the closed caps used in the physical
comparison, with coefficient `max C 1 * 2^d`.

The geometric production of the vector-cap estimate is not asserted here.
The same outer point and time occur in every cap of every stated sum.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section

namespace StickyKakeya4.VectorBushEscape

open VectorBushFrostman

/-- Full-family vector-bush escape on the original compact unit front.
Only the total mass of each finite family must be positive; neither a
uniform family-mass lower bound nor an individual-bush lower bound is used. -/
theorem exists_front_frostman_of_vector_families
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (N : ℕ → ℕ) (σ : (n : ℕ) → Fin (N n) → Measure E3)
    [∀ (n : ℕ) (i : Fin (N n)), IsFiniteMeasure (σ n i)]
    (hq : ∀ n, 0 < (Measure.sum (σ n)) univ)
    (b : E3 → E3) (hb : Measurable b)
    (c : (n : ℕ) → Fin (N n) → E3) (s₀ : (n : ℕ) → Fin (N n) → ℝ)
    (u v g K d : ℝ) (C : ℝ≥0∞)
    (huv : u < v) (hg : 0 < g) (hK : 2 / g ≤ K) (hK1 : 1 ≤ K)
    (hd : 0 < d) (hC : C ≠ ∞)
    (ε ρ : ℕ → ℝ) (hερ : ∀ n, ε n ≤ ρ n) (hρ : Tendsto ρ atTop (𝓝 0))
    (hbush : ∀ n i, ∀ᵐ a ∂σ n i, ‖b a + s₀ n i • a - c n i‖ ≤ ε n)
    (hgap : ∀ n i, ∀ s ∈ Icc u v, g ≤ |s - s₀ n i|)
    (hsupport : ∀ n i, ∀ᵐ a ∂σ n i, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hvector : ∀ n (y : E3) (s : ℝ), s ∈ Icc u v → ∀ R : ℝ,
      ρ n ≤ R → R ≤ 1 →
        (∑' i, σ n i (Metric.closedBall (vectorCenter (c n i) y (s₀ n i) s) R)) ≤
          C * (Measure.sum (σ n)) univ * ENNReal.ofReal R ^ d) :
    ∃ μ : Measure E4, IsProbabilityMeasure μ ∧ μ (unitFront ambient)ᶜ = 0 ∧
      ∃ D : ℝ≥0∞, D ≠ ∞ ∧
        (∀ (x : E4) (r : ℝ), 0 < r →
          μ (Metric.ball x r) ≤ D * (ENNReal.ofReal r) ^ (d + 1)) ∧
        ENNReal.ofReal (d + 1) ≤ dimH (unitFront ambient) := by
  let μs : ℕ → Measure E4 := fun n => familyFrontProbability (σ n) b u v
  have hprob : ∀ n, IsProbabilityMeasure (μs n) := fun n =>
    familyFrontProbability_isProbability (σ n) (hq n) b hb u v huv
  have hcarried : ∀ n, μs n (unitFront ambient)ᶜ = 0 := fun n =>
    familyFrontProbability_supported (σ n) b hb u v ambient hcompact (hsupport n)
  let D₀ : ℝ≥0∞ := familyFrostmanConstant u v K d C
  have hD₀ : D₀ ≠ ∞ := familyFrostmanConstant_ne_top u v K d C huv hd.le hC
  have hscale : ∀ n x r, 0 < r → ρ n ≤ r → r ≤ 1 →
      μs n (Metric.ball x r) ≤ D₀ * (ENNReal.ofReal r) ^ (d + 1) := by
    intro n x r hr hρr _hr1
    exact familyFrontProbability_finite_scale_bound (σ n) (hq n) b hb (c n) (s₀ n)
      u v (ε n) (ρ n) g K d C huv (hερ n) hg hK hK1 hd.le
      (hbush n) (hgap n) (hvector n) x r hr hρr
  obtain ⟨μ, hμ, hμK, hD, hμball⟩ :=
    CompactFrontLimit.exists_supported_frostman_probability
      (StickyKakeya4.IsCompact.unitFront hcompact) μs hprob hcarried
      ρ hρ D₀ hD₀ (d + 1) (by linarith) hscale
  letI : IsProbabilityMeasure μ := hμ
  refine ⟨μ, hμ, hμK, max D₀ 1, hD, hμball, ?_⟩
  let t : ℝ≥0 := ⟨d + 1, by linarith⟩
  have ht : 0 < t := by change (0 : ℝ) < d + 1; linarith
  have hhaus : Measure.hausdorffMeasure (t : ℝ) (unitFront ambient) ≠ 0 :=
    hausdorffMeasure_ne_zero_of_ball_growth μ (unitFront ambient) hμK (max D₀ 1) hD
      t ht (fun x r hr _hr1 => hμball x r hr)
  have hdim : (t : ℝ≥0∞) ≤ dimH (unitFront ambient) :=
    le_dimH_of_hausdorffMeasure_ne_zero hhaus
  change ENNReal.ofReal (t : ℝ) ≤ dimH (unitFront ambient)
  simpa only [ENNReal.ofReal_coe_nnreal] using hdim

/-- The original open-cap convention implies the closed-cap estimate needed
for the physical comparison, at a fixed explicit coefficient loss.  Small
radii are doubled; larger radii are bounded by the total family mass. -/
theorem closed_cap_sum_le_of_open_cap_sum
    {m : ℕ} (σ : Fin m → Measure E3) (z : Fin m → E3)
    (ρ R d : ℝ) (C : ℝ≥0∞) (hρ : 0 < ρ) (hd : 0 ≤ d)
    (hρR : ρ ≤ R) (hR1 : R ≤ 1)
    (hopen : ∀ T : ℝ, ρ ≤ T → T ≤ 1 →
      (∑' i, σ i (Metric.ball (z i) T)) ≤
        C * (Measure.sum σ) univ * (ENNReal.ofReal T) ^ d) :
    (∑' i, σ i (Metric.closedBall (z i) R)) ≤
      (max C 1 * (2 : ℝ≥0∞) ^ d) * (Measure.sum σ) univ * (ENNReal.ofReal R) ^ d := by
  have hR : 0 < R := hρ.trans_le hρR
  by_cases hsmall : R ≤ 1 / 2
  · calc
      _ ≤ ∑' i, σ i (Metric.ball (z i) (2 * R)) := by
        apply ENNReal.tsum_le_tsum
        intro i
        exact measure_mono (Metric.closedBall_subset_ball (by linarith))
      _ ≤ C * (Measure.sum σ) univ * (ENNReal.ofReal (2 * R)) ^ d :=
        hopen (2 * R) (by linarith) (by linarith)
      _ = C * (2 : ℝ≥0∞) ^ d * (Measure.sum σ) univ * (ENNReal.ofReal R) ^ d := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.mul_rpow_of_nonneg _ _ hd]
        norm_num only [ENNReal.ofReal_ofNat]
        ring
      _ ≤ _ := by gcongr; exact le_max_left C 1
  · have htwoR : (1 : ℝ≥0∞) ≤ 2 * ENNReal.ofReal R := by
      calc
        1 = ENNReal.ofReal (1 : ℝ) := by simp
        _ ≤ ENNReal.ofReal (2 * R) := ENNReal.ofReal_le_ofReal (by linarith)
        _ = 2 * ENNReal.ofReal R := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    have hpow : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ d * (ENNReal.ofReal R) ^ d := by
      simpa only [ENNReal.one_rpow, ENNReal.mul_rpow_of_nonneg _ _ hd] using
        ENNReal.rpow_le_rpow htwoR hd
    have hone : (1 : ℝ≥0∞) ≤ max C 1 * ((2 : ℝ≥0∞) ^ d * (ENNReal.ofReal R) ^ d) :=
      one_le_mul_of_one_le_of_one_le (le_max_right C 1) hpow
    calc
      _ ≤ ∑' i, σ i univ := ENNReal.tsum_le_tsum (fun _ => measure_mono (subset_univ _))
      _ = (Measure.sum σ) univ := (Measure.sum_apply _ MeasurableSet.univ).symm
      _ = (Measure.sum σ) univ * 1 := by simp
      _ ≤ (Measure.sum σ) univ *
          (max C 1 * ((2 : ℝ≥0∞) ^ d * (ENNReal.ofReal R) ^ d)) := by
        gcongr
      _ = _ := by ring

/-- The normalization in equation (340) is exactly equivalent to its
mass-weighted form, because the actual total family mass is positive and finite. -/
theorem normalized_open_cap_sum_le_iff
    {m : ℕ} (σ : Fin m → Measure E3) [∀ i, IsFiniteMeasure (σ i)]
    (hq : 0 < (Measure.sum σ) univ) (z : Fin m → E3) (R d : ℝ) (C : ℝ≥0∞) :
    ((Measure.sum σ) univ)⁻¹ * (∑' i, σ i (Metric.ball (z i) R)) ≤
        C * (ENNReal.ofReal R) ^ d ↔
      (∑' i, σ i (Metric.ball (z i) R)) ≤
        C * (Measure.sum σ) univ * (ENNReal.ofReal R) ^ d := by
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (ENNReal.inv_mul_le_iff (y := ∑' i, σ i (Metric.ball (z i) R))
      (z := C * (ENNReal.ofReal R) ^ d) hq.ne' (measure_ne_top _ _))

/-- Original-open-ball version of the synchronized vector-family escape.
The ball convention is converted by proof, rather than strengthened silently
into a closed-cap hypothesis.  No individual bush is selected. -/
theorem exists_front_frostman_of_open_vector_families
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (N : ℕ → ℕ) (σ : (n : ℕ) → Fin (N n) → Measure E3)
    [∀ (n : ℕ) (i : Fin (N n)), IsFiniteMeasure (σ n i)]
    (hq : ∀ n, 0 < (Measure.sum (σ n)) univ)
    (b : E3 → E3) (hb : Measurable b)
    (c : (n : ℕ) → Fin (N n) → E3) (s₀ : (n : ℕ) → Fin (N n) → ℝ)
    (u v g K d : ℝ) (C : ℝ≥0∞)
    (huv : u < v) (hg : 0 < g) (hK : 2 / g ≤ K) (hK1 : 1 ≤ K)
    (hd : 0 < d) (hC : C ≠ ∞)
    (ε ρ : ℕ → ℝ) (hερ : ∀ n, ε n ≤ ρ n)
    (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop (𝓝 0))
    (hbush : ∀ n i, ∀ᵐ a ∂σ n i, ‖b a + s₀ n i • a - c n i‖ ≤ ε n)
    (hgap : ∀ n i, ∀ s ∈ Icc u v, g ≤ |s - s₀ n i|)
    (hsupport : ∀ n i, ∀ᵐ a ∂σ n i, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hvector : ∀ n (y : E3) (s : ℝ), s ∈ Icc u v → ∀ R : ℝ,
      ρ n ≤ R → R ≤ 1 →
        ((Measure.sum (σ n)) univ)⁻¹ *
          (∑' i, σ n i (Metric.ball (vectorCenter (c n i) y (s₀ n i) s) R)) ≤
            C * ENNReal.ofReal R ^ d) :
    ∃ μ : Measure E4, IsProbabilityMeasure μ ∧ μ (unitFront ambient)ᶜ = 0 ∧
      ∃ D : ℝ≥0∞, D ≠ ∞ ∧
        (∀ (x : E4) (r : ℝ), 0 < r →
          μ (Metric.ball x r) ≤ D * (ENNReal.ofReal r) ^ (d + 1)) ∧
        ENNReal.ofReal (d + 1) ≤ dimH (unitFront ambient) := by
  let C' : ℝ≥0∞ := max C 1 * (2 : ℝ≥0∞) ^ d
  have hC' : C' ≠ ∞ := by dsimp [C']; finiteness
  apply exists_front_frostman_of_vector_families ambient hcompact N σ hq b hb c s₀
    u v g K d C' huv hg hK hK1 hd hC' ε ρ hερ hρ hbush hgap hsupport
  intro n y s hs R hρR hR1
  exact closed_cap_sum_le_of_open_cap_sum (σ n)
    (fun i => vectorCenter (c n i) y (s₀ n i) s) (ρ n) R d C
    (hρpos n) hd.le hρR hR1 (fun T hρT hT1 =>
      (normalized_open_cap_sum_le_iff (σ n) (hq n)
        (fun i => vectorCenter (c n i) y (s₀ n i) s) T d C).mp
          (hvector n y s hs T hρT hT1))

end StickyKakeya4.VectorBushEscape
