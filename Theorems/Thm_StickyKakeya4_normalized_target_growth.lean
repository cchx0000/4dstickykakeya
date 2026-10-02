import Theorems.Thm_StickyKakeya4_weighted_growth_star_split

/-!
# Layer-free positive growth and stationary target-conditional star probabilities

Normalized multiplicity `N=∑eᵢ/qᵢ` is used for selector-support growth, while
`e=∑eᵢ` remains the actual old-target marginal density. A finite positive lower
bound on the `qᵢ` is used only to transfer positivity, never as a scale-uniform
retained fraction. This yields the positive-output alternative needed by
qualitative whole-support reversal.

For quantitative source-mass layers, the fresh index law is the stationary
actual law `pᵢ=eᵢ/e`, not `wᵢ/N`. It has atom bound `2/N` on `q≤qᵢ≤2q`, so
`N≥24` gives half success for three fresh sources distinct from the inherited
one. Stationarity of the full occurrence kernel is a separate construction;
no paid or cross-cap power bound is asserted here.
-/

open MeasureTheory Set
open scoped ENNReal
open StickyKakeya4.WeightedGrowthStarSplit StickyKakeya4.FourDistinctSources

noncomputable section

namespace StickyKakeya4.NormalizedTargetGrowth

variable {X I : Type*} [MeasurableSpace X] [Fintype I]

omit [MeasurableSpace X] in
/-- A finite positive source-mass minimum compares normalized multiplicity
with the genuine target density. -/
theorem targetDensity_lower (qᵢ : I → ℝ) (w : I → X → ℝ≥0∞) (q : ℝ)
    (hlower : ∀ i, q ≤ qᵢ i) (x : X) :
    ENNReal.ofReal q * WeightedGrowthStarSplit.multiplicity w x ≤ targetDensity qᵢ w x := by
  rw [WeightedGrowthStarSplit.multiplicity, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hlower i)) _

/-- The comparison is an actual measure inequality. Its coefficient is allowed
to be arbitrarily small; subsequent use is only qualitative positivity. -/
theorem normalized_measure_le_old_measure (σ : Measure X)
    (qᵢ : I → ℝ) (w : I → X → ℝ≥0∞) (q : ℝ)
    (hlower : ∀ i, q ≤ qᵢ i) :
    ENNReal.ofReal q • σ.withDensity (WeightedGrowthStarSplit.multiplicity w) ≤
      σ.withDensity (targetDensity qᵢ w) := by
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_mono
  exact Filter.Eventually.of_forall (targetDensity_lower qᵢ w q hlower)

/-- Positive normalized target mass is positive old-edge mass, without any
uniform conversion factor being claimed. -/
theorem normalized_positive_implies_old_positive (σ : Measure X)
    (qᵢ : I → ℝ) (w : I → X → ℝ≥0∞) (q : ℝ) (hq : 0 < q)
    (hlower : ∀ i, q ≤ qᵢ i) (H : Set X)
    (hpos : (σ.withDensity (WeightedGrowthStarSplit.multiplicity w)) H ≠ 0) :
    (σ.withDensity (targetDensity qᵢ w)) H ≠ 0 := by
  have h := normalized_measure_le_old_measure σ qᵢ w q hlower H
  rw [Measure.smul_apply, smul_eq_mul] at h
  exact ne_zero_of_lt ((bot_lt_iff_ne_bot.mpr
    (mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hq) hpos)).trans_le h)

omit [MeasurableSpace X] in
theorem multiplicity_le_card (w : I → X → ℝ≥0∞)
    (hw : ∀ i x, w i x ≤ 1) (x : X) :
    WeightedGrowthStarSplit.multiplicity w x ≤ (Fintype.card I : ℝ≥0∞) := by
  calc
    WeightedGrowthStarSplit.multiplicity w x ≤ ∑ _i : I, (1 : ℝ≥0∞) := by
      exact Finset.sum_le_sum (fun i _ => hw i x)
    _ = (Fintype.card I : ℝ≥0∞) := by simp

/-- The normalized multiplicity measure is finite for every finite source
family; no lower bound on individual source masses is needed for this. -/
theorem finite_normalized_measure (σ : Measure X) [IsFiniteMeasure σ]
    (w : I → X → ℝ≥0∞) (hw : ∀ i x, w i x ≤ 1) :
    IsFiniteMeasure (σ.withDensity (WeightedGrowthStarSplit.multiplicity w)) := by
  apply isFiniteMeasure_withDensity
  have hbound : (∫⁻ x, WeightedGrowthStarSplit.multiplicity w x ∂σ) ≤
      (Fintype.card I : ℝ≥0∞) * σ univ := by
    calc
      (∫⁻ x, WeightedGrowthStarSplit.multiplicity w x ∂σ) ≤ ∫⁻ _x, (Fintype.card I : ℝ≥0∞) ∂σ :=
        lintegral_mono (multiplicity_le_card w hw)
      _ = _ := lintegral_const _
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (measure_ne_top σ univ)) hbound

/-- Normalized low multiplicity produces whole-selector-support growth. -/
theorem normalized_low_support_growth (σ : Measure X) [IsFiniteMeasure σ]
    (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (K c Q W : ℝ) (hK : 0 < K)
    (hamp : c * K ^ 2 * Q ≤ W)
    (hlow : W / 2 ≤ ((σ.withDensity (WeightedGrowthStarSplit.multiplicity w))
      {x | WeightedGrowthStarSplit.multiplicity w x ≤ ENNReal.ofReal K}).toReal) :
    c * K * Q / 2 ≤ (σ {x | WeightedGrowthStarSplit.multiplicity w x ≤ ENNReal.ofReal K}).toReal := by
  let μ := σ.withDensity (WeightedGrowthStarSplit.multiplicity w)
  let L := {x | WeightedGrowthStarSplit.multiplicity w x ≤ ENNReal.ofReal K}
  have hL : MeasurableSet L :=
    measurableSet_le (measurable_multiplicity w hw) measurable_const
  have hdom : μ.restrict L ≤ ENNReal.ofReal K • σ :=
    restricted_density_le_const_smul σ (WeightedGrowthStarSplit.multiplicity w) L hL _ (fun _ hx => hx)
  have hsupp : (μ.restrict L) Lᶜ = 0 := by
    rw [Measure.restrict_apply hL.compl]
    simp
  have hmass := supported_mass_toReal_le σ (μ.restrict L) K hK.le hdom L hL hsupp
  simp only [Measure.restrict_apply_univ] at hmass
  have hchain : K * (c * K * Q) ≤ K * (2 * (σ L).toReal) := by nlinarith
  have hcancel := le_of_mul_le_mul_left hchain hK
  linarith

/-- No dyadic source-mass comparison is needed for a positive-output route:
low normalized mass gives growth, while high normalized mass gives positive
OLD mass and genuine distinct-source witnesses. The `q` minimum is not used
to promise any scale-uniform old-mass retention. -/
theorem layer_free_growth_or_positive_old_star
    (σ : Measure X) [IsFiniteMeasure σ]
    (qᵢ : I → ℝ) (w : I → X → ℝ≥0∞)
    (hw : ∀ i, Measurable (w i)) (hweights : ∀ i x, w i x ≤ 1)
    (q K c Q : ℝ) (hq : 0 < q) (hK : 12 ≤ K) (hc : 0 < c) (hQ : 0 < Q)
    (hlower : ∀ i, q ≤ qᵢ i)
    (hamp : c * K ^ 2 * Q ≤ ((σ.withDensity (WeightedGrowthStarSplit.multiplicity w)) univ).toReal) :
    c * K * Q / 2 ≤ (σ {x | WeightedGrowthStarSplit.multiplicity w x ≤ ENNReal.ofReal K}).toReal ∨
      ((σ.withDensity (targetDensity qᵢ w))
          {x | WeightedGrowthStarSplit.multiplicity w x ≤ ENNReal.ofReal K}ᶜ ≠ 0 ∧
        ∀ x ∈ {x | WeightedGrowthStarSplit.multiplicity w x ≤ ENNReal.ofReal K}ᶜ, ∀ i : I,
          (1 : ℝ) / 2 ≤ fourDistinctProbability
            (fun j => (w j x / WeightedGrowthStarSplit.multiplicity w x).toReal) i) := by
  let μ := σ.withDensity (WeightedGrowthStarSplit.multiplicity w)
  let L := {x | WeightedGrowthStarSplit.multiplicity w x ≤ ENNReal.ofReal K}
  let : IsFiniteMeasure μ := finite_normalized_measure σ w hweights
  have hL : MeasurableSet L :=
    measurableSet_le (measurable_multiplicity w hw) measurable_const
  have hKpos : 0 < K := by linarith
  rcases low_or_high_carries_half μ L hL with hlow | hhigh
  · exact Or.inl (normalized_low_support_growth σ w hw K c Q _ hKpos hamp hlow)
  · right
    have hWpos : 0 < (μ univ).toReal := lt_of_lt_of_le (by positivity) hamp
    have hhighpos : μ Lᶜ ≠ 0 := by
      intro hz
      have : (μ Lᶜ).toReal = 0 := by rw [hz]; rfl
      linarith
    refine ⟨normalized_positive_implies_old_positive σ qᵢ w q hq hlower Lᶜ hhighpos, ?_⟩
    intro x hx i
    change ¬ WeightedGrowthStarSplit.multiplicity w x ≤ ENNReal.ofReal K at hx
    exact ennreal_weighted_four_distinct_probability_ge_half
      (fun j => w j x) (fun j => hweights j x) K hK (lt_of_not_ge hx).le i

/-- The stationary actual weights `qᵢwᵢ` have atoms at most `2/K` when the
source masses are comparable and normalized multiplicity is at least `K`. -/
theorem stationary_atom_le (qᵢ w : I → ℝ) (q K : ℝ)
    (hq : 0 < q) (hK : 0 < K)
    (hlower : ∀ i, q ≤ qᵢ i) (hupper : ∀ i, qᵢ i ≤ 2 * q)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hN : K ≤ ∑ i, w i) (i : I) :
    normalizedWeights (fun j => qᵢ j * w j) i ≤ 2 / K := by
  have hsumlower : q * K ≤ ∑ j, qᵢ j * w j := by
    calc
      q * K ≤ q * ∑ j, w j := mul_le_mul_of_nonneg_left hN hq.le
      _ = ∑ j, q * w j := Finset.mul_sum ..
      _ ≤ ∑ j, qᵢ j * w j := Finset.sum_le_sum
        (fun j _ => mul_le_mul_of_nonneg_right (hlower j) (hw0 j))
  have hsumpos : 0 < ∑ j, qᵢ j * w j := (mul_pos hq hK).trans_le hsumlower
  have hui : qᵢ i * w i ≤ 2 * q := by
    calc
      qᵢ i * w i ≤ qᵢ i * 1 :=
        mul_le_mul_of_nonneg_left (hw1 i) (hq.le.trans (hlower i))
      _ ≤ 2 * q := by simpa using hupper i
  unfold normalizedWeights
  apply (div_le_div_iff₀ hsumpos hK).mpr
  nlinarith [mul_le_mul_of_nonneg_right hui hK.le]

/-- Under the stationary actual target-conditional law, the fixed-inherited
four-source event has probability at least one half when `N≥24`. -/
theorem stationary_four_distinct_probability_ge_half
    (qᵢ w : I → ℝ) (q K : ℝ) (hq : 0 < q) (hK : 24 ≤ K)
    (hlower : ∀ i, q ≤ qᵢ i) (hupper : ∀ i, qᵢ i ≤ 2 * q)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hN : K ≤ ∑ i, w i) (i : I) :
    (1 : ℝ) / 2 ≤ fourDistinctProbability
      (normalizedWeights (fun j => qᵢ j * w j)) i := by
  have hKpos : 0 < K := by linarith
  have hsumpos : 0 < ∑ j, qᵢ j * w j := by
    have hsumlower : q * K ≤ ∑ j, qᵢ j * w j := by
      calc
        q * K ≤ q * ∑ j, w j := mul_le_mul_of_nonneg_left hN hq.le
        _ = ∑ j, q * w j := Finset.mul_sum ..
        _ ≤ ∑ j, qᵢ j * w j := Finset.sum_le_sum
          (fun j _ => mul_le_mul_of_nonneg_right (hlower j) (hw0 j))
    exact (mul_pos hq hKpos).trans_le hsumlower
  apply four_distinct_probability_ge_half
    (normalizedWeights (fun j => qᵢ j * w j))
    (normalizedWeights_nonneg _ (fun j => mul_nonneg (hq.le.trans (hlower j)) (hw0 j)))
    (normalizedWeights_sum _ hsumpos) (2 / K)
    (stationary_atom_le qᵢ w q K hq hKpos hlower hupper hw0 hw1 hN)
  apply (div_le_div_iff₀ hKpos (by norm_num : (0 : ℝ) < 12)).mpr
  linarith

/-- ENNReal incidence weights feed the stationary probability law directly;
there is no replacement of `eᵢ/e` by normalized occurrence source mass. -/
theorem stationary_ennreal_four_distinct_probability_ge_half
    (qᵢ : I → ℝ) (w : I → ℝ≥0∞) (q K : ℝ) (hq : 0 < q) (hK : 24 ≤ K)
    (hlower : ∀ i, q ≤ qᵢ i) (hupper : ∀ i, qᵢ i ≤ 2 * q)
    (hw : ∀ i, w i ≤ 1) (hN : ENNReal.ofReal K ≤ ∑ i, w i) (i : I) :
    (1 : ℝ) / 2 ≤ fourDistinctProbability
      (fun j => ((ENNReal.ofReal (qᵢ j) * w j) /
        ∑ k, ENNReal.ofReal (qᵢ k) * w k).toReal) i := by
  have hqnonneg (j : I) : 0 ≤ qᵢ j := hq.le.trans (hlower j)
  have hfinite (j : I) : w j ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hw j)
  have hfinite_u (j : I) : ENNReal.ofReal (qᵢ j) * w j ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite j)
  have hKpos : 0 < K := by linarith
  have hNreal : K ≤ ∑ j, (w j).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun j _ => hfinite j)) hN
    simpa only [ENNReal.toReal_ofReal hKpos.le,
      ENNReal.toReal_sum (fun j _ => hfinite j)] using h
  have hwreal (j : I) : (w j).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top (hw j)
  have heq : (fun j => ((ENNReal.ofReal (qᵢ j) * w j) /
      ∑ k, ENNReal.ofReal (qᵢ k) * w k).toReal) =
      normalizedWeights (fun j => qᵢ j * (w j).toReal) := by
    funext j
    simp only [normalizedWeights, ENNReal.toReal_div,
      ENNReal.toReal_sum (fun j _ => hfinite_u j), ENNReal.toReal_mul]
    simp_rw [ENNReal.toReal_ofReal (hqnonneg _)]
  rw [heq]
  exact stationary_four_distinct_probability_ge_half qᵢ (fun j => (w j).toReal) q K hq hK
    hlower hupper (fun _ => ENNReal.toReal_nonneg) hwreal hNreal i

end StickyKakeya4.NormalizedTargetGrowth
