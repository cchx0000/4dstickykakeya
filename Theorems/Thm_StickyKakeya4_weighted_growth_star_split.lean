import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic
import Theorems.Thm_StickyKakeya4_four_distinct_sources

/-!
# Robust target growth on the low-multiplicity branch

On one source-mass layer `q ≤ qᵢ ≤ 2q`, write the actual target density as
`e = ∑ qᵢ wᵢ` and normalized target multiplicity as `N = ∑ wᵢ`.
The low-multiplicity cut `N ≤ K` gives the pointwise bound `e ≤ 2qK`.
Consequently a retained amount of old-edge mass forces genuinely large target
support, even after discarding a controlled fraction of edge mass.

This avoids claiming growth merely because negligible weights touch a large
target set. The complementary high-multiplicity branch is the input to the
independent-source-index star lemma. These estimates do not assert a global
iteration invariant, source-fiber incidence, or quadratic cross-cap payment.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.WeightedGrowthStarSplit

variable {X I : Type*} [MeasurableSpace X] [Fintype I]

def multiplicity (w : I → X → ℝ≥0∞) (x : X) : ℝ≥0∞ := ∑ i, w i x

def targetDensity (qᵢ : I → ℝ) (w : I → X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (qᵢ i) * w i x

omit [MeasurableSpace X] in
/-- Upper source-mass regularity converts low multiplicity to a pointwise bound
on the actual old-target marginal density. -/
theorem targetDensity_le_on_low_multiplicity
    (qᵢ : I → ℝ) (w : I → X → ℝ≥0∞) (q K : ℝ)
    (hq : 0 ≤ q) (hupper : ∀ i, qᵢ i ≤ 2 * q)
    {x : X} (hlow : multiplicity w x ≤ ENNReal.ofReal K) :
    targetDensity qᵢ w x ≤ ENNReal.ofReal (2 * q * K) := by
  calc
    targetDensity qᵢ w x ≤ ∑ i, ENNReal.ofReal (2 * q) * w i x := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hupper i)) _
    _ = ENNReal.ofReal (2 * q) * multiplicity w x := by
      rw [multiplicity, Finset.mul_sum]
    _ ≤ ENNReal.ofReal (2 * q) * ENNReal.ofReal K := mul_le_mul_right hlow _
    _ = ENNReal.ofReal (2 * q * K) :=
      (ENNReal.ofReal_mul (by positivity)).symm

/-- A bound on a restricted density is domination of measures. -/
theorem restricted_density_le_const_smul
    (σ : Measure X) (e : X → ℝ≥0∞) (L : Set X) (hL : MeasurableSet L)
    (D : ℝ≥0∞) (hbound : ∀ x ∈ L, e x ≤ D) :
    (σ.withDensity e).restrict L ≤ D • σ := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.restrict_apply hS, withDensity_apply _ (hS.inter hL), Measure.smul_apply]
  calc
    (∫⁻ x in S ∩ L, e x ∂σ) ≤ ∫⁻ _x in S ∩ L, D ∂σ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (hS.inter hL)] with x hx
      exact hbound x hx.2
    _ = D * σ (S ∩ L) := by simp
    _ ≤ D * σ S := mul_le_mul_right (measure_mono inter_subset_left) D

/-- The low-multiplicity old-edge marginal has a uniformly bounded density
with respect to the original target measure, before any new normalization. -/
theorem low_multiplicity_measure_domination
    (σ : Measure X) (qᵢ : I → ℝ) (w : I → X → ℝ≥0∞) (q K : ℝ)
    (hq : 0 ≤ q) (hupper : ∀ i, qᵢ i ≤ 2 * q)
    (hL : MeasurableSet {x | multiplicity w x ≤ ENNReal.ofReal K}) :
    (σ.withDensity (targetDensity qᵢ w)).restrict
        {x | multiplicity w x ≤ ENNReal.ofReal K} ≤
      ENNReal.ofReal (2 * q * K) • σ := by
  apply restricted_density_le_const_smul
  · exact hL
  · intro x hx
    exact targetDensity_le_on_low_multiplicity qᵢ w q K hq hupper hx

/-- A retained submeasure with bounded density cannot concentrate substantial
edge mass on a target support of very small selector mass. -/
theorem supported_mass_toReal_le
    (σ : Measure X) [IsFiniteMeasure σ] (ν : Measure X)
    (D : ℝ) (hD : 0 ≤ D) (hdom : ν ≤ ENNReal.ofReal D • σ)
    (H : Set X) (hH : MeasurableSet H) (hsupport : ν Hᶜ = 0) :
    (ν univ).toReal ≤ D * (σ H).toReal := by
  have hmass : ν univ = ν H := by
    simpa only [hsupport, add_zero] using (measure_add_measure_compl (μ := ν) hH).symm
  have hbound : ν univ ≤ ENNReal.ofReal D * σ H := by
    rw [hmass]
    simpa only [Measure.smul_apply, smul_eq_mul] using hdom H
  have hfinite : ENNReal.ofReal D * σ H ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top σ H)
  have hreal := ENNReal.toReal_mono hfinite hbound
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD] using hreal

/-- Exact finite-mass dichotomy for a low/high measurable cut. -/
theorem low_or_high_carries_half (ν : Measure X) [IsFiniteMeasure ν]
    (L : Set X) (hL : MeasurableSet L) :
    (ν univ).toReal / 2 ≤ (ν L).toReal ∨
      (ν univ).toReal / 2 ≤ (ν Lᶜ).toReal := by
  have hsum := measure_add_measure_compl (μ := ν) hL
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (measure_ne_top ν L) (measure_ne_top ν Lᶜ)] at hreal
  by_cases h : (ν univ).toReal / 2 ≤ (ν L).toReal
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- Amplification on comparable source pieces supplies the aggregate input
`E ≥ c K² q Q` used by the robust low-multiplicity estimate. -/
theorem amplified_layer_mass_lower
    (qᵢ Eᵢ : I → ℝ) (q c K : ℝ) (hq : 0 ≤ q) (hc : 0 ≤ c)
    (hlower : ∀ i, q ≤ qᵢ i)
    (hamp : ∀ i, c * K ^ 2 * (qᵢ i) ^ 2 ≤ Eᵢ i) :
    c * K ^ 2 * q * (∑ i, qᵢ i) ≤ ∑ i, Eᵢ i := by
  calc
    c * K ^ 2 * q * (∑ i, qᵢ i) = ∑ i, c * K ^ 2 * q * qᵢ i := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i, Eᵢ i := by
      apply Finset.sum_le_sum
      intro i _
      have hqi : 0 ≤ qᵢ i := hq.trans (hlower i)
      have hsquare : q * qᵢ i ≤ (qᵢ i) ^ 2 := by nlinarith [hlower i]
      calc
        c * K ^ 2 * q * qᵢ i = (c * K ^ 2) * (q * qᵢ i) := by ring
        _ ≤ (c * K ^ 2) * (qᵢ i) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare (by positivity)
        _ ≤ Eᵢ i := hamp i

/-- Quantitative support growth survives an arbitrary retained submeasure.
Here `E` is the incoming edge mass, `Lmass` is its low-multiplicity portion,
and the retained measure keeps at least `1-ε` of that portion. The result is
`σ(H) ≥ (1-ε)cKQ/4`, with `B=K²`. -/
theorem robust_target_support_growth
    (σ : Measure X) [IsFiniteMeasure σ] (ν : Measure X)
    (H : Set X) (hH : MeasurableSet H) (hsupport : ν Hᶜ = 0)
    (q K c Q E Lmass ε : ℝ) (hq : 0 < q) (hK : 0 < K)
    (hε : ε ≤ 1)
    (hamp : c * K ^ 2 * q * Q ≤ E)
    (hlow : E / 2 ≤ Lmass)
    (hretain : (1 - ε) * Lmass ≤ (ν univ).toReal)
    (hdom : ν ≤ ENNReal.ofReal (2 * q * K) • σ) :
    (1 - ε) * c * K * Q / 4 ≤ (σ H).toReal := by
  have hmass := supported_mass_toReal_le σ ν (2 * q * K) (by positivity)
    hdom H hH hsupport
  have hret : 0 ≤ 1 - ε := by linarith
  have hleft : (1 - ε) * (c * K ^ 2 * q * Q) ≤
      (1 - ε) * E := mul_le_mul_of_nonneg_left hamp hret
  have hmid : (1 - ε) * E ≤ 2 * ((1 - ε) * Lmass) := by
    nlinarith [mul_le_mul_of_nonneg_left hlow hret]
  have hchain : q * K * ((1 - ε) * c * K * Q) ≤
      q * K * (4 * (σ H).toReal) := by nlinarith
  have hcancel : (1 - ε) * c * K * Q ≤ 4 * (σ H).toReal :=
    le_of_mul_le_mul_left hchain (mul_pos hq hK)
  linarith

theorem measurable_multiplicity (w : I → X → ℝ≥0∞)
    (hw : ∀ i, Measurable (w i)) : Measurable (multiplicity w) := by
  unfold multiplicity
  fun_prop

/-- Integrated low-branch growth from the actual weighted target density.
Only a relative retained-mass condition is assumed; the needed bounded-density
estimate is proved from the low-multiplicity cut and source-mass regularity. -/
theorem robust_low_multiplicity_support_growth
    (σ : Measure X) [IsFiniteMeasure σ] (ν : Measure X)
    (qᵢ : I → ℝ) (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (H : Set X) (hH : MeasurableSet H) (hsupport : ν Hᶜ = 0)
    (q K c Q E Lmass ε : ℝ) (hq : 0 < q) (hK : 0 < K)
    (hupper : ∀ i, qᵢ i ≤ 2 * q) (hε : ε ≤ 1)
    (hamp : c * K ^ 2 * q * Q ≤ E)
    (hlow : E / 2 ≤ Lmass)
    (hretain : (1 - ε) * Lmass ≤ (ν univ).toReal)
    (hretained : ν ≤ (σ.withDensity (targetDensity qᵢ w)).restrict
      {x | multiplicity w x ≤ ENNReal.ofReal K}) :
    (1 - ε) * c * K * Q / 4 ≤ (σ H).toReal := by
  apply robust_target_support_growth σ ν H hH hsupport q K c Q E Lmass ε
    hq hK hε hamp hlow hretain
  apply hretained.trans
  apply low_multiplicity_measure_domination σ qᵢ w q K hq.le hupper
  exact measurableSet_le (measurable_multiplicity w hw) measurable_const

/-- The complete finite-layer alternative: either the low branch has robust
large target support, or a half-mass high branch admits three independent
fresh source indices distinct from one another and from every fixed inherited
index with probability at least one half. Actual source-point incidence is
supplied separately by the old-target fiber kernels. -/
theorem weighted_growth_or_distinct_source_star
    (σ : Measure X) [IsFiniteMeasure σ]
    (qᵢ : I → ℝ) (w : I → X → ℝ≥0∞)
    [IsFiniteMeasure (σ.withDensity (targetDensity qᵢ w))]
    (hw : ∀ i, Measurable (w i)) (hweights : ∀ i x, w i x ≤ 1)
    (q K c Q : ℝ) (hq : 0 < q) (hK : 12 ≤ K)
    (hupper : ∀ i, qᵢ i ≤ 2 * q)
    (hamp : c * K ^ 2 * q * Q ≤
      ((σ.withDensity (targetDensity qᵢ w)) univ).toReal) :
    c * K * Q / 4 ≤
        (σ {x | multiplicity w x ≤ ENNReal.ofReal K}).toReal ∨
      (((σ.withDensity (targetDensity qᵢ w)) univ).toReal / 2 ≤
          ((σ.withDensity (targetDensity qᵢ w))
            {x | multiplicity w x ≤ ENNReal.ofReal K}ᶜ).toReal ∧
        ∀ x ∈ {x | multiplicity w x ≤ ENNReal.ofReal K}ᶜ, ∀ i : I,
          (1 : ℝ) / 2 ≤ FourDistinctSources.fourDistinctProbability
            (fun j => (w j x / multiplicity w x).toReal) i) := by
  let μ := σ.withDensity (targetDensity qᵢ w)
  let L := {x | multiplicity w x ≤ ENNReal.ofReal K}
  have hL : MeasurableSet L :=
    measurableSet_le (measurable_multiplicity w hw) measurable_const
  have hKpos : 0 < K := by linarith
  rcases low_or_high_carries_half μ L hL with hlow | hhigh
  · left
    have hsupp : (μ.restrict L) Lᶜ = 0 := by
      rw [Measure.restrict_apply hL.compl]
      simp
    have hretain : (1 - (0 : ℝ)) * (μ L).toReal ≤
        ((μ.restrict L) univ).toReal := by simp
    have hgrowth := robust_low_multiplicity_support_growth σ (μ.restrict L)
      qᵢ w hw L hL hsupp q K c Q (μ univ).toReal (μ L).toReal 0 hq hKpos
      hupper (by norm_num) hamp hlow hretain le_rfl
    simpa only [sub_zero, one_mul] using hgrowth
  · right
    refine ⟨hhigh, ?_⟩
    intro x hx i
    change ¬ multiplicity w x ≤ ENNReal.ofReal K at hx
    have hN : ENNReal.ofReal K ≤ ∑ j, w j x :=
      (lt_of_not_ge hx).le
    simpa only [multiplicity] using
      FourDistinctSources.ennreal_weighted_four_distinct_probability_ge_half
        (fun j => w j x) (fun j => hweights j x) K hK hN i

/-- The high-multiplicity success probability integrates linearly over the
whole original occurrence, even when its inherited source index depends on
all the old coordinates. No fourth independent source is substituted for it. -/
theorem high_branch_linear_star_mass
    {Ω : Type*} [MeasurableSpace Ω] (Γ : Measure Ω)
    (inherited : Ω → I) (w : I → Ω → ℝ≥0∞) (K : ℝ) (hK : 12 ≤ K)
    (H : Set Ω) (hH : MeasurableSet H)
    (hweights : ∀ i ω, w i ω ≤ 1)
    (hN : ∀ ω ∈ H, ENNReal.ofReal K ≤ ∑ i, w i ω) :
    (1 / 2 : ℝ≥0∞) * Γ H ≤
      ∫⁻ ω in H, ENNReal.ofReal
        (FourDistinctSources.fourDistinctProbability
          (fun i => (w i ω / ∑ j, w j ω).toReal) (inherited ω)) ∂Γ := by
  calc
    (1 / 2 : ℝ≥0∞) * Γ H = ∫⁻ _ω in H, (1 / 2 : ℝ≥0∞) ∂Γ := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hH] with ω hω
      have hp := FourDistinctSources.ennreal_weighted_four_distinct_probability_ge_half
        (fun i => w i ω) (fun i => hweights i ω) K hK (hN ω hω) (inherited ω)
      simpa using ENNReal.ofReal_le_ofReal hp

/-- A half-mass high-multiplicity branch retains at least one quarter of the
incoming absolute occurrence in distinct-source stars. The success integral
is the actual finite fresh-triple law averaged against the original measure. -/
theorem high_half_branch_retains_quarter
    {Ω : Type*} [MeasurableSpace Ω] (Γ : Measure Ω)
    (inherited : Ω → I) (w : I → Ω → ℝ≥0∞) (K : ℝ) (hK : 12 ≤ K)
    (H : Set Ω) (hH : MeasurableSet H)
    (hweights : ∀ i ω, w i ω ≤ 1)
    (hN : ∀ ω ∈ H, ENNReal.ofReal K ≤ ∑ i, w i ω)
    (hhalf : (1 / 2 : ℝ≥0∞) * Γ univ ≤ Γ H) :
    (1 / 4 : ℝ≥0∞) * Γ univ ≤
      ∫⁻ ω in H, ENNReal.ofReal
        (FourDistinctSources.fourDistinctProbability
          (fun i => (w i ω / ∑ j, w j ω).toReal) (inherited ω)) ∂Γ := by
  calc
    (1 / 4 : ℝ≥0∞) * Γ univ =
        (1 / 2 : ℝ≥0∞) * ((1 / 2 : ℝ≥0∞) * Γ univ) := by
      rw [← mul_assoc]
      norm_num [← ENNReal.mul_inv]
    _ ≤ (1 / 2 : ℝ≥0∞) * Γ H := mul_le_mul_right hhalf _
    _ ≤ _ := high_branch_linear_star_mass Γ inherited w K hK H hH hweights hN

end StickyKakeya4.WeightedGrowthStarSplit
