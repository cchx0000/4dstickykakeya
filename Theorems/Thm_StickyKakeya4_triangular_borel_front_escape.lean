import Theorems.Thm_StickyKakeya4_parameterized_scalar_potential
import Theorems.Thm_StickyKakeya4_triangular_potential_escape

/-!
# Full-dimensional fronts for Borel triangular intercepts

The three intercept coordinates may be arbitrary measurable functions of the
preceding slope coordinates and their own coordinate. A finite nonzero actual
source dominated by a product of finite bounded-density scalar sources yields
probability Frostman measures of every exponent 1+3s, 0<s<1, supported on the
original front. All scalar potential hypotheses are derived internally.
-/

/-!
# Actual fronts of arbitrary Borel triangular selectors

Every potential measurability and finiteness input is derived from the bounded
coordinate reference densities. The actual source may be coupled; its literal
source/time pushforward support is preserved. The final dimension-four theorem
has no unproved energy or Frostman certificate. General selectors are not
asserted to admit this triangular representation.
-/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4.TriangularBorelFrontEscape
open ScalarProjection TriangularPotentialEscape EnergyDimension

def affine₁ (b : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := b p.2+p.1*p.2

def affine₂ (b : ℝ × ℝ → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ := b p.2+p.1*p.2.2

def affine₃ (b : Source → ℝ) (p : ℝ × Source) : ℝ := b p.2+p.1*p.2.2

theorem ae_finite_lift_right
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (τ : Measure ℝ) (ν : Measure X) (η : Measure Y) [SFinite ν] [SFinite η]
    (P : ℝ × X → ℝ≥0∞) (hP : Measurable P)
    (hfin : ∀ᵐ p ∂τ.prod ν, P p < ∞) :
    ∀ᵐ p ∂τ.prod (ν.prod η), P (p.1,p.2.1) < ∞ := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_lt (hP.comp (by fun_prop)) measurable_const)).mpr
  filter_upwards [Measure.ae_ae_of_ae_prod hfin] with t ht
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_lt (hP.comp (by fun_prop)) measurable_const)).mpr
  filter_upwards [ht] with x hx
  exact ae_of_all _ (fun _ => hx)

/-- Arbitrary measurable triangular intercepts yield an actual supported
Frostman measure of exponent 1+3s. Every native potential hypothesis is derived
from bounded coordinate densities; the support is the original point map. -/
theorem exists_triangular_borel_supported_frostman
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (D₁ D₂ D₃ : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (hμ₁ : μ₁ ≤ ENNReal.ofReal D₁ • volume)
    (hμ₂ : μ₂ ≤ ENNReal.ofReal D₂ • volume)
    (hμ₃ : μ₃ ≤ ENNReal.ofReal D₃ • volume)
    (σ : Measure Source) [IsFiniteMeasure σ] (hσ : σ ≠ 0)
    (D : ℝ≥0∞) (hD : D ≠ ∞) (hdom : σ ≤ D • ((μ₁.prod μ₂).prod μ₃))
    (u v : ℝ) (huv : u < v)
    (b₁ : ℝ → ℝ) (b₂ : ℝ × ℝ → ℝ) (b₃ : Source → ℝ)
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) (hb₃ : Measurable b₃)
    (K : Set E4)
    (hsupport : (((volume.restrict (Icc u v)).prod σ).map
      (point (affine₁ b₁) (affine₂ b₂) (affine₃ b₃))) Kᶜ = 0)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∃ ν : Measure E4, IsProbabilityMeasure ν ∧ ν Kᶜ = 0 ∧
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x r, 0 < r →
        ν (Metric.ball x r) ≤ C * ENNReal.ofReal r ^ (1+3*s) := by
  let τ : Measure ℝ := volume.restrict (Icc u v)
  let ρ : Measure Source := (μ₁.prod μ₂).prod μ₃
  let f₁ : Unit × ℝ → ℝ := fun p => b₁ p.2
  have hf₁ : Measurable f₁ := hb₁.comp measurable_snd
  have hg₁ : Measurable (affine₁ b₁) := by unfold affine₁; fun_prop
  have hg₂ : Measurable (affine₂ b₂) := by unfold affine₂; fun_prop
  have hg₃ : Measurable (affine₃ b₃) := by unfold affine₃; fun_prop
  have e₁ : potential₁ μ₁ (affine₁ b₁) s =
      fun p => parameterizedScalarPotential μ₁ f₁ s (p.1,((),p.2)) := by
    funext p
    exact (parameterizedScalarPotential_eq_map_potential μ₁ f₁ hf₁ s p.1 () p.2).symm
  have e₂ : potential₂ μ₂ (affine₂ b₂) s = parameterizedScalarPotential μ₂ b₂ s := by
    funext p
    exact (parameterizedScalarPotential_eq_map_potential μ₂ b₂ hb₂ s p.1 p.2.1 p.2.2).symm
  have e₃ : potential₃ μ₃ (affine₃ b₃) s = parameterizedScalarPotential μ₃ b₃ s := by
    funext p
    exact (parameterizedScalarPotential_eq_map_potential μ₃ b₃ hb₃ s p.1 p.2.1 p.2.2).symm
  have hP₁ : Measurable (potential₁ μ₁ (affine₁ b₁) s) := by
    rw [e₁]
    exact (measurable_parameterizedScalarPotential μ₁ f₁ hf₁ s).comp (by fun_prop)
  have hP₂ : Measurable (potential₂ μ₂ (affine₂ b₂) s) := by
    rw [e₂]
    exact measurable_parameterizedScalarPotential μ₂ b₂ hb₂ s
  have hP₃ : Measurable (potential₃ μ₃ (affine₃ b₃) s) := by
    rw [e₃]
    exact measurable_parameterizedScalarPotential μ₃ b₃ hb₃ s
  have ha₁ : ∀ᵐ p ∂τ.prod μ₁, potential₁ μ₁ (affine₁ b₁) s p < ∞ := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hP₁ measurable_const)).mpr
    filter_upwards [ae_finite_parameterizedScalarPotential_integral μ₁ D₁ hD₁ hμ₁
      f₁ hf₁ u v s hs hs1 ()] with t ht
    apply ae_lt_top (hP₁.comp (show Measurable (fun a : ℝ => (t,a)) by fun_prop))
    simpa only [e₁, Function.comp_apply] using ht.ne
  have ha₂ : ∀ᵐ p ∂τ.prod (μ₁.prod μ₂), potential₂ μ₂ (affine₂ b₂) s p < ∞ := by
    rw [e₂]
    exact ae_finite_parameterizedScalarPotential μ₁ μ₂ D₂ hD₂ hμ₂ b₂ hb₂ u v s hs hs1
  have ha₃ : ∀ᵐ p ∂τ.prod ρ, potential₃ μ₃ (affine₃ b₃) s p < ∞ := by
    rw [e₃]
    exact ae_finite_parameterizedScalarPotential (μ₁.prod μ₂) μ₃ D₃ hD₃ hμ₃
      b₃ hb₃ u v s hs hs1
  have hr₁ : ∀ᵐ p ∂τ.prod ρ, potential₁ μ₁ (affine₁ b₁) s (p.1,p.2.1.1) < ∞ :=
    ae_finite_lift_right τ (μ₁.prod μ₂) μ₃
      (fun p => potential₁ μ₁ (affine₁ b₁) s (p.1,p.2.1)) (hP₁.comp (by fun_prop))
      (ae_finite_lift_right τ μ₁ μ₂ _ hP₁ ha₁)
  have hr₂ : ∀ᵐ p ∂τ.prod ρ, potential₂ μ₂ (affine₂ b₂) s (p.1,p.2.1) < ∞ :=
    ae_finite_lift_right τ (μ₁.prod μ₂) μ₃ _ hP₂ ha₂
  have hac : τ.prod σ ≪ τ.prod ρ :=
    Measure.AbsolutelyContinuous.rfl.prod (Measure.absolutelyContinuous_of_le_smul hdom)
  have hτu : τ univ ≠ 0 := by
    simp [τ, Real.volume_Icc, ENNReal.ofReal_eq_zero, not_le.mpr huv]
  have hσu : σ univ ≠ 0 := fun hz => hσ (Measure.measure_univ_eq_zero.mp hz)
  have hsource : τ.prod σ ≠ 0 := by
    intro hz
    have hh : (τ.prod σ) (univ ×ˢ univ) ≠ 0 := by
      rw [Measure.prod_prod]
      exact mul_ne_zero hτu hσu
    simp [hz] at hh
  exact exists_actual_supported_frostman μ₁ μ₂ μ₃ τ σ hsource D hD hdom
    Measure.restrict_le_self (affine₁ b₁) (affine₂ b₂) (affine₃ b₃)
    hg₁ hg₂ hg₃ s hs hP₁ hP₂ hP₃ (hac.ae_le hr₁) (hac.ae_le hr₂) (hac.ae_le ha₃)
    K hsupport

theorem dimH_eq_four_of_triangular_frostman
    (K : Set E4)
    (hfrost : ∀ s : ℝ, 0 < s → s < 1 →
      ∃ ν : Measure E4, IsProbabilityMeasure ν ∧ ν Kᶜ = 0 ∧
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x r, 0 < r →
          ν (Metric.ball x r) ≤ C * ENNReal.ofReal r ^ (1 + 3 * s)) :
    dimH K = 4 := by
  apply le_antisymm
  · calc
      dimH K ≤ dimH (univ : Set E4) := dimH_mono (subset_univ K)
      _ = 4 := by simp [Real.dimH_univ_eq_finrank, E4]
  · by_contra hnot
    have hlt : dimH K < (4 : ℝ≥0∞) := lt_of_not_ge hnot
    have htop : dimH K ≠ ⊤ := ne_top_of_lt (hlt.trans (show (4 : ℝ≥0∞) < ⊤ by norm_num))
    have hfourtop : (4 : ℝ≥0∞) ≠ ∞ := by norm_num
    have hreal : (dimH K).toReal < 4 := by
      simpa using (ENNReal.toReal_lt_toReal htop hfourtop).mpr hlt
    let s : ℝ := ((dimH K).toReal + 2) / 6
    have hs : 0 < s := by dsimp [s]; positivity
    have hs1 : s < 1 := by dsimp [s]; linarith
    obtain ⟨ν, hν, hsupport, C, hC, hball⟩ := hfrost s hs hs1
    let : IsProbabilityMeasure ν := hν
    let q : NNReal := ⟨1 + 3 * s, by positivity⟩
    have hq : 0 < q := by change (0 : ℝ) < 1+3*s; positivity
    have hdim : (q : ℝ≥0∞) ≤ dimH K :=
      le_dimH_of_hausdorffMeasure_ne_zero
        (hausdorffMeasure_ne_zero_of_ball_growth ν K hsupport C hC q hq
          (fun x r hr _ => hball x r hr))
    have hdimreal := (ENNReal.toReal_le_toReal (by simp) htop).mpr hdim
    change 1 + 3 * s ≤ (dimH K).toReal at hdimreal
    dsimp [s] at hdimreal
    linarith


/-- The actual front of an arbitrary Borel triangular selector has full
four-dimensional Hausdorff dimension under bounded coordinate source densities.
This theorem makes no assertion that a general selector is triangularizable. -/
theorem triangular_borel_front_dimH_eq_four
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (D₁ D₂ D₃ : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (hμ₁ : μ₁ ≤ ENNReal.ofReal D₁ • volume)
    (hμ₂ : μ₂ ≤ ENNReal.ofReal D₂ • volume)
    (hμ₃ : μ₃ ≤ ENNReal.ofReal D₃ • volume)
    (σ : Measure Source) [IsFiniteMeasure σ] (hσ : σ ≠ 0)
    (D : ℝ≥0∞) (hD : D ≠ ∞) (hdom : σ ≤ D • ((μ₁.prod μ₂).prod μ₃))
    (u v : ℝ) (huv : u < v)
    (b₁ : ℝ → ℝ) (b₂ : ℝ × ℝ → ℝ) (b₃ : Source → ℝ)
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) (hb₃ : Measurable b₃)
    (K : Set E4)
    (hsupport : (((volume.restrict (Icc u v)).prod σ).map
      (point (affine₁ b₁) (affine₂ b₂) (affine₃ b₃))) Kᶜ = 0)
    : dimH K = 4 := by
  apply dimH_eq_four_of_triangular_frostman K
  intro s hs hs1
  exact exists_triangular_borel_supported_frostman μ₁ μ₂ μ₃ D₁ D₂ D₃
    hD₁ hD₂ hD₃ hμ₁ hμ₂ hμ₃ σ hσ D hD hdom u v huv
    b₁ b₂ b₃ hb₁ hb₂ hb₃ K hsupport s hs hs1

end StickyKakeya4.TriangularBorelFrontEscape
