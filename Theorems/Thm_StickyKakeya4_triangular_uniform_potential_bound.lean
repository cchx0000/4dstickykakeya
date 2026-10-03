import Theorems.Thm_StickyKakeya4_uniform_scalar_projection_energy
import Theorems.Thm_StickyKakeya4_triangular_borel_front_escape
import Theorems.Thm_StickyKakeya4_triangular_potential_escape

/-!
# Uniform native potential bounds for the original triangular source law

The explicit constant is independent of all three measurable intercepts.
All scalar energy input is derived from bounded coordinate densities.
-/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4.TriangularUniformPotentialBound
open ScalarProjection TriangularPotentialEscape TriangularBorelFrontEscape

/-- An unused coordinate contributes precisely the total mass of its measure. -/
theorem lintegral_dummy_coordinate
    {T X Y : Type*} [MeasurableSpace T] [MeasurableSpace X] [MeasurableSpace Y]
    (τ : Measure T) (ν : Measure X) (η : Measure Y)
    [IsFiniteMeasure τ] [IsFiniteMeasure ν] [IsFiniteMeasure η]
    (P : T × X → ℝ≥0∞) (hP : Measurable P) :
    (∫⁻ p, P (p.1, p.2.1) ∂τ.prod (ν.prod η)) =
      (∫⁻ p, P p ∂τ.prod ν) * η univ := by
  rw [lintegral_prod _ (by fun_prop)]
  have hinner (t : T) :
      (∫⁻ p : X × Y, P (t, p.1) ∂ν.prod η) =
        (∫⁻ x, P (t, x) ∂ν) * η univ := by
    have ht : Measurable (fun p : X × Y => P (t, p.1)) :=
      hP.comp (measurable_const.prodMk measurable_fst)
    rw [lintegral_prod _ ht.aemeasurable]
    simp_rw [lintegral_const]
    exact lintegral_mul_const' _ _ (measure_ne_top η univ)
  simp_rw [hinner]
  rw [lintegral_mul_const' _ _ (measure_ne_top η univ)]
  rw [lintegral_prod _ hP.aemeasurable]

/-- Domination in one coordinate transfers to nonnegative product integrals. -/
theorem lintegral_prod_le_of_measure_le_smul
    {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (τ : Measure T) (σ ρ : Measure X) [SFinite ρ]
    (D : ℝ≥0∞) (hD : D ≠ ∞) (hdom : σ ≤ D • ρ)
    (F : T × X → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂τ.prod σ) ≤ D * (∫⁻ p, F p ∂τ.prod ρ) := by
  calc
    _ ≤ ∫⁻ t, ∫⁻ x, F (t, x) ∂σ ∂τ := lintegral_prod_le _
    _ ≤ ∫⁻ t, ∫⁻ x, F (t, x) ∂(D • ρ) ∂τ := by
      apply lintegral_mono
      intro t
      exact lintegral_mono' hdom le_rfl
    _ = ∫⁻ t, D * (∫⁻ x, F (t, x) ∂ρ) ∂τ := by
      simp_rw [lintegral_smul_measure, smul_eq_mul]
    _ = D * (∫⁻ t, ∫⁻ x, F (t, x) ∂ρ ∂τ) :=
      lintegral_const_mul' _ _ hD
    _ = _ := by rw [lintegral_prod _ hF.aemeasurable]

/-- The sum of the three native potentials on the original source coordinates. -/
def nativePotentialSum (μ₁ μ₂ μ₃ : Measure ℝ)
    (b₁ : ℝ → ℝ) (b₂ : ℝ × ℝ → ℝ) (b₃ : Source → ℝ) (s : ℝ)
    (p : ℝ × Source) : ℝ≥0∞ :=
  potential₁ μ₁ (affine₁ b₁) s (p.1,p.2.1.1) +
    potential₂ μ₂ (affine₂ b₂) s (p.1,p.2.1) +
    potential₃ μ₃ (affine₃ b₃) s p

/-- The source-dependent constant for the original law; it is independent of the intercepts. -/
def uniformTriangularPotentialBound (μ₁ μ₂ μ₃ : Measure ℝ)
    (D : ℝ≥0∞) (u v s : ℝ) : ℝ≥0∞ :=
  D * (uniformScalarEnergyBound μ₁ u v s * μ₂ univ * μ₃ univ +
    uniformScalarEnergyBound μ₂ u v s * μ₁ univ * μ₃ univ +
    uniformScalarEnergyBound μ₃ u v s * μ₁ univ * μ₂ univ)

theorem uniformTriangularPotentialBound_lt_top
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (D : ℝ≥0∞) (hD : D ≠ ∞) (u v s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    uniformTriangularPotentialBound μ₁ μ₂ μ₃ D u v s < ∞ := by
  apply ENNReal.mul_lt_top hD.lt_top
  apply ENNReal.add_lt_top.mpr
  constructor
  · apply ENNReal.add_lt_top.mpr
    constructor
    · exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (uniformScalarEnergyBound_lt_top μ₁ u v s hs hs1)
          (measure_lt_top μ₂ univ)) (measure_lt_top μ₃ univ)
    · exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (uniformScalarEnergyBound_lt_top μ₂ u v s hs hs1)
          (measure_lt_top μ₁ univ)) (measure_lt_top μ₃ univ)
  · exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (uniformScalarEnergyBound_lt_top μ₃ u v s hs hs1)
        (measure_lt_top μ₁ univ)) (measure_lt_top μ₂ univ)

theorem potential₁_affine_eq_parameterized
    (μ : Measure ℝ) (b : ℝ → ℝ) (hb : Measurable b) (s : ℝ) :
    potential₁ μ (affine₁ b) s = fun p =>
      parameterizedScalarPotential μ (fun q : Unit × ℝ => b q.2) s (p.1,((),p.2)) := by
  funext p
  exact (parameterizedScalarPotential_eq_map_potential μ (fun q : Unit × ℝ => b q.2)
    (hb.comp measurable_snd) s p.1 () p.2).symm

theorem potential₂_affine_eq_parameterized
    (μ : Measure ℝ) (b : ℝ × ℝ → ℝ) (hb : Measurable b) (s : ℝ) :
    potential₂ μ (affine₂ b) s = parameterizedScalarPotential μ b s := by
  funext p
  exact (parameterizedScalarPotential_eq_map_potential μ b hb s p.1 p.2.1 p.2.2).symm

theorem potential₃_affine_eq_parameterized
    (μ : Measure ℝ) (b : Source → ℝ) (hb : Measurable b) (s : ℝ) :
    potential₃ μ (affine₃ b) s = parameterizedScalarPotential μ b s := by
  funext p
  exact (parameterizedScalarPotential_eq_map_potential μ b hb s p.1 p.2.1 p.2.2).symm

theorem measurable_potential₁_affine
    (μ : Measure ℝ) [SFinite μ] (b : ℝ → ℝ) (hb : Measurable b) (s : ℝ) :
    Measurable (potential₁ μ (affine₁ b) s) := by
  rw [potential₁_affine_eq_parameterized μ b hb s]
  exact (measurable_parameterizedScalarPotential μ (fun q : Unit × ℝ => b q.2)
    (hb.comp measurable_snd) s).comp (by fun_prop)

theorem measurable_potential₂_affine
    (μ : Measure ℝ) [SFinite μ] (b : ℝ × ℝ → ℝ) (hb : Measurable b) (s : ℝ) :
    Measurable (potential₂ μ (affine₂ b) s) := by
  rw [potential₂_affine_eq_parameterized μ b hb s]
  exact measurable_parameterizedScalarPotential μ b hb s

theorem measurable_potential₃_affine
    (μ : Measure ℝ) [SFinite μ] (b : Source → ℝ) (hb : Measurable b) (s : ℝ) :
    Measurable (potential₃ μ (affine₃ b) s) := by
  rw [potential₃_affine_eq_parameterized μ b hb s]
  exact measurable_parameterizedScalarPotential μ b hb s

theorem measurable_nativePotentialSum
    (μ₁ μ₂ μ₃ : Measure ℝ) [SFinite μ₁] [SFinite μ₂] [SFinite μ₃]
    (b₁ : ℝ → ℝ) (b₂ : ℝ × ℝ → ℝ) (b₃ : Source → ℝ)
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) (hb₃ : Measurable b₃) (s : ℝ) :
    Measurable (nativePotentialSum μ₁ μ₂ μ₃ b₁ b₂ b₃ s) := by
  exact (((measurable_potential₁_affine μ₁ b₁ hb₁ s).comp (by fun_prop)).add
    ((measurable_potential₂_affine μ₂ b₂ hb₂ s).comp (by fun_prop))).add
      (measurable_potential₃_affine μ₃ b₃ hb₃ s)

/-- Uniform bound for the first native coordinate potential before dummy coordinates are added. -/
theorem average_potential₁_affine_le
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume) (b : ℝ → ℝ) (hb : Measurable b)
    (u v s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (∫⁻ p, potential₁ μ (affine₁ b) s p ∂(volume.restrict (Icc u v)).prod μ) ≤
      uniformScalarEnergyBound μ u v s := by
  let f : Unit × ℝ → ℝ := fun p => b p.2
  have hf : Measurable f := hb.comp measurable_snd
  calc
    _ = ∫⁻ t in Icc u v, ∫⁻ a, potential₁ μ (affine₁ b) s (t,a) ∂μ :=
      lintegral_prod _ (measurable_potential₁_affine μ b hb s).aemeasurable
    _ = ∫⁻ t in Icc u v, ∫⁻ p : ℝ × ℝ,
        (ENNReal.ofReal |(b p.1-b p.2)+t*(p.1-p.2)|)^(-s) ∂μ.prod μ := by
      apply lintegral_congr
      intro t
      rw [potential₁_affine_eq_parameterized μ b hb s]
      exact parameterizedScalarPotential_integral_eq_pair_energy μ f hf s t ()
    _ = ∫⁻ p : ℝ × (ℝ × ℝ),
        (ENNReal.ofReal |(b p.2.1-b p.2.2)+p.1*(p.2.1-p.2.2)|)^(-s)
          ∂(volume.restrict (Icc u v)).prod (μ.prod μ) :=
      (inverse_energy_prod_eq_iterated (volume.restrict (Icc u v)) (μ.prod μ)
        (fun p : ℝ × (ℝ × ℝ) => |(b p.2.1-b p.2.2)+p.1*(p.2.1-p.2.2)|)
        (by fun_prop) s).symm
    _ ≤ _ := average_scalar_projection_pair_energy_le μ D hD hμ b hb u v s hs hs1

/-- The original reference product integrates the three native potentials with
exactly the masses of their unused coordinates. -/
theorem reference_nativePotentialSum_integral_le
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (D₁ D₂ D₃ : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (hμ₁ : μ₁ ≤ ENNReal.ofReal D₁ • volume)
    (hμ₂ : μ₂ ≤ ENNReal.ofReal D₂ • volume)
    (hμ₃ : μ₃ ≤ ENNReal.ofReal D₃ • volume)
    (b₁ : ℝ → ℝ) (b₂ : ℝ × ℝ → ℝ) (b₃ : Source → ℝ)
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) (hb₃ : Measurable b₃)
    (u v s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (∫⁻ p, nativePotentialSum μ₁ μ₂ μ₃ b₁ b₂ b₃ s p
      ∂(volume.restrict (Icc u v)).prod ((μ₁.prod μ₂).prod μ₃)) ≤
      uniformScalarEnergyBound μ₁ u v s * μ₂ univ * μ₃ univ +
      uniformScalarEnergyBound μ₂ u v s * μ₁ univ * μ₃ univ +
      uniformScalarEnergyBound μ₃ u v s * μ₁ univ * μ₂ univ := by
  let τ : Measure ℝ := volume.restrict (Icc u v)
  let ρ : Measure Source := (μ₁.prod μ₂).prod μ₃
  let P₁ : ℝ × Source → ℝ≥0∞ := fun p => potential₁ μ₁ (affine₁ b₁) s (p.1,p.2.1.1)
  let P₂ : ℝ × Source → ℝ≥0∞ := fun p => potential₂ μ₂ (affine₂ b₂) s (p.1,p.2.1)
  let P₃ : ℝ × Source → ℝ≥0∞ := potential₃ μ₃ (affine₃ b₃) s
  have hP₁ : Measurable P₁ := (measurable_potential₁_affine μ₁ b₁ hb₁ s).comp (by fun_prop)
  have hP₂ : Measurable P₂ := (measurable_potential₂_affine μ₂ b₂ hb₂ s).comp (by fun_prop)
  have hI₁ : (∫⁻ p, P₁ p ∂τ.prod ρ) ≤
      uniformScalarEnergyBound μ₁ u v s * μ₂ univ * μ₃ univ := by
    calc
      _ = (∫⁻ p, potential₁ μ₁ (affine₁ b₁) s (p.1,p.2.1)
          ∂τ.prod (μ₁.prod μ₂)) * μ₃ univ :=
        lintegral_dummy_coordinate τ (μ₁.prod μ₂) μ₃ _
          ((measurable_potential₁_affine μ₁ b₁ hb₁ s).comp (by fun_prop))
      _ = ((∫⁻ p, potential₁ μ₁ (affine₁ b₁) s p ∂τ.prod μ₁) * μ₂ univ) * μ₃ univ := by
        rw [lintegral_dummy_coordinate τ μ₁ μ₂ _ (measurable_potential₁_affine μ₁ b₁ hb₁ s)]
      _ ≤ _ := mul_le_mul_left
        (mul_le_mul_left (average_potential₁_affine_le μ₁ D₁ hD₁ hμ₁ b₁ hb₁ u v s hs hs1)
          (μ₂ univ)) (μ₃ univ)
  have hI₂ : (∫⁻ p, P₂ p ∂τ.prod ρ) ≤
      uniformScalarEnergyBound μ₂ u v s * μ₁ univ * μ₃ univ := by
    calc
      _ = (∫⁻ p, potential₂ μ₂ (affine₂ b₂) s p ∂τ.prod (μ₁.prod μ₂)) * μ₃ univ :=
        lintegral_dummy_coordinate τ (μ₁.prod μ₂) μ₃ _ (measurable_potential₂_affine μ₂ b₂ hb₂ s)
      _ ≤ _ := by
        apply mul_le_mul_left
        rw [potential₂_affine_eq_parameterized μ₂ b₂ hb₂ s]
        exact average_parameterizedScalarPotential_le μ₁ μ₂ D₂ hD₂ hμ₂ b₂ hb₂ u v s hs hs1
  have hI₃ : (∫⁻ p, P₃ p ∂τ.prod ρ) ≤
      uniformScalarEnergyBound μ₃ u v s * μ₁ univ * μ₂ univ := by
    dsimp only [P₃]
    rw [potential₃_affine_eq_parameterized μ₃ b₃ hb₃ s]
    have hmass : (μ₁.prod μ₂) univ = μ₁ univ * μ₂ univ := by
      rw [← univ_prod_univ, Measure.prod_prod]
    simpa only [hmass, mul_assoc] using
      average_parameterizedScalarPotential_le (μ₁.prod μ₂) μ₃ D₃ hD₃ hμ₃ b₃ hb₃ u v s hs hs1
  change (∫⁻ p, P₁ p + P₂ p + P₃ p ∂τ.prod ρ) ≤ _
  rw [lintegral_add_left (show Measurable (fun p => P₁ p + P₂ p) from hP₁.add hP₂),
    lintegral_add_left hP₁]
  exact add_le_add (add_le_add hI₁ hI₂) hI₃

/-- Quantitative bound for the original actual triangular source law. Every
energy input is derived from the three coordinate density assumptions. -/
theorem actual_nativePotentialSum_integral_le
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (D₁ D₂ D₃ : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (hμ₁ : μ₁ ≤ ENNReal.ofReal D₁ • volume)
    (hμ₂ : μ₂ ≤ ENNReal.ofReal D₂ • volume)
    (hμ₃ : μ₃ ≤ ENNReal.ofReal D₃ • volume)
    (σ : Measure Source) [IsFiniteMeasure σ]
    (D : ℝ≥0∞) (hD : D ≠ ∞) (hdom : σ ≤ D • ((μ₁.prod μ₂).prod μ₃))
    (b₁ : ℝ → ℝ) (b₂ : ℝ × ℝ → ℝ) (b₃ : Source → ℝ)
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) (hb₃ : Measurable b₃)
    (u v s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (∫⁻ p, nativePotentialSum μ₁ μ₂ μ₃ b₁ b₂ b₃ s p
      ∂(volume.restrict (Icc u v)).prod σ) ≤
      uniformTriangularPotentialBound μ₁ μ₂ μ₃ D u v s := by
  refine (lintegral_prod_le_of_measure_le_smul (volume.restrict (Icc u v))
    σ ((μ₁.prod μ₂).prod μ₃) D hD hdom _
    (measurable_nativePotentialSum μ₁ μ₂ μ₃ b₁ b₂ b₃ hb₁ hb₂ hb₃ s)).trans ?_
  exact mul_le_mul_right
    (reference_nativePotentialSum_integral_le μ₁ μ₂ μ₃ D₁ D₂ D₃ hD₁ hD₂ hD₃
      hμ₁ hμ₂ hμ₃ b₁ b₂ b₃ hb₁ hb₂ hb₃ u v s hs hs1) D

end StickyKakeya4.TriangularUniformPotentialBound
