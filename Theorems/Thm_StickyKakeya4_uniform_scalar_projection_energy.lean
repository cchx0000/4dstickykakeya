import Theorems.Thm_StickyKakeya4_scalar_borel_projection_energy
import Theorems.Thm_StickyKakeya4_parameterized_scalar_potential

/-!
# Uniform scalar projection energy bounds

The constants below depend only on the original source measure, time interval,
and exponent. They do not depend on the measurable intercept function.
-/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4.ScalarProjection

/-- The explicit one-dimensional power-tail integral in the layer-cake bound. -/
def powerTailIntegral (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-p))

/-- The power-tail envelope is finite for exponents above one. -/
theorem powerTailIntegral_lt_top (p : ℝ) (hp : 1 < p) : powerTailIntegral p < ∞ := by
  have hpint := integrableOn_Ioi_rpow_of_lt (show -p < -1 by linarith)
    (show (0 : ℝ) < 1 by norm_num)
  have hpow0 : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] (fun z : ℝ => z ^ (-p)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact Real.rpow_nonneg (by linarith [mem_Ioi.mp hz]) _
  exact (hasFiniteIntegral_iff_ofReal hpow0).mp hpint.hasFiniteIntegral

/-- Quantitative layer cake; the constant is retained in the conclusion. -/
theorem lintegral_le_of_power_tail
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (p : ℝ)
    (htail : ∀ z : ℝ, 1 < z →
      μ {x | z ≤ f x} ≤ C * ENNReal.ofReal (z ^ (-p))) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ μ univ + C * powerTailIntegral p := by
  rw [lintegral_eq_lintegral_meas_le μ (ae_of_all _ hf0) hf.aemeasurable]
  have hsmall : (∫⁻ z in Ioc (0 : ℝ) 1, μ {x | z ≤ f x}) ≤ μ univ := by
    calc
      _ ≤ ∫⁻ _z in Ioc (0 : ℝ) 1, μ univ :=
        lintegral_mono (fun _ => measure_mono (subset_univ _))
      _ = μ univ := by simp [lintegral_const, Real.volume_Ioc]
  have hlarge : (∫⁻ z in Ioi (1 : ℝ), μ {x | z ≤ f x}) ≤ C * powerTailIntegral p := by
    calc
      _ ≤ ∫⁻ z in Ioi (1 : ℝ), C * ENNReal.ofReal (z ^ (-p)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
        exact htail z hz
      _ = _ := lintegral_const_mul' _ _ hC
  calc
    _ ≤ ∫⁻ z in Ioc (0 : ℝ) 1 ∪ Ioi 1, μ {x | z ≤ f x} :=
      lintegral_mono_set Ioi_subset_Ioc_union_Ioi
    _ ≤ (∫⁻ z in Ioc (0 : ℝ) 1, μ {x | z ≤ f x}) +
        ∫⁻ z in Ioi (1 : ℝ), μ {x | z ≤ f x} := lintegral_union_le _ _ _
    _ ≤ _ := add_le_add hsmall hlarge

/-- Quantitative inverse-energy estimate with the true infinite diagonal kernel. -/
theorem inverse_energy_le_of_sublevel_power
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (C q t : ℝ) (hC : 0 ≤ C) (ht : 0 < t) (htq : t < q)
    (hsub : ∀ r : ℝ, 0 < r → r < 1 →
      μ {x | f x ≤ r} ≤ ENNReal.ofReal (C * r ^ q)) :
    (∫⁻ x, (ENNReal.ofReal (f x)) ^ (-t) ∂μ) ≤
      μ univ + ENNReal.ofReal C * powerTailIntegral (q / t) := by
  have hq : 0 < q := ht.trans htq
  have hzero := zero_level_measure_eq_zero_of_sublevel_power μ f C q hq hsub
  have hfpos : ∀ᵐ x ∂μ, 0 < f x := by
    have hfne : ∀ᵐ x ∂μ, f x ≠ 0 := by
      simpa only [ae_iff, not_not] using hzero
    filter_upwards [hfne] with x hx
    exact (hf0 x).lt_of_ne hx.symm
  have heq : (fun x => (ENNReal.ofReal (f x)) ^ (-t)) =ᵐ[μ]
      (fun x => ENNReal.ofReal ((f x) ^ (-t))) := by
    filter_upwards [hfpos] with x hx
    exact ENNReal.ofReal_rpow_of_pos hx
  rw [lintegral_congr_ae heq]
  have hmeas : Measurable (fun x => (f x) ^ (-t)) := by fun_prop
  apply lintegral_le_of_power_tail μ (fun x => (f x) ^ (-t)) hmeas
    (fun x => Real.rpow_nonneg (hf0 x) _) (ENNReal.ofReal C) ENNReal.ofReal_ne_top (q / t)
  intro z hz
  have hz0 : 0 < z := zero_lt_one.trans hz
  let r : ℝ := z ^ ((-t)⁻¹)
  have hr0 : 0 < r := Real.rpow_pos_of_pos hz0 _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hz (inv_lt_zero.mpr (neg_lt_zero.mpr ht))
  calc
    μ {x | z ≤ (f x) ^ (-t)} ≤ μ {x | f x ≤ r} := by
      apply measure_mono
      intro x hx
      change z ≤ (f x) ^ (-t) at hx
      change f x ≤ r
      have hfx : 0 < f x := by
        apply (hf0 x).lt_of_ne
        intro he
        have he' : f x = 0 := he.symm
        rw [he', Real.zero_rpow (by linarith : -t ≠ 0)] at hx
        linarith
      exact (Real.le_rpow_inv_iff_of_neg hfx hz0 (by linarith : -t < 0)).mpr hx
    _ ≤ ENNReal.ofReal (C * r ^ q) := hsub r hr0 hr1
    _ = ENNReal.ofReal C * ENNReal.ofReal (z ^ (-(q / t))) := by
      have hpower : r ^ q = z ^ (-(q / t)) := by
        dsimp [r]
        rw [← Real.rpow_mul hz0.le]
        congr 1
        simp only [inv_neg, div_eq_mul_inv]
        ring
      rw [ENNReal.ofReal_mul hC, hpower]

/-- Fixed-source energy appearing in the uniform bound. -/
def sourcePairEnergy (μ : Measure ℝ) (q : ℝ) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, (ENNReal.ofReal |p.1-p.2|)^(-q) ∂μ.prod μ

/-- An explicit finite envelope independent of every measurable intercept. -/
def uniformScalarEnergyBound (μ : Measure ℝ) (l h s : ℝ) : ℝ≥0∞ :=
  ((volume.restrict (Icc l h)).prod (μ.prod μ)) univ +
    ENNReal.ofReal ((|h-l|+2)*(sourcePairEnergy μ ((s+1)/2)).toReal) *
      powerTailIntegral (((s+1)/2) / s)

/-- The envelope is finite; bounded source density is used in its applicability theorem. -/
theorem uniformScalarEnergyBound_lt_top
    (μ : Measure ℝ) [IsFiniteMeasure μ] (l h s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    uniformScalarEnergyBound μ l h s < ∞ := by
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact measure_lt_top _ _
  · apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    apply powerTailIntegral_lt_top
    apply (lt_div_iff₀ hs).mpr
    linarith

/-- Uniform averaged energy for the original source-pair law, with no assumption on
intercept regularity beyond measurability. All source-energy inputs are discharged. -/
theorem average_scalar_projection_pair_energy_le
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume) (f : ℝ → ℝ) (hf : Measurable f)
    (l h s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (∫⁻ p : ℝ × (ℝ × ℝ),
      (ENNReal.ofReal |(f p.2.1-f p.2.2)+p.1*(p.2.1-p.2.2)|)^(-s)
        ∂(volume.restrict (Icc l h)).prod (μ.prod μ)) ≤
      uniformScalarEnergyBound μ l h s := by
  let q : ℝ := (s+1)/2
  have hsq : s < q := by dsimp [q]; linarith
  have hq : 0 < q := hs.trans hsq
  have hq1 : q < 1 := by dsimp [q]; linarith
  let E := sourcePairEnergy μ q
  have hE : E < ∞ := finite_source_pair_energy μ D hD hμ q hq hq1
  apply inverse_energy_le_of_sublevel_power
    ((volume.restrict (Icc l h)).prod (μ.prod μ))
    (fun p : ℝ × (ℝ × ℝ) => |(f p.2.1-f p.2.2)+p.1*(p.2.1-p.2.2)|)
    (by fun_prop) (fun _ => abs_nonneg _) ((|h-l|+2)*E.toReal) q s
    (by positivity) hs hsq
  intro r hr _
  calc
    _ ≤ ENNReal.ofReal ((|h-l|+2)*r^q) * E :=
      averaged_collision_le_source_energy μ f hf l h r q hr hq hq1
        (source_pair_diagonal_null μ D hD hμ)
    _ = ENNReal.ofReal (((|h-l|+2)*E.toReal)*r^q) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hE.ne]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- Uniform averaged energy of the full actual projected measures. -/
theorem average_scalar_projection_energy_le
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume) (f : ℝ → ℝ) (hf : Measurable f)
    (l h s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (∫⁻ t in Icc l h, (∫⁻ y, (∫⁻ z, edist y z ^ (-s)
      ∂μ.map (fun x => f x+t*x)) ∂μ.map (fun x => f x+t*x))) ≤
      uniformScalarEnergyBound μ l h s := by
  calc
    _ = ∫⁻ t in Icc l h, (∫⁻ p : ℝ × ℝ,
        (ENNReal.ofReal |(f p.1-f p.2)+t*(p.1-p.2)|)^(-s) ∂μ.prod μ) :=
      lintegral_congr (fun t => scalar_map_energy_eq μ f hf t s)
    _ = ∫⁻ p : ℝ × (ℝ × ℝ),
        (ENNReal.ofReal |(f p.2.1-f p.2.2)+p.1*(p.2.1-p.2.2)|)^(-s)
          ∂(volume.restrict (Icc l h)).prod (μ.prod μ) :=
      (inverse_energy_prod_eq_iterated (volume.restrict (Icc l h)) (μ.prod μ)
        (fun p : ℝ × (ℝ × ℝ) => |(f p.2.1-f p.2.2)+p.1*(p.2.1-p.2.2)|)
        (by fun_prop) s).symm
    _ ≤ _ := average_scalar_projection_pair_energy_le μ D hD hμ f hf l h s hs hs1

/-- A single finite constant bounds every measurable intercept function. -/
theorem exists_uniform_average_scalar_projection_energy_bound
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume)
    (l h s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : ℝ → ℝ, Measurable f →
      (∫⁻ t in Icc l h, (∫⁻ y, (∫⁻ z, edist y z ^ (-s)
        ∂μ.map (fun x => f x+t*x)) ∂μ.map (fun x => f x+t*x))) ≤ C := by
  exact ⟨uniformScalarEnergyBound μ l h s,
    (uniformScalarEnergyBound_lt_top μ l h s hs hs1).ne,
    fun f hf => average_scalar_projection_energy_le μ D hD hμ f hf l h s hs hs1⟩

variable {Z : Type*} [MeasurableSpace Z]

/-- Tonelli writes the native time–parameter–source integral as the integral
of each parameter's integrated source potential. -/
theorem parameterizedScalarPotential_integral_eq_parameter_integral
    (ζ : Measure Z) [IsFiniteMeasure ζ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (f : Z × ℝ → ℝ) (hf : Measurable f)
    (l h s : ℝ) :
    (∫⁻ p, parameterizedScalarPotential μ f s p
      ∂(volume.restrict (Icc l h)).prod (ζ.prod μ)) =
      ∫⁻ z, (∫⁻ t in Icc l h, ∫⁻ a,
        parameterizedScalarPotential μ f s (t,(z,a)) ∂μ) ∂ζ := by
  have hP := measurable_parameterizedScalarPotential μ f hf s
  let Q : ℝ × Z → ℝ≥0∞ := fun p =>
    ∫⁻ a, parameterizedScalarPotential μ f s (p.1,(p.2,a)) ∂μ
  have hQ : Measurable Q := by
    have hm : Measurable (fun p : (ℝ × Z) × ℝ =>
        parameterizedScalarPotential μ f s (p.1.1,(p.1.2,p.2))) :=
      hP.comp (by fun_prop)
    exact hm.lintegral_prod_right'
  calc
    _ = ∫⁻ t in Icc l h, ∫⁻ za,
        parameterizedScalarPotential μ f s (t,za) ∂ζ.prod μ := lintegral_prod _ hP.aemeasurable
    _ = ∫⁻ t in Icc l h, ∫⁻ z, ∫⁻ a,
        parameterizedScalarPotential μ f s (t,(z,a)) ∂μ ∂ζ := by
      apply lintegral_congr
      intro t
      exact lintegral_prod _ ((hP.comp (by fun_prop)).aemeasurable)
    _ = _ := lintegral_lintegral_swap hQ.aemeasurable

/-- A uniform bound on each parameter yields an integral bound under the
literal product of the time, parameter and source measures. -/
theorem parameterizedScalarPotential_integral_le_of_uniform_bound
    (ζ : Measure Z) [IsFiniteMeasure ζ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (f : Z × ℝ → ℝ) (hf : Measurable f)
    (l h s : ℝ) (C : ℝ≥0∞)
    (hC : ∀ z, (∫⁻ t in Icc l h, ∫⁻ a,
      parameterizedScalarPotential μ f s (t,(z,a)) ∂μ) ≤ C) :
    (∫⁻ p, parameterizedScalarPotential μ f s p
      ∂(volume.restrict (Icc l h)).prod (ζ.prod μ)) ≤ C * ζ univ := by
  rw [parameterizedScalarPotential_integral_eq_parameter_integral ζ μ f hf l h s]
  calc
    _ ≤ ∫⁻ _z, C ∂ζ := lintegral_mono hC
    _ = _ := lintegral_const C

/-- The same fixed envelope controls the original potential law after integration
against any finite prefix measure. It is independent of both the intercept and prefix. -/
theorem average_parameterizedScalarPotential_le
    (ζ : Measure Z) [IsFiniteMeasure ζ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume)
    (f : Z × ℝ → ℝ) (hf : Measurable f)
    (l h s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (∫⁻ p, parameterizedScalarPotential μ f s p
      ∂(volume.restrict (Icc l h)).prod (ζ.prod μ)) ≤
      uniformScalarEnergyBound μ l h s * ζ univ := by
  apply parameterizedScalarPotential_integral_le_of_uniform_bound ζ μ f hf l h s
  intro z
  have hz : Measurable (fun a => f (z,a)) := by fun_prop
  calc
    _ = ∫⁻ t in Icc l h, ∫⁻ p : ℝ × ℝ,
        (ENNReal.ofReal |(f (z,p.1)-f (z,p.2))+t*(p.1-p.2)|)^(-s) ∂μ.prod μ :=
      lintegral_congr (fun t =>
        parameterizedScalarPotential_integral_eq_pair_energy μ f hf s t z)
    _ = ∫⁻ p : ℝ × (ℝ × ℝ),
        (ENNReal.ofReal |(f (z,p.2.1)-f (z,p.2.2))+p.1*(p.2.1-p.2.2)|)^(-s)
          ∂(volume.restrict (Icc l h)).prod (μ.prod μ) :=
      (inverse_energy_prod_eq_iterated (volume.restrict (Icc l h)) (μ.prod μ)
        (fun p : ℝ × (ℝ × ℝ) =>
          |(f (z,p.2.1)-f (z,p.2.2))+p.1*(p.2.1-p.2.2)|)
        (by fun_prop) s).symm
    _ ≤ _ := average_scalar_projection_pair_energy_le μ D hD hμ
      (fun a => f (z,a)) hz l h s hs hs1

/-- The full native time–prefix–source potential is integrable. -/
theorem finite_average_parameterizedScalarPotential
    (ζ : Measure Z) [IsFiniteMeasure ζ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume)
    (f : Z × ℝ → ℝ) (hf : Measurable f)
    (l h s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (∫⁻ p, parameterizedScalarPotential μ f s p
      ∂(volume.restrict (Icc l h)).prod (ζ.prod μ)) < ∞ := by
  exact (average_parameterizedScalarPotential_le ζ μ D hD hμ f hf l h s hs hs1).trans_lt
    (ENNReal.mul_lt_top (uniformScalarEnergyBound_lt_top μ l h s hs hs1)
      (measure_lt_top ζ univ))

/-- Uniform Markov bound on the bad-potential region of the original product law. -/
theorem parameterizedScalarPotential_superlevel_le
    (ζ : Measure Z) [IsFiniteMeasure ζ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume)
    (f : Z × ℝ → ℝ) (hf : Measurable f)
    (l h s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (N : ℝ≥0∞) (hN : N ≠ 0) (hNtop : N ≠ ∞) :
    ((volume.restrict (Icc l h)).prod (ζ.prod μ))
      {p | N ≤ parameterizedScalarPotential μ f s p} ≤
      (uniformScalarEnergyBound μ l h s * ζ univ) / N := by
  exact (meas_ge_le_lintegral_div
    (measurable_parameterizedScalarPotential μ f hf s).aemeasurable hN hNtop).trans
    (ENNReal.div_le_div_right
      (average_parameterizedScalarPotential_le ζ μ D hD hμ f hf l h s hs hs1) N)

/-- A single positive integer cutoff makes the original bad-potential mass small
for every jointly measurable intercept family. The cutoff is independent of the family. -/
theorem exists_uniform_parameterizedScalarPotential_cutoff
    (ζ : Measure Z) [IsFiniteMeasure ζ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume)
    (l h s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ f : Z × ℝ → ℝ, Measurable f →
      ((volume.restrict (Icc l h)).prod (ζ.prod μ))
        {p | (N : ℝ≥0∞) ≤ parameterizedScalarPotential μ f s p} < ε := by
  have hC : uniformScalarEnergyBound μ l h s * ζ univ ≠ ∞ :=
    (ENNReal.mul_lt_top (uniformScalarEnergyBound_lt_top μ l h s hs hs1)
      (measure_lt_top ζ univ)).ne
  obtain ⟨N, hN, hsmall⟩ := ENNReal.exists_nat_pos_inv_mul_lt hC hε
  refine ⟨N, hN, ?_⟩
  intro f hf
  apply (parameterizedScalarPotential_superlevel_le ζ μ D hD hμ f hf l h s hs hs1
    N (by exact_mod_cast hN.ne') (by simp)).trans_lt
  simpa only [ENNReal.div_eq_inv_mul] using hsmall

end StickyKakeya4.ScalarProjection
