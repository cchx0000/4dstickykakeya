import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# From local collision sublevels to finite inverse-distance energy

This is the layer-cake part of the analytical implication used in the original
manuscript's Theorem 6.27 (pp. 33–34).  A positive local sublevel exponent first
forces the zero-distance set to be null.  A power-tail estimate then proves
finiteness of the extended-nonnegative inverse-distance energy at every
strictly smaller positive exponent.

The energy integrand has value infinity at zero distance.  This singularity
is not erased by the totalized real power function: equality with the real
power is used only after the zero-distance set has been proved null.
No geometric residual bound or Hausdorff/slicing conclusion is asserted here.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4

/-- A local positive-power sublevel estimate excludes positive mass at zero. -/
theorem zero_level_measure_eq_zero_of_sublevel_power
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (C q : ℝ) (hq : 0 < q)
    (hsub : ∀ r : ℝ, 0 < r → r < 1 →
      μ {x | f x ≤ r} ≤ ENNReal.ofReal (C * r ^ q)) :
    μ {x | f x = 0} = 0 := by
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r ^ q))
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => ENNReal.ofReal (C * r ^ q)) :=
      ENNReal.continuous_ofReal.comp
        (continuous_const.mul (Real.continuous_rpow_const hq.le))
    have ht := hc.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    simpa [Real.zero_rpow hq.ne'] using ht
  apply le_antisymm ?_ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    (show Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) from
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one))] with r hr0 hr1
  calc
    μ {x | f x = 0} ≤ μ {x | f x ≤ r} := by
      apply measure_mono
      intro x hx
      change f x = 0 at hx
      change f x ≤ r
      rw [hx]
      exact hr0.le
    _ ≤ ENNReal.ofReal (C * r ^ q) := hsub r hr0 hr1

/-- Layer cake and the integrability of a power tail give a finite integral. -/
theorem finite_lintegral_of_power_tail
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (p : ℝ) (hp : 1 < p)
    (htail : ∀ z : ℝ, 1 < z →
      μ {x | z ≤ f x} ≤ C * ENNReal.ofReal (z ^ (-p))) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) < ∞ := by
  rw [lintegral_eq_lintegral_meas_le μ (ae_of_all _ hf0) hf.aemeasurable]
  have hsmall : (∫⁻ z in Ioc (0 : ℝ) 1, μ {x | z ≤ f x}) < ∞ := by
    calc
      (∫⁻ z in Ioc (0 : ℝ) 1, μ {x | z ≤ f x}) ≤
          ∫⁻ _z in Ioc (0 : ℝ) 1, μ univ :=
        lintegral_mono (fun _ => measure_mono (subset_univ _))
      _ = μ univ := by simp [lintegral_const, Real.volume_Ioc]
      _ < ∞ := measure_lt_top μ univ
  have hlarge : (∫⁻ z in Ioi (1 : ℝ), μ {x | z ≤ f x}) < ∞ := by
    have hpint := integrableOn_Ioi_rpow_of_lt (show -p < -1 by linarith)
      (show (0 : ℝ) < 1 by norm_num)
    have hpow0 : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] (fun z : ℝ => z ^ (-p)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      exact Real.rpow_nonneg (by linarith [mem_Ioi.mp hz]) _
    have hpowfin : (∫⁻ z in Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-p))) < ∞ :=
      (hasFiniteIntegral_iff_ofReal hpow0).mp hpint.hasFiniteIntegral
    calc
      (∫⁻ z in Ioi (1 : ℝ), μ {x | z ≤ f x}) ≤
          ∫⁻ z in Ioi (1 : ℝ), C * ENNReal.ofReal (z ^ (-p)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
        exact htail z hz
      _ = C * ∫⁻ z in Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-p)) :=
        lintegral_const_mul' _ _ hC
      _ < ∞ := ENNReal.mul_lt_top hC.lt_top hpowfin
  calc
    (∫⁻ z in Ioi (0 : ℝ), μ {x | z ≤ f x}) ≤
        ∫⁻ z in Ioc (0 : ℝ) 1 ∪ Ioi 1, μ {x | z ≤ f x} :=
      lintegral_mono_set Ioi_subset_Ioc_union_Ioi
    _ ≤ (∫⁻ z in Ioc (0 : ℝ) 1, μ {x | z ≤ f x}) +
        ∫⁻ z in Ioi (1 : ℝ), μ {x | z ≤ f x} := lintegral_union_le _ _ _
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨hsmall, hlarge⟩

/-- A genuine finite inverse-distance energy consequence of a local sublevel
power bound.  The ENNReal integrand has value infinity at distance zero; the
proof first establishes that this zero-distance set has measure zero. -/
theorem finite_inverse_energy_of_sublevel_power
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (C q t : ℝ) (hC : 0 ≤ C) (ht : 0 < t) (htq : t < q)
    (hsub : ∀ r : ℝ, 0 < r → r < 1 →
      μ {x | f x ≤ r} ≤ ENNReal.ofReal (C * r ^ q)) :
    (∫⁻ x, (ENNReal.ofReal (f x)) ^ (-t) ∂μ) < ∞ := by
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
  apply finite_lintegral_of_power_tail μ (fun x => (f x) ^ (-t)) hmeas
    (fun x => Real.rpow_nonneg (hf0 x) _) (ENNReal.ofReal C) ENNReal.ofReal_ne_top
    (q / t) ((lt_div_iff₀ ht).mpr (by simpa using htq))
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

/-- Tonelli for extended-nonnegative inverse-distance energy.  In particular,
zero distances are kept as genuine infinite integrand values when `t>0`. -/
theorem inverse_energy_prod_eq_iterated
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (f : X × Y → ℝ) (hf : Measurable f) (t : ℝ) :
    (∫⁻ p, (ENNReal.ofReal (f p)) ^ (-t) ∂μ.prod ν) =
      ∫⁻ x, (∫⁻ y, (ENNReal.ofReal (f (x, y))) ^ (-t) ∂ν) ∂μ := by
  apply lintegral_prod
  have hm : Measurable (fun p => (ENNReal.ofReal (f p)) ^ (-t)) := by fun_prop
  exact hm.aemeasurable

/-- Finite product energy gives finite fibre energy for almost every outer
parameter, with the exceptional set measured by the actual outer measure. -/
theorem ae_finite_fiber_inverse_energy_of_finite_product_energy
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (f : X × Y → ℝ) (hf : Measurable f) (t : ℝ)
    (henergy : (∫⁻ p, (ENNReal.ofReal (f p)) ^ (-t) ∂μ.prod ν) < ∞) :
    ∀ᵐ x ∂μ, (∫⁻ y, (ENNReal.ofReal (f (x, y))) ^ (-t) ∂ν) < ∞ := by
  have hm : Measurable (fun p => (ENNReal.ofReal (f p)) ^ (-t)) := by fun_prop
  apply ae_lt_top hm.lintegral_prod_right'
  rw [← inverse_energy_prod_eq_iterated μ ν f hf t]
  exact henergy.ne

/-- A local sublevel power bound on the time/source product measure gives
finite average inverse-distance energy at every smaller positive exponent. -/
theorem finite_average_inverse_energy_of_sublevel_power
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : X × Y → ℝ) (hf : Measurable f) (hf0 : ∀ p, 0 ≤ f p)
    (C q t : ℝ) (hC : 0 ≤ C) (ht : 0 < t) (htq : t < q)
    (hsub : ∀ r : ℝ, 0 < r → r < 1 →
      (μ.prod ν) {p | f p ≤ r} ≤ ENNReal.ofReal (C * r ^ q)) :
    (∫⁻ x, (∫⁻ y, (ENNReal.ofReal (f (x, y))) ^ (-t) ∂ν) ∂μ) < ∞ := by
  rw [← inverse_energy_prod_eq_iterated μ ν f hf t]
  exact finite_inverse_energy_of_sublevel_power (μ.prod ν) f hf hf0 C q t hC ht htq hsub

/-- The almost-everywhere finite-energy conclusion in the analytical part
of Theorem 6.27, abstracted over its measurable time/source parameterization. -/
theorem ae_finite_fiber_inverse_energy_of_sublevel_power
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : X × Y → ℝ) (hf : Measurable f) (hf0 : ∀ p, 0 ≤ f p)
    (C q t : ℝ) (hC : 0 ≤ C) (ht : 0 < t) (htq : t < q)
    (hsub : ∀ r : ℝ, 0 < r → r < 1 →
      (μ.prod ν) {p | f p ≤ r} ≤ ENNReal.ofReal (C * r ^ q)) :
    ∀ᵐ x ∂μ, (∫⁻ y, (ENNReal.ofReal (f (x, y))) ^ (-t) ∂ν) < ∞ := by
  apply ae_finite_fiber_inverse_energy_of_finite_product_energy μ ν f hf t
  exact finite_inverse_energy_of_sublevel_power (μ.prod ν) f hf hf0 C q t hC ht htq hsub

end StickyKakeya4
