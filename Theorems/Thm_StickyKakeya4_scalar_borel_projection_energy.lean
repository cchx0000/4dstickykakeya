import Theorems.Thm_StickyKakeya4_residual_energy
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Scalar Borel projection escape from bounded source density

For a finite measure on the real line dominated by a finite multiple of
Lebesgue measure and any measurable intercept f, the full pushforward under
x ↦ f(x) + t*x has finite s-energy for almost every actual time t, for every
fixed 0 < s < 1. Its s-energy averaged over any bounded time interval is finite.
All energy hypotheses are derived. The ENNReal kernel remains infinite on
the diagonal, which is proved null rather than totalized away. No regularity
of f beyond measurability and no bounded source support are required.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4.ScalarProjection

/-- Absolute continuity with bounded density gives the exact linear source-pair
sublevel estimate. No bounded-support assumption is needed. -/
theorem source_pair_sublevel_le
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume) (r : ℝ) (hr : 0 ≤ r) :
    (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2| ≤ r} ≤
      ENNReal.ofReal ((2 * D * (μ univ).toReal) * r) := by
  have hm : MeasurableSet {p : ℝ × ℝ | |p.1 - p.2| ≤ r} := by
    exact measurableSet_le (by fun_prop) measurable_const
  rw [Measure.prod_apply hm]
  calc
    _ ≤ ∫⁻ _x, ENNReal.ofReal (2 * D * r) ∂μ := by
      apply lintegral_mono
      intro x
      have he : {y : ℝ | |x - y| ≤ r} = Icc (x-r) (x+r) := by
        ext y
        simp only [mem_ofPred_eq, abs_le, mem_Icc]
        constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
      change μ {y : ℝ | |x-y| ≤ r} ≤ _
      rw [he]
      calc
        _ ≤ (ENNReal.ofReal D • volume) (Icc (x-r) (x+r)) := hμ _
        _ = ENNReal.ofReal (2 * D * r) := by
          rw [Measure.smul_apply, smul_eq_mul, Real.volume_Icc]
          rw [← ENNReal.ofReal_mul hD]
          congr 1
          ring
    _ = _ := by
      rw [lintegral_const]
      conv_lhs => rw [← ENNReal.ofReal_toReal (measure_ne_top μ univ)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- The singular source diagonal is genuinely null. -/
theorem source_pair_diagonal_null
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume) :
    (μ.prod μ) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  have h := zero_level_measure_eq_zero_of_sublevel_power (μ.prod μ)
    (fun p : ℝ × ℝ => |p.1-p.2|) (2*D*(μ univ).toReal) 1 zero_lt_one
    (fun r hr _ => by simpa using source_pair_sublevel_le μ D hD hμ r hr.le)
  simpa only [abs_eq_zero, sub_eq_zero] using h

/-- Every source energy below dimension one is finite, including the true
infinite value of the kernel on the diagonal. -/
theorem finite_source_pair_energy
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume) (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal |p.1-p.2|)^(-q) ∂μ.prod μ) < ∞ := by
  apply finite_inverse_energy_of_sublevel_power (μ.prod μ)
    (fun p : ℝ × ℝ => |p.1-p.2|) (by fun_prop) (fun _ => abs_nonneg _)
    (2*D*(μ univ).toReal) 1 q (by positivity) hq hq1
  intro r hr _
  simpa using source_pair_sublevel_le μ D hD hμ r hr.le

/-- An affine scalar time fibre has length at most twice radius divided by
its nonzero slope. -/
theorem time_fiber_volume_le
    (u v l h r : ℝ) (hv : v ≠ 0) (_hr : 0 ≤ r) :
    (volume.restrict (Icc l h)) {t : ℝ | |u+t*v| ≤ r} ≤
      ENNReal.ofReal (2*r/|v|) := by
  have hav : 0 < |v| := abs_pos.mpr hv
  calc
    _ ≤ volume {t : ℝ | |u+t*v| ≤ r} := Measure.restrict_le_self _
    _ ≤ volume (Icc (-u/v-r/|v|) (-u/v+r/|v|)) := by
      apply measure_mono
      intro t ht
      have he : t - (-u/v) = (u+t*v)/v := by field_simp; ring
      have ha : |t-(-u/v)| ≤ r/|v| := by
        rw [he, abs_div]
        exact div_le_div_of_nonneg_right ht hav.le
      obtain ⟨ha, hb⟩ := abs_le.mp ha
      exact ⟨by linarith, by linarith⟩
    _ = _ := by rw [Real.volume_Icc]; congr 1; ring

/-- A convenient fractional interpolation of the two time-fibre bounds. -/
theorem min_linear_le_fractional
    (L z q : ℝ) (hL : 0 ≤ L) (hz : 0 < z) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    min L (2*z) ≤ (L+2)*z^q := by
  by_cases hz1 : z ≤ 1
  · have hp : z ≤ z^q := Real.self_le_rpow_of_le_one hz.le hz1 hq1
    calc
      min L (2*z) ≤ 2*z := min_le_right _ _
      _ ≤ 2*z^q := by gcongr
      _ ≤ (L+2)*z^q := by gcongr; linarith
  · have hp : 1 ≤ z^q := Real.one_le_rpow (le_of_not_ge hz1) hq
    calc
      min L (2*z) ≤ L := min_le_left _ _
      _ ≤ (L+2)*z^q := by nlinarith

/-- The time estimate retains the inverse source-distance factor. -/
theorem time_fiber_fractional_le
    (u v l h r q : ℝ) (hv : v ≠ 0) (hr : 0 < r)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (volume.restrict (Icc l h)) {t : ℝ | |u+t*v| ≤ r} ≤
      ENNReal.ofReal ((|h-l|+2)*r^q) * (ENNReal.ofReal |v|)^(-q) := by
  have hav : 0 < |v| := abs_pos.mpr hv
  have hsmall : (volume.restrict (Icc l h)) {t : ℝ | |u+t*v| ≤ r} ≤
      ENNReal.ofReal |h-l| := by
    calc
      _ ≤ (volume.restrict (Icc l h)) univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal (h-l) := by simp [Real.volume_Icc]
      _ ≤ ENNReal.ofReal |h-l| := ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hlarge := time_fiber_volume_le u v l h r hv hr.le
  have hmin := le_min hsmall hlarge
  calc
    _ ≤ min (ENNReal.ofReal |h-l|) (ENNReal.ofReal (2*r/|v|)) := hmin
    _ = ENNReal.ofReal (min |h-l| (2*(r/|v|))) := by
      rw [ENNReal.ofReal_min]
      congr 2
      ring
    _ ≤ ENNReal.ofReal ((|h-l|+2)*(r/|v|)^q) :=
      ENNReal.ofReal_le_ofReal
        (min_linear_le_fractional |h-l| (r/|v|) q (abs_nonneg _)
          (div_pos hr hav) hq hq1)
    _ = ENNReal.ofReal ((|h-l|+2)*r^q) * (ENNReal.ofReal |v|)^(-q) := by
      rw [Real.div_rpow hr.le hav.le, div_eq_mul_inv, ← Real.rpow_neg hav.le]
      rw [ENNReal.ofReal_rpow_of_pos hav, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- Finite source energy gives a quantitative averaged collision estimate;
its final use below derives that energy from bounded density. -/
theorem averaged_collision_le_source_energy
    (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ → ℝ) (hf : Measurable f)
    (l h r q : ℝ) (hr : 0 < r) (hq : 0 < q) (hq1 : q < 1)
    (hdiag : (μ.prod μ) {p : ℝ × ℝ | p.1=p.2} = 0) :
    ((volume.restrict (Icc l h)).prod (μ.prod μ))
      {p : ℝ × (ℝ × ℝ) |
        |(f p.2.1-f p.2.2)+p.1*(p.2.1-p.2.2)| ≤ r} ≤
      ENNReal.ofReal ((|h-l|+2)*r^q) *
        ∫⁻ p : ℝ × ℝ, (ENNReal.ofReal |p.1-p.2|)^(-q) ∂μ.prod μ := by
  have hm : MeasurableSet {p : ℝ × (ℝ × ℝ) |
      |(f p.2.1-f p.2.2)+p.1*(p.2.1-p.2.2)| ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  have hne : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, p.1 ≠ p.2 := by
    simpa only [ae_iff, not_not] using hdiag
  rw [Measure.prod_apply_symm hm]
  calc
    _ ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((|h-l|+2)*r^q) *
        (ENNReal.ofReal |p.1-p.2|)^(-q) ∂μ.prod μ := by
      apply lintegral_mono_ae
      filter_upwards [hne] with p hp
      exact time_fiber_fractional_le (f p.1-f p.2) (p.1-p.2) l h r q
        (sub_ne_zero.mpr hp) hr hq.le hq1.le
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Arbitrary Borel intercepts preserve finite average energy at every
exponent below one. There is no energy hypothesis in this endpoint. -/
theorem finite_average_scalar_projection_pair_energy
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume) (f : ℝ → ℝ) (hf : Measurable f)
    (l h s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (∫⁻ p : ℝ × (ℝ × ℝ),
      (ENNReal.ofReal |(f p.2.1-f p.2.2)+p.1*(p.2.1-p.2.2)|)^(-s)
        ∂(volume.restrict (Icc l h)).prod (μ.prod μ)) < ∞ := by
  let q : ℝ := (s+1)/2
  have hsq : s < q := by dsimp [q]; linarith
  have hq : 0 < q := hs.trans hsq
  have hq1 : q < 1 := by dsimp [q]; linarith
  let E : ℝ≥0∞ := ∫⁻ p : ℝ × ℝ,
    (ENNReal.ofReal |p.1-p.2|)^(-q) ∂μ.prod μ
  have hE : E < ∞ := finite_source_pair_energy μ D hD hμ q hq hq1
  apply finite_inverse_energy_of_sublevel_power
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

/-- Almost every actual time has finite ordered-pair projection energy. -/
theorem ae_finite_scalar_projection_pair_energy
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume) (f : ℝ → ℝ) (hf : Measurable f)
    (l h s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∀ᵐ t ∂volume.restrict (Icc l h),
      (∫⁻ p : ℝ × ℝ,
        (ENNReal.ofReal |(f p.1-f p.2)+t*(p.1-p.2)|)^(-s) ∂μ.prod μ) < ∞ := by
  exact ae_finite_fiber_inverse_energy_of_finite_product_energy
    (volume.restrict (Icc l h)) (μ.prod μ) _ (by fun_prop) s
    (finite_average_scalar_projection_pair_energy μ D hD hμ f hf l h s hs hs1)


/-- The scalar pushforward identity keeps the ENNReal singularity at zero. -/
theorem scalar_map_energy_eq
    (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ → ℝ) (hf : Measurable f)
    (t s : ℝ) :
    (∫⁻ y, (∫⁻ z, edist y z ^ (-s) ∂μ.map (fun x => f x+t*x))
      ∂μ.map (fun x => f x+t*x)) =
    ∫⁻ p : ℝ × ℝ,
      (ENNReal.ofReal |(f p.1-f p.2)+t*(p.1-p.2)|)^(-s) ∂μ.prod μ := by
  have hg : Measurable (fun x => f x+t*x) := by fun_prop
  have hm : Measurable (fun p : ℝ × ℝ => edist p.1 p.2 ^ (-s)) := by fun_prop
  calc
    _ = ∫⁻ x, (∫⁻ z, edist (f x+t*x) z ^ (-s)
          ∂μ.map (fun y => f y+t*y)) ∂μ :=
      lintegral_map (f := fun y : ℝ => ∫⁻ z, edist y z ^ (-s)
        ∂μ.map (fun x => f x+t*x)) hm.lintegral_prod_right' hg
    _ = ∫⁻ x, (∫⁻ y, edist (f x+t*x) (f y+t*y) ^ (-s) ∂μ) ∂μ := by
      apply lintegral_congr
      intro x
      exact lintegral_map (by fun_prop) hg
    _ = _ := by
      rw [lintegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro y
      have he : (f x+t*x)-(f y+t*y) = (f x-f y)+t*(x-y) := by ring
      rw [edist_dist, Real.dist_eq, he]

/-- The average is finite for the full, actual projected measures of an
arbitrary measurable scalar intercept function. -/
theorem finite_average_scalar_projection_energy
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume) (f : ℝ → ℝ) (hf : Measurable f)
    (l h s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (∫⁻ t in Icc l h, (∫⁻ y, (∫⁻ z, edist y z ^ (-s)
      ∂μ.map (fun x => f x+t*x)) ∂μ.map (fun x => f x+t*x))) < ∞ := by
  calc
    _ = ∫⁻ t in Icc l h, (∫⁻ p : ℝ × ℝ,
        (ENNReal.ofReal |(f p.1-f p.2)+t*(p.1-p.2)|)^(-s) ∂μ.prod μ) :=
      lintegral_congr (fun t => scalar_map_energy_eq μ f hf t s)
    _ = ∫⁻ p : ℝ × (ℝ × ℝ),
        (ENNReal.ofReal |(f p.2.1-f p.2.2)+p.1*(p.2.1-p.2.2)|)^(-s)
          ∂(volume.restrict (Icc l h)).prod (μ.prod μ) :=
      (inverse_energy_prod_eq_iterated (volume.restrict (Icc l h))
        (μ.prod μ)
        (fun p : ℝ × (ℝ × ℝ) => |(f p.2.1-f p.2.2)+p.1*(p.2.1-p.2.2)|)
        (by fun_prop) s).symm
    _ < ∞ := finite_average_scalar_projection_pair_energy μ D hD hμ f hf l h s hs hs1

/-- For almost every actual time the full projected measure has finite
s-energy. The bounded-density source assumptions derive all energy inputs. -/
theorem ae_finite_scalar_projection_energy
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume) (f : ℝ → ℝ) (hf : Measurable f)
    (l h s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∀ᵐ t ∂volume.restrict (Icc l h),
      (∫⁻ y, (∫⁻ z, edist y z ^ (-s) ∂μ.map (fun x => f x+t*x))
        ∂μ.map (fun x => f x+t*x)) < ∞ := by
  filter_upwards [ae_finite_scalar_projection_pair_energy μ D hD hμ f hf l h s hs hs1]
    with t ht
  rw [scalar_map_energy_eq μ f hf t s]
  exact ht

end StickyKakeya4.ScalarProjection
