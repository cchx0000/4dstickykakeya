import Theorems.Thm_StickyKakeya4_residual_sublevel_power

/-!
# A direct extra-dimensional collision-energy gain

The analytical passage from the original manuscript's averaged transverse
collision bound to the four-dimensional front is proved for the actual E4
spacetime parametrization.  A radius-ρ spacetime collision forces two times
within ρ and a same-time transverse collision at radius `(1+A)ρ`, when target
slopes have norm at most A.  Integrating the second time gives the exact factor
2ρ and raises the sublevel exponent by one.  The generic layer-cake theorem
then gives finite energy of the actual pushed-forward front measure.

The source measure, its almost-everywhere slope bound, and its averaged
collision bound remain explicit.  No geometric residual power estimate,
measurable Frostman-kernel selection, or unproved slicing theorem is assumed.
-/

open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace StickyKakeya4

/-- The inverse-distance energy of a measurable pushforward is exactly the
ordered-pair energy of its source, including zero-distance singularities. -/
theorem map_inverse_energy_eq_distance_pair_integral
    {X Y : Type*} [MeasurableSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (μ : Measure X) [IsFiniteMeasure μ] (g : X → Y) (hg : Measurable g) (t : ℝ) :
    (∫⁻ y, (∫⁻ z, edist y z ^ (-t) ∂μ.map g) ∂μ.map g) =
      ∫⁻ p, (ENNReal.ofReal (dist (g p.1) (g p.2))) ^ (-t) ∂μ.prod μ := by
  have hm : Measurable (fun p : Y × Y => edist p.1 p.2 ^ (-t)) := by fun_prop
  have hinner (x : X) :
      (∫⁻ z, edist (g x) z ^ (-t) ∂μ.map g) =
        ∫⁻ y, edist (g x) (g y) ^ (-t) ∂μ :=
    lintegral_map (by fun_prop) hg
  calc
    (∫⁻ y, (∫⁻ z, edist y z ^ (-t) ∂μ.map g) ∂μ.map g) =
        ∫⁻ x, (∫⁻ z, edist (g x) z ^ (-t) ∂μ.map g) ∂μ :=
      lintegral_map hm.lintegral_prod_right' hg
    _ = ∫⁻ x, (∫⁻ y, edist (g x) (g y) ^ (-t) ∂μ) ∂μ :=
      lintegral_congr hinner
    _ = ∫⁻ p, (ENNReal.ofReal (dist (g p.1) (g p.2))) ^ (-t) ∂μ.prod μ := by
      rw [lintegral_prod _ (by fun_prop)]
      simp only [edist_dist]

/-- A finite time/ordered-pair energy yields finite energy for almost every
actual projected measure of a jointly measurable family of maps. -/
theorem ae_finite_map_inverse_energy_of_finite_time_pair_energy
    {S X Y : Type*} [MeasurableSpace S] [MeasurableSpace X]
    [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (τ : Measure S) (μ : Measure X) [IsFiniteMeasure μ]
    (g : S × X → Y) (hg : Measurable g) (t : ℝ)
    (henergy : (∫⁻ p : S × (X × X),
      (ENNReal.ofReal (dist (g (p.1, p.2.1)) (g (p.1, p.2.2)))) ^ (-t)
        ∂τ.prod (μ.prod μ)) < ∞) :
    ∀ᵐ s ∂τ, (∫⁻ y, (∫⁻ z, edist y z ^ (-t)
      ∂μ.map (fun x => g (s, x))) ∂μ.map (fun x => g (s, x))) < ∞ := by
  have hm : Measurable
      (fun p : S × (X × X) => dist (g (p.1, p.2.1)) (g (p.1, p.2.2))) := by
    fun_prop
  have hae := ae_finite_fiber_inverse_energy_of_finite_product_energy
    τ (μ.prod μ) _ hm t henergy
  filter_upwards [hae] with s hs
  rw [map_inverse_energy_eq_distance_pair_integral μ (fun x => g (s, x))
    (by fun_prop) t]
  exact hs

/-- The actual Euclidean four-dimensional lift of a horizontal point and time. -/
def spacetimeLift (y : E3) (s : ℝ) : E4 :=
  WithLp.toLp 2 (Fin.lastCases s (fun i : Fin 3 => y i))

@[simp] theorem spacetimeLift_castSucc (y : E3) (s : ℝ) (i : Fin 3) :
    spacetimeLift y s i.castSucc = y i := by simp [spacetimeLift]

@[simp] theorem spacetimeLift_last (y : E3) (s : ℝ) :
    spacetimeLift y s (Fin.last 3) = s := by
  simpa [spacetimeLift] using
    (Fin.lastCases_last (motive := fun _ : Fin 4 => ℝ)
      (last := s) (cast := fun i : Fin 3 => y i))

theorem spacetimeLift_sub (y z : E3) (s t : ℝ) :
    spacetimeLift y s - spacetimeLift z t = spacetimeLift (y - z) (s - t) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [PiLp.sub_apply, spacetimeLift_last]
  · simp only [PiLp.sub_apply, spacetimeLift_castSucc]

theorem spacetimeLift_norm_sq (y : E3) (s : ℝ) :
    ‖spacetimeLift y s‖ ^ 2 = ‖y‖ ^ 2 + s ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc,
    EuclideanSpace.real_norm_sq_eq]
  simp only [spacetimeLift_castSucc, spacetimeLift_last]

theorem measurable_spacetimeLift :
    Measurable (fun p : E3 × ℝ => spacetimeLift p.1 p.2) := by
  unfold spacetimeLift
  apply (WithLp.measurable_toLp 2 (Fin 4 → ℝ)).comp
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last]
    exact measurable_snd
  · simp only [Fin.lastCases_castSucc]
    fun_prop

/-- A Euclidean spacetime collision bounds both its horizontal displacement
and its time displacement, with no metric-equivalence loss. -/
theorem spacetimeLift_collision_coordinates
    (y z : E3) (s t ρ : ℝ) (hρ : 0 ≤ ρ)
    (h : ‖spacetimeLift y s - spacetimeLift z t‖ ≤ ρ) :
    ‖y - z‖ ≤ ρ ∧ |s - t| ≤ ρ := by
  have hsq : ‖spacetimeLift y s - spacetimeLift z t‖ ^ 2 =
      ‖y - z‖ ^ 2 + (s - t) ^ 2 := by
    rw [spacetimeLift_sub, spacetimeLift_norm_sq]
  have hnorm : 0 ≤ ‖spacetimeLift y s - spacetimeLift z t‖ := norm_nonneg _
  constructor
  · nlinarith [norm_nonneg (y - z), sq_nonneg (s - t)]
  · nlinarith [sq_nonneg ‖y - z‖, sq_abs (s - t), abs_nonneg (s - t)]

/-- The spacetime parametrization of the affine graph family. -/
def slopeSpacetimePoint (b : E3 → E3) (p : ℝ × E3) : E4 :=
  spacetimeLift (b p.2 + p.1 • p.2) p.1

theorem measurable_slopeSpacetimePoint (b : E3 → E3) (hb : Measurable b) :
    Measurable (slopeSpacetimePoint b) := by
  unfold slopeSpacetimePoint
  exact measurable_spacetimeLift.comp
    (((hb.comp measurable_snd).add (measurable_fst.smul measurable_snd)).prodMk
      measurable_fst)

/-- A spacetime collision between bounded-slope trajectories forces a
same-time transverse collision at only the factor `1+A` larger radius. -/
theorem spacetime_collision_imp_same_time
    (b : E3 → E3) (a a' : E3) (s s' A ρ : ℝ) (hρ : 0 ≤ ρ)
    (hA : ‖a'‖ ≤ A)
    (h : ‖slopeSpacetimePoint b (s, a) - slopeSpacetimePoint b (s', a')‖ ≤ ρ) :
    |s - s'| ≤ ρ ∧ ‖(b a - b a') + s • (a - a')‖ ≤ (1 + A) * ρ := by
  obtain ⟨hh, ht⟩ := spacetimeLift_collision_coordinates
    (b a + s • a) (b a' + s' • a') s s' ρ hρ h
  refine ⟨ht, ?_⟩
  have hv : (b a - b a') + s • (a - a') =
      ((b a + s • a) - (b a' + s' • a')) + (s' - s) • a' := by module
  have hm : ‖(s' - s) • a'‖ ≤ ρ * A := by
    rw [norm_smul, Real.norm_eq_abs, abs_sub_comm s' s]
    exact mul_le_mul ht hA (norm_nonneg _) hρ
  rw [hv]
  calc
    _ ≤ ‖(b a + s • a) - (b a' + s' • a')‖ + ‖(s' - s) • a'‖ := norm_add_le _ _
    _ ≤ ρ + ρ * A := add_le_add hh hm
    _ = (1 + A) * ρ := by ring

/-- For a fixed source and target slope, the target-time collision fibre has
length at most `2ρ`, and is empty unless there is a same-time collision. -/
theorem spacetime_time_fiber_volume_le
    (b : E3 → E3) (a a' : E3) (s u v A ρ : ℝ) (hρ : 0 ≤ ρ) (hA : ‖a'‖ ≤ A) :
    (volume.restrict (Icc u v))
      {s' | ‖slopeSpacetimePoint b (s, a) - slopeSpacetimePoint b (s', a')‖ ≤ ρ} ≤
      if ‖(b a - b a') + s • (a - a')‖ ≤ (1 + A) * ρ
      then ENNReal.ofReal (2 * ρ) else 0 := by
  split_ifs with hc
  · calc
      _ ≤ volume
          {s' | ‖slopeSpacetimePoint b (s, a) - slopeSpacetimePoint b (s', a')‖ ≤ ρ} :=
        Measure.restrict_le_self _
      _ ≤ volume (Icc (s - ρ) (s + ρ)) := by
        apply measure_mono
        intro s' hs'
        have ht := (spacetime_collision_imp_same_time b a a' s s' A ρ hρ hA hs').1
        obtain ⟨hlo, hhi⟩ := abs_le.mp ht
        exact ⟨by linarith, by linarith⟩
      _ = ENNReal.ofReal (2 * ρ) := by rw [Real.volume_Icc]; congr 1; ring
  · have he : {s' | ‖slopeSpacetimePoint b (s, a) - slopeSpacetimePoint b (s', a')‖ ≤ ρ} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro s' hs'
      exact hc (spacetime_collision_imp_same_time b a a' s s' A ρ hρ hA hs').2
    rw [he, measure_empty]

/-- The target-time fibre estimate integrated over the actual target slope
measure.  Bounded slopes are required only almost everywhere. -/
theorem spacetime_source_row_mass_le
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3) (hb : Measurable b)
    (a : E3) (s u v A ρ : ℝ) (hρ : 0 ≤ ρ)
    (hA : ∀ᵐ a' ∂σ, ‖a'‖ ≤ A) :
    ((volume.restrict (Icc u v)).prod σ)
      {p : ℝ × E3 | ‖slopeSpacetimePoint b (s, a) - slopeSpacetimePoint b p‖ ≤ ρ} ≤
      ENNReal.ofReal (2 * ρ) *
        σ {a' | ‖(b a - b a') + s • (a - a')‖ ≤ (1 + A) * ρ} := by
  have hF := measurable_slopeSpacetimePoint b hb
  have hs : MeasurableSet
      {p : ℝ × E3 | ‖slopeSpacetimePoint b (s, a) - slopeSpacetimePoint b p‖ ≤ ρ} :=
    measurableSet_le (measurable_const.sub hF).norm measurable_const
  have hc : MeasurableSet {a' | ‖(b a - b a') + s • (a - a')‖ ≤ (1 + A) * ρ} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.prod_apply_symm hs]
  calc
    _ ≤ ∫⁻ a', {a' | ‖(b a - b a') + s • (a - a')‖ ≤ (1 + A) * ρ}.indicator
        (fun _ => ENNReal.ofReal (2 * ρ)) a' ∂σ := by
      apply lintegral_mono_ae
      filter_upwards [hA] with a' ha'
      exact spacetime_time_fiber_volume_le b a a' s u v A ρ hρ ha'
    _ = _ := lintegral_indicator_const hc _

/-- The concrete extra-dimensional gain: full spacetime pair sublevel mass
is at most `2ρ` times the averaged transverse collision mass at radius `(1+A)ρ`.
All endpoint pairs and both time variables are retained in the product measure. -/
theorem spacetime_pair_sublevel_le_time_collision
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3) (hb : Measurable b)
    (u v A ρ : ℝ) (hρ : 0 ≤ ρ) (hA : ∀ᵐ a ∂σ, ‖a‖ ≤ A) :
    (((volume.restrict (Icc u v)).prod σ).prod ((volume.restrict (Icc u v)).prod σ))
      {p : (ℝ × E3) × (ℝ × E3) |
        ‖slopeSpacetimePoint b p.1 - slopeSpacetimePoint b p.2‖ ≤ ρ} ≤
      ENNReal.ofReal (2 * ρ) *
        ∫⁻ s in Icc u v, (σ.prod σ)
          {p : E3 × E3 | ‖(b p.1 - b p.2) + s • (p.1 - p.2)‖ ≤ (1 + A) * ρ} := by
  have hF := measurable_slopeSpacetimePoint b hb
  have hs : MeasurableSet {p : (ℝ × E3) × (ℝ × E3) |
      ‖slopeSpacetimePoint b p.1 - slopeSpacetimePoint b p.2‖ ≤ ρ} :=
    measurableSet_le (by fun_prop) measurable_const
  have hrow : Measurable (fun p : ℝ × E3 =>
      σ {a' | ‖(b p.2 - b a') + p.1 • (p.2 - a')‖ ≤ (1 + A) * ρ}) := by
    have hm : MeasurableSet {z : (ℝ × E3) × E3 |
        ‖(b z.1.2 - b z.2) + z.1.1 • (z.1.2 - z.2)‖ ≤ (1 + A) * ρ} :=
      measurableSet_le (by fun_prop) measurable_const
    exact measurable_measure_prodMk_left (ν := σ) hm
  rw [Measure.prod_apply hs]
  calc
    _ ≤ ∫⁻ p : ℝ × E3, ENNReal.ofReal (2 * ρ) *
        σ {a' | ‖(b p.2 - b a') + p.1 • (p.2 - a')‖ ≤ (1 + A) * ρ}
          ∂(volume.restrict (Icc u v)).prod σ := by
      apply lintegral_mono
      intro p
      exact spacetime_source_row_mass_le σ b hb p.2 p.1 u v A ρ hρ hA
    _ = ENNReal.ofReal (2 * ρ) *
        ∫⁻ p : ℝ × E3,
          σ {a' | ‖(b p.2 - b a') + p.1 • (p.2 - a')‖ ≤ (1 + A) * ρ}
            ∂(volume.restrict (Icc u v)).prod σ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      congr 1
      rw [lintegral_prod _ hrow.aemeasurable]
      apply lintegral_congr
      intro s
      have hm : MeasurableSet {p : E3 × E3 |
          ‖(b p.1 - b p.2) + s • (p.1 - p.2)‖ ≤ (1 + A) * ρ} :=
        measurableSet_le (by fun_prop) measurable_const
      exact (Measure.prod_apply hm).symm

/-- Local sublevel bounds below any fixed positive radius suffice for finite
inverse energy.  Larger radii are controlled by the finite total mass. -/
theorem finite_inverse_energy_of_local_sublevel_power
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (C q t R : ℝ) (hC : 0 ≤ C) (ht : 0 < t) (htq : t < q) (hR : 0 < R)
    (hsub : ∀ r : ℝ, 0 < r → r < R →
      μ {x | f x ≤ r} ≤ ENNReal.ofReal (C * r ^ q)) :
    (∫⁻ x, (ENNReal.ofReal (f x)) ^ (-t) ∂μ) < ∞ := by
  let M : ℝ := (μ univ).toReal
  let D : ℝ := C + M / R ^ q
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hq : 0 < q := ht.trans htq
  have hRq : 0 < R ^ q := Real.rpow_pos_of_pos hR q
  have hD : 0 ≤ D := add_nonneg hC (div_nonneg hM hRq.le)
  apply finite_inverse_energy_of_sublevel_power μ f hf hf0 D q t hD ht htq
  intro r hr0 _hr1
  have hrq : 0 ≤ r ^ q := Real.rpow_nonneg hr0.le q
  by_cases hrR : r < R
  · exact (hsub r hr0 hrR).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith [div_nonneg hM hRq.le]) hrq))
  · have hp : R ^ q ≤ r ^ q := Real.rpow_le_rpow hR.le (le_of_not_gt hrR) hq.le
    have hMr : M ≤ (M / R ^ q) * r ^ q := by
      calc
        M = (M / R ^ q) * R ^ q := (div_mul_cancel₀ M hRq.ne').symm
        _ ≤ (M / R ^ q) * r ^ q := mul_le_mul_of_nonneg_left hp (div_nonneg hM hRq.le)
    calc
      μ {x | f x ≤ r} ≤ μ univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal M := (ENNReal.ofReal_toReal (measure_ne_top μ univ)).symm
      _ ≤ ENNReal.ofReal (D * r ^ q) := ENNReal.ofReal_le_ofReal (hMr.trans
        (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) hrq))

/-- The averaged transverse sublevel exponent `q` gains one full dimension
for the actual Euclidean spacetime front, under almost-everywhere bounded
slopes.  This is a direct energy proof and does not assume a slicing theorem. -/
theorem finite_spacetime_pair_energy_of_averaged_sublevel_power
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3) (hb : Measurable b)
    (u v A C q t : ℝ) (hA : 0 ≤ A) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ A)
    (hC : 0 ≤ C) (hq : 0 < q) (ht : 0 < t) (htq : t < q + 1)
    (hsub : ∀ r : ℝ, 0 < r → r < 1 →
      (∫⁻ s in Icc u v, (σ.prod σ)
        {p : E3 × E3 | ‖(b p.1 - b p.2) + s • (p.1 - p.2)‖ ≤ r}) ≤
          ENNReal.ofReal (C * r ^ q)) :
    (∫⁻ p : (ℝ × E3) × (ℝ × E3),
      (ENNReal.ofReal ‖slopeSpacetimePoint b p.1 - slopeSpacetimePoint b p.2‖) ^ (-t)
      ∂(((volume.restrict (Icc u v)).prod σ).prod
        ((volume.restrict (Icc u v)).prod σ))) < ∞ := by
  have hF := measurable_slopeSpacetimePoint b hb
  have hm : Measurable (fun p : (ℝ × E3) × (ℝ × E3) =>
      ‖slopeSpacetimePoint b p.1 - slopeSpacetimePoint b p.2‖) := by fun_prop
  have hk : 0 < 1 + A := by linarith
  apply finite_inverse_energy_of_local_sublevel_power
    (((volume.restrict (Icc u v)).prod σ).prod ((volume.restrict (Icc u v)).prod σ))
    _ hm (fun _ => norm_nonneg _) (2 * C * (1 + A) ^ q) (q + 1) t (1 / (1 + A))
    (by positivity) ht htq (by positivity)
  intro r hr0 hrR
  have hkr0 : 0 < (1 + A) * r := mul_pos hk hr0
  have hkr1 : (1 + A) * r < 1 := by
    have h := (lt_div_iff₀ hk).mp hrR
    nlinarith
  calc
    _ ≤ ENNReal.ofReal (2 * r) *
        ∫⁻ s in Icc u v, (σ.prod σ)
          {p : E3 × E3 | ‖(b p.1 - b p.2) + s • (p.1 - p.2)‖ ≤ (1 + A) * r} :=
      spacetime_pair_sublevel_le_time_collision σ b hb u v A r hr0.le hslopes
    _ ≤ ENNReal.ofReal (2 * r) * ENNReal.ofReal (C * ((1 + A) * r) ^ q) := by
      gcongr
      exact hsub ((1 + A) * r) hkr0 hkr1
    _ = ENNReal.ofReal ((2 * C * (1 + A) ^ q) * r ^ (q + 1)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.mul_rpow hk.le hr0.le, Real.rpow_add hr0, Real.rpow_one]
      ring

/-- The finite-energy measure is the actual pushforward onto the Euclidean
spacetime front.  Consequently support can be checked in the original compact
front, with no weak-limit or selector-closure substitution. -/
theorem finite_spacetime_front_energy_of_averaged_sublevel_power
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3) (hb : Measurable b)
    (u v A C q t : ℝ) (hA : 0 ≤ A) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ A)
    (hC : 0 ≤ C) (hq : 0 < q) (ht : 0 < t) (htq : t < q + 1)
    (hsub : ∀ r : ℝ, 0 < r → r < 1 →
      (∫⁻ s in Icc u v, (σ.prod σ)
        {p : E3 × E3 | ‖(b p.1 - b p.2) + s • (p.1 - p.2)‖ ≤ r}) ≤
          ENNReal.ofReal (C * r ^ q)) :
    (∫⁻ x, (∫⁻ y, edist x y ^ (-t)
      ∂(((volume.restrict (Icc u v)).prod σ).map (slopeSpacetimePoint b)))
      ∂(((volume.restrict (Icc u v)).prod σ).map (slopeSpacetimePoint b))) < ∞ := by
  rw [map_inverse_energy_eq_distance_pair_integral
    ((volume.restrict (Icc u v)).prod σ) (slopeSpacetimePoint b)
      (measurable_slopeSpacetimePoint b hb) t]
  simpa only [dist_eq_norm] using
    finite_spacetime_pair_energy_of_averaged_sublevel_power σ b hb u v A C q t
      hA hslopes hC hq ht htq hsub

end StickyKakeya4
