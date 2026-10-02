import Theorems.Thm_StickyKakeya4_packet_free_bush_bound
import Theorems.Thm_StickyKakeya4_angular_residual_shell

/-!
# Uniform inverse-distance potential in a root line tube

An explicit scalar grid covers the radius-`s` part of a tube by `O(s/δ)`
balls of radius `3δ`. Cubic ball density therefore gives `O(s δ²)`.
Interpolating this with the cubic ball bound yields radial sublevel growth
`O(δ^(2-ε) s^(1+ε))`. Layer cake integrates this genuine radial estimate,
producing a uniform finite constant `81 (4π/3) (1+1/ε)`.

The weight is the extended nonnegative inverse of the distance, hence is
infinite at the root. Its singular set is proved null from cubic density
before any conversion to a real-valued inverse is used.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
noncomputable section
namespace StickyKakeya4.LineTubeInversePotential
open PacketFreeBushBound

/-- A radius-`s` portion of a line tube has an explicit one-dimensional cover. -/
theorem local_residual_tube_cover (x a q v : E3)
    (hroot : lineResidual a q v = 0) (δ s : ℝ)
    (hδ : 0 < δ) (hs : 0 < s) (hx : ‖x - a‖ ≤ s)
    (hres : ‖lineResidual x q v‖ ≤ 2 * δ) :
    ∃ i ∈ Finset.range (⌊2 / (δ / s)⌋₊ + 1),
      x ∈ Metric.closedBall (a + (-s + (i : ℝ) * δ) • lineUnit v) (3 * δ) := by
  have hu : |inner ℝ (x - a) (lineUnit v)| ≤ s := by
    calc
      _ = ‖inner ℝ (x - a) (lineUnit v)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x - a‖ * ‖lineUnit v‖ := norm_inner_le_norm _ _
      _ ≤ s * 1 := mul_le_mul hx (norm_lineUnit_le_one v) (norm_nonneg _) hs.le
      _ = s := mul_one _
  have hu' : |inner ℝ (x - a) (lineUnit v) / s| ≤ 1 := by
    rw [abs_div, abs_of_pos hs]
    exact (div_le_one hs).mpr hu
  obtain ⟨i, hi, hdist⟩ := scalar_grid_cover (δ / s)
    (inner ℝ (x - a) (lineUnit v) / s) (div_pos hδ hs) hu'
  have hdist' : |inner ℝ (x - a) (lineUnit v) - (-s + (i : ℝ) * δ)| ≤ δ := by
    have hh := (mul_le_mul_of_nonneg_right hdist hs.le)
    rw [div_mul_cancel₀ _ hs.ne'] at hh
    calc
      _ = |inner ℝ (x - a) (lineUnit v) / s - (-1 + (i : ℝ) * (δ / s))| * s := by
        symm
        calc
          _ = |(inner ℝ (x - a) (lineUnit v) / s - (-1 + (i : ℝ) * (δ / s))) * s| := by
            rw [abs_mul, abs_of_pos hs]
          _ = _ := by
            congr 1
            field_simp
      _ ≤ δ := hh
  refine ⟨i, hi, ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  have heq : x - (a + (-s + (i : ℝ) * δ) • lineUnit v) =
      lineResidual x q v +
        (inner ℝ (x - a) (lineUnit v) - (-s + (i : ℝ) * δ)) • lineUnit v := by
    have ha : a = lineBase q v + inner ℝ a (lineUnit v) • lineUnit v := by
      exact sub_eq_zero.mp hroot
    simp only [lineResidual, inner_sub_left, sub_smul]
    nth_rw 1 [ha]
    module
  rw [heq]
  have hn : ‖(inner ℝ (x - a) (lineUnit v) - (-s + (i : ℝ) * δ)) • lineUnit v‖ ≤ δ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hdist' (norm_lineUnit_le_one v) (norm_nonneg _) hδ.le).trans_eq
      (mul_one δ)
  exact (norm_add_le _ _).trans (by linarith)

/-- Cubic ball density pays a length-`s` tube by `s δ²`. -/
theorem local_residual_tube_mass_le (σ : Measure E3) (C : ℝ≥0∞)
    (hdensity : ∀ x : E3, ∀ r : ℝ, 0 ≤ r →
      σ (Metric.closedBall x r) ≤ C * ENNReal.ofReal r ^ 3)
    (a q v : E3) (hroot : lineResidual a q v = 0) (δ s : ℝ) (hδ : 0 < δ) (hδs : δ ≤ s) :
    σ {x | ‖x - a‖ ≤ s ∧ ‖lineResidual x q v‖ ≤ 2 * δ} ≤
      81 * C * ENNReal.ofReal s * ENNReal.ofReal δ ^ 2 := by
  classical
  have hs : 0 < s := hδ.trans_le hδs
  let n : ℕ := ⌊2 / (δ / s)⌋₊ + 1
  let caps : ℕ → Set E3 := fun i =>
    Metric.closedBall (a + (-s + (i : ℝ) * δ) • lineUnit v) (3 * δ)
  have hsub : {x | ‖x - a‖ ≤ s ∧ ‖lineResidual x q v‖ ≤ 2 * δ} ⊆
      ⋃ i ∈ Finset.range n, caps i := by
    intro x hx
    obtain ⟨i, hi, hcap⟩ := local_residual_tube_cover x a q v hroot δ s hδ hs hx.1 hx.2
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hcap⟩⟩
  have hcardR : (n : ℝ) * δ ≤ 3 * s := by
    have hh := mul_le_mul_of_nonneg_right
      (scalar_grid_card_bound (δ / s) (div_pos hδ hs) ((div_le_one hs).mpr hδs)) hs.le
    dsimp [n] at *
    convert hh using 1 <;> (first | rfl | field_simp)
  have hcard : (n : ℝ≥0∞) * ENNReal.ofReal δ ≤ 3 * ENNReal.ofReal s := by
    have hh := ENNReal.ofReal_le_ofReal hcardR
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat] using hh
  calc
    _ ≤ σ (⋃ i ∈ Finset.range n, caps i) := measure_mono hsub
    _ ≤ ∑ i ∈ Finset.range n, σ (caps i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range n, C * ENNReal.ofReal (3 * δ) ^ 3 := by
      apply Finset.sum_le_sum
      intro i hi
      exact hdensity _ _ (by positivity)
    _ = (n : ℝ≥0∞) * (C * ENNReal.ofReal (3 * δ) ^ 3) := by simp
    _ = 27 * C * ((n : ℝ≥0∞) * ENNReal.ofReal δ) * ENNReal.ofReal δ ^ 2 := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
      ring
    _ ≤ 27 * C * (3 * ENNReal.ofReal s) * ENNReal.ofReal δ ^ 2 := by gcongr
    _ = _ := by ring

/-- Power interpolation between the ball and tube scales. -/
theorem cubic_le_interpolated (δ r ε : ℝ) (_hδ : 0 < δ) (hr : 0 < r)
    (hrδ : r ≤ δ) (hε : ε < 1) :
    r ^ 3 ≤ δ ^ (2 - ε) * r ^ (1 + ε) := by
  calc
    r ^ 3 = r ^ (2 - ε) * r ^ (1 + ε) := by
      rw [← Real.rpow_add hr]
      norm_num
    _ ≤ δ ^ (2 - ε) * r ^ (1 + ε) := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hr.le hrδ (by linarith : 0 ≤ 2 - ε))
        (Real.rpow_nonneg hr.le _)

theorem tube_le_interpolated (δ r ε : ℝ) (hδ : 0 < δ) (hr : 0 < r)
    (hδr : δ ≤ r) (hε : 0 < ε) :
    r * δ ^ 2 ≤ δ ^ (2 - ε) * r ^ (1 + ε) := by
  have hp : δ ^ ε ≤ r ^ ε := Real.rpow_le_rpow hδ.le hδr hε.le
  calc
    r * δ ^ 2 = δ ^ (2 - ε) * (r * δ ^ ε) := by
      have hh : δ ^ (2 - ε) * δ ^ ε = δ ^ 2 := by
        rw [← Real.rpow_add hδ]
        norm_num
      nlinarith [hh]
    _ ≤ δ ^ (2 - ε) * (r * r ^ ε) := by gcongr
    _ = δ ^ (2 - ε) * r ^ (1 + ε) := by
      rw [Real.rpow_add hr, Real.rpow_one]

/-- The restricted tube has an improved radial sublevel bound about its root. -/
theorem local_residual_tube_mass_le_power (σ : Measure E3) (C : ℝ≥0∞)
    (hdensity : ∀ x : E3, ∀ r : ℝ, 0 ≤ r →
      σ (Metric.closedBall x r) ≤ C * ENNReal.ofReal r ^ 3)
    (a q v : E3) (hroot : lineResidual a q v = 0) (δ r ε : ℝ) (hδ : 0 < δ) (hr : 0 < r)
    (hε : 0 < ε) (hε1 : ε < 1) :
    σ {x | ‖x - a‖ ≤ r ∧ ‖lineResidual x q v‖ ≤ 2 * δ} ≤
      (81 * C * ENNReal.ofReal (δ ^ (2 - ε))) * ENNReal.ofReal (r ^ (1 + ε)) := by
  by_cases hrδ : r ≤ δ
  · calc
      _ ≤ σ (Metric.closedBall a r) := measure_mono (fun x hx => by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hx.1)
      _ ≤ C * ENNReal.ofReal r ^ 3 := hdensity a r hr.le
      _ ≤ 81 * C * ENNReal.ofReal r ^ 3 := by
        apply mul_le_mul_left
        simpa only [one_mul] using (mul_le_mul_left (by norm_num : (1 : ℝ≥0∞) ≤ 81) C)
      _ ≤ _ := by
        rw [← ENNReal.ofReal_pow hr.le, mul_assoc (81 * C),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
          (cubic_le_interpolated δ r ε hδ hr hrδ hε1)) (81 * C)
  · calc
      _ ≤ 81 * C * ENNReal.ofReal r * ENNReal.ofReal δ ^ 2 :=
        local_residual_tube_mass_le σ C hdensity a q v hroot δ r hδ (le_of_not_ge hrδ)
      _ ≤ _ := by
        rw [← ENNReal.ofReal_pow hδ.le, mul_assoc (81 * C),
          ← ENNReal.ofReal_mul hr.le, mul_assoc (81 * C),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
          (tube_le_interpolated δ r ε hδ hr (le_of_not_ge hrδ) hε)) (81 * C)

theorem inverse_integral_le_of_power_sublevel
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Measurable f)
    (ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1)
    (D : ℝ≥0∞) (hD : D ≠ ⊤)
    (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (htotal : μ univ ≤ D)
    (hsub : ∀ r : ℝ, 0 < r → μ {x | f x ≤ r} ≤
      D * ENNReal.ofReal (r ^ (1 + ε))) :
    (∫⁻ x, (ENNReal.ofReal (f x))⁻¹ ∂μ) ≤
      D * (1 + ENNReal.ofReal (1 / ε)) := by
  have heq : (fun x => (ENNReal.ofReal (f x))⁻¹) =ᵐ[μ]
      (fun x => ENNReal.ofReal ((f x)⁻¹)) := by
    filter_upwards [hpos] with x hx
    exact (ENNReal.ofReal_inv_of_pos hx).symm
  rw [lintegral_congr_ae heq,
    lintegral_eq_lintegral_meas_le μ
      (hpos.mono (fun _ hx => (inv_pos.mpr hx).le)) hf.inv.aemeasurable]
  have hsmall : (∫⁻ z in Ioc (0 : ℝ) 1,
      μ {x | z ≤ (f x)⁻¹}) ≤ D := by
    calc
      _ ≤ ∫⁻ _z in Ioc (0 : ℝ) 1, D := by
        apply lintegral_mono
        intro z
        exact (measure_mono (subset_univ _)).trans htotal
      _ = D := by simp [Real.volume_Ioc]
  have hlarge : (∫⁻ z in Ioi (1 : ℝ),
      μ {x | z ≤ (f x)⁻¹}) ≤ D * ENNReal.ofReal (1 / ε) := by
    have hpowint := integrableOn_Ioi_rpow_of_lt
      (by linarith : -(1 + ε) < -1) (by norm_num : (0 : ℝ) < 1)
    have hpow0 : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))]
        (fun z : ℝ => z ^ (-(1 + ε))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      exact Real.rpow_nonneg (zero_lt_one.trans hz).le _
    have hpow : (∫⁻ z in Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-(1 + ε)))) =
        ENNReal.ofReal (1 / ε) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hpowint hpow0,
        integral_Ioi_rpow_of_lt (by linarith : -(1 + ε) < -1)
          (by norm_num : (0 : ℝ) < 1)]
      congr 1
      simp only [Real.one_rpow]
      field_simp [hε.ne']
      ring
    calc
      _ ≤ ∫⁻ z in Ioi (1 : ℝ), D * ENNReal.ofReal (z ^ (-(1 + ε))) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
        have hz0 : 0 < z := lt_trans zero_lt_one hz
        calc
          μ {x | z ≤ (f x)⁻¹} ≤ μ {x | f x ≤ z⁻¹} := by
            apply measure_mono_ae
            filter_upwards [hpos] with x hx
            intro hzx
            have hi := (inv_le_inv₀ (inv_pos.mpr hx) hz0).mpr hzx
            change f x ≤ z⁻¹
            simpa only [inv_inv] using hi
          _ ≤ D * ENNReal.ofReal ((z⁻¹) ^ (1 + ε)) := hsub z⁻¹ (inv_pos.mpr hz0)
          _ = D * ENNReal.ofReal (z ^ (-(1 + ε))) := by
            rw [Real.rpow_neg_eq_inv_rpow]
      _ = D * ∫⁻ z in Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-(1 + ε))) :=
        lintegral_const_mul' _ _ hD
      _ = _ := by rw [hpow]
  calc
    _ ≤ ∫⁻ z in Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ),
        μ {x | z ≤ (f x)⁻¹} :=
      lintegral_mono_set Ioi_subset_Ioc_union_Ioi
    _ ≤ (∫⁻ z in Ioc (0 : ℝ) 1, μ {x | z ≤ (f x)⁻¹}) +
        ∫⁻ z in Ioi (1 : ℝ), μ {x | z ≤ (f x)⁻¹} :=
      lintegral_union_le _ _ _
    _ ≤ D + D * ENNReal.ofReal (1 / ε) := add_le_add hsmall hlarge
    _ = _ := by ring


/-- The singular point of a cubic-density measure is genuinely null. -/
theorem root_distance_pos_ae (σ : Measure E3) (C : ℝ≥0∞) (_hC : C ≠ ⊤)
    (hdensity : ∀ x : E3, ∀ r : ℝ, 0 ≤ r →
      σ (Metric.closedBall x r) ≤ C * ENNReal.ofReal r ^ 3) (a : E3) :
    ∀ᵐ x ∂σ, 0 < ‖x - a‖ := by
  have hz : σ (Metric.closedBall a 0) = 0 := by
    have hh := hdensity a 0 le_rfl
    simpa using hh
  rw [ae_iff]
  convert hz using 1
  congr 1
  ext x
  simp only [mem_ofPred_eq, not_lt, Metric.mem_closedBall, dist_eq_norm]

/-- The full inverse-distance potential in a root line tube, including the
infinite value at the proved-null root, has every subquadratic power bound. -/
theorem affine_residual_tube_inverse_potential_le (σ : Measure E3) (C : ℝ≥0∞)
    (hC : C ≠ ⊤)
    (hdensity : ∀ x : E3, ∀ r : ℝ, 0 ≤ r →
      σ (Metric.closedBall x r) ≤ C * ENNReal.ofReal r ^ 3)
    (hunit : ∀ᵐ x ∂σ, ‖x‖ ≤ 1)
    (a q v : E3) (hroot : lineResidual a q v = 0) (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) (hε1 : ε < 1) :
    (∫⁻ x in {x | ‖lineResidual x q v‖ ≤ 2 * δ},
      (ENNReal.ofReal ‖x - a‖)⁻¹ ∂σ) ≤
      (81 * C * (1 + ENNReal.ofReal (1 / ε))) * ENNReal.ofReal (δ ^ (2 - ε)) := by
  let S : Set E3 := {x | ‖lineResidual x q v‖ ≤ 2 * δ}
  let D : ℝ≥0∞ := 81 * C * ENNReal.ofReal (δ ^ (2 - ε))
  have hS : MeasurableSet S := measurableSet_le
    (measurable_lineResidual id (fun _ => q) (fun _ => v)
      measurable_id measurable_const measurable_const).norm measurable_const
  have hD : D ≠ ⊤ := by dsimp [D]; finiteness
  have hpos : ∀ᵐ x ∂σ.restrict S, 0 < ‖x - a‖ :=
    ae_restrict_of_ae (root_distance_pos_ae σ C hC hdensity a)
  have htotal : (σ.restrict S) univ ≤ D := by
    rw [Measure.restrict_apply_univ]
    calc
      _ ≤ 81 * C * ENNReal.ofReal δ ^ 2 :=
        residual_tube_measure_le_quadratic σ id hunit C
          (fun x r hr => by simpa only [preimage_id] using hdensity x r hr) q v δ hδ
      _ ≤ D := by
        dsimp [D]
        gcongr
        rw [← ENNReal.ofReal_pow hδ.le]
        apply ENNReal.ofReal_le_ofReal
        have hh := Real.rpow_le_rpow_of_exponent_ge hδ hδ1
          (show 2 - ε ≤ (2 : ℝ) by linarith)
        simpa using hh
  have hsub (r : ℝ) (hr : 0 < r) :
      (σ.restrict S) {x | ‖x - a‖ ≤ r} ≤ D * ENNReal.ofReal (r ^ (1 + ε)) := by
    rw [Measure.restrict_apply (measurableSet_le (by fun_prop) measurable_const)]
    exact local_residual_tube_mass_le_power σ C hdensity a q v hroot δ r ε hδ hr hε hε1
  have hh := inverse_integral_le_of_power_sublevel (σ.restrict S)
    (fun x => ‖x - a‖) (by fun_prop) ε hε hε1 D hD hpos htotal hsub
  calc
    _ ≤ D * (1 + ENNReal.ofReal (1 / ε)) := hh
    _ = _ := by dsimp [D]; ring

/-- Specialization to the line through zero and the root. -/
theorem residual_tube_inverse_potential_le (σ : Measure E3) (C : ℝ≥0∞)
    (hC : C ≠ ⊤)
    (hdensity : ∀ x : E3, ∀ r : ℝ, 0 ≤ r →
      σ (Metric.closedBall x r) ≤ C * ENNReal.ofReal r ^ 3)
    (hunit : ∀ᵐ x ∂σ, ‖x‖ ≤ 1)
    (a : E3) (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) (hε1 : ε < 1) :
    (∫⁻ x in {x | ‖lineResidual x 0 a‖ ≤ 2 * δ},
      (ENNReal.ofReal ‖x - a‖)⁻¹ ∂σ) ≤
      (81 * C * (1 + ENNReal.ofReal (1 / ε))) * ENNReal.ofReal (δ ^ (2 - ε)) := by
  apply affine_residual_tube_inverse_potential_le σ C hC hdensity hunit a 0 a _ δ ε hδ hδ1 hε hε1
  simp [lineResidual, lineBase, projection_line_direction]

/-- Bounded Lebesgue density gives a root-uniform finite constant, independent
of the tube scale. In fact the proof permits every root, including zero. -/
theorem exists_uniform_line_tube_inverse_potential (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (σ : Measure E3), σ ≤ volume →
      (∀ᵐ x ∂σ, ‖x‖ ≤ 1) → ∀ (a : E3), ‖a‖ ≤ 1 →
      ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      (∫⁻ x in {x | ‖lineResidual x 0 a‖ ≤ 2 * δ},
        (ENNReal.ofReal ‖x - a‖)⁻¹ ∂σ) ≤ K * ENNReal.ofReal (δ ^ (2 - ε)) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.pi * 4 / 3)
  refine ⟨81 * C * (1 + ENNReal.ofReal (1 / ε)), by dsimp [C]; finiteness, ?_⟩
  intro σ hσ hunit a _ha δ hδ hδ1
  apply residual_tube_inverse_potential_le σ C ENNReal.ofReal_ne_top ?_
    hunit a δ ε hδ hδ1 hε hε1
  intro x r hr
  calc
    σ (Metric.closedBall x r) ≤ volume (Metric.closedBall x r) := hσ _
    _ = C * ENNReal.ofReal r ^ 3 := by
      rw [EuclideanSpace.volume_closedBall_fin_three]
      exact mul_comm _ _

/-- Every affine line has the same inverse-potential constant at every root
on that line; neither the line nor its root needs a bounded parameterization. -/
theorem exists_uniform_affine_line_tube_inverse_potential (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (σ : Measure E3), σ ≤ volume →
      (∀ᵐ x ∂σ, ‖x‖ ≤ 1) → ∀ (a q v : E3), lineResidual a q v = 0 →
      ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      (∫⁻ x in {x | ‖lineResidual x q v‖ ≤ 2 * δ},
        (ENNReal.ofReal ‖x - a‖)⁻¹ ∂σ) ≤ K * ENNReal.ofReal (δ ^ (2 - ε)) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.pi * 4 / 3)
  refine ⟨81 * C * (1 + ENNReal.ofReal (1 / ε)), by dsimp [C]; finiteness, ?_⟩
  intro σ hσ hunit a q v hroot δ hδ hδ1
  apply affine_residual_tube_inverse_potential_le σ C ENNReal.ofReal_ne_top ?_
    hunit a q v hroot δ ε hδ hδ1 hε hε1
  intro x r hr
  calc
    σ (Metric.closedBall x r) ≤ volume (Metric.closedBall x r) := hσ _
    _ = C * ENNReal.ofReal r ^ 3 := by
      rw [EuclideanSpace.volume_closedBall_fin_three]
      exact mul_comm _ _

end StickyKakeya4.LineTubeInversePotential
