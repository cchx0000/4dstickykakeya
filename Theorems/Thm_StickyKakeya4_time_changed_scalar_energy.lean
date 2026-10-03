import Theorems.Thm_StickyKakeya4_parameterized_scalar_potential

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4.ScalarProjection

/-- Scalar sublevels against an arbitrary finite parameter law with linear ball growth. -/
theorem parameter_fiber_linear_le
    (ν : Measure ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hgrowth : ∀ c r : ℝ, 0 < r → ν (Metric.ball c r) ≤
      ENNReal.ofReal K * ENNReal.ofReal r)
    (u v r : ℝ) (hv : v ≠ 0) (hr : 0 < r) :
    ν {t : ℝ | |u+t*v| ≤ r} ≤ ENNReal.ofReal (2*K*(r/|v|)) := by
  have hav : 0 < |v| := abs_pos.mpr hv
  calc
    _ ≤ ν (Metric.ball (-u/v) (2*r/|v|)) := by
      apply measure_mono
      intro t ht
      rw [Metric.mem_ball, Real.dist_eq]
      have he : t-(-u/v) = (u+t*v)/v := by field_simp; ring
      rw [he, abs_div]
      exact (div_le_div_of_nonneg_right ht hav.le).trans_lt (by
        apply (div_lt_div_iff_of_pos_right hav).2
        linarith)
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (2*r/|v|) :=
      hgrowth _ _ (div_pos (by positivity) hav)
    _ = _ := by
      rw [← ENNReal.ofReal_mul hK]
      congr 1
      ring

/-- Interpolation of finite total mass with a linear parameter-fibre estimate. -/
theorem parameter_min_linear_le_fractional
    (L K z q : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hz : 0 < z) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    min L (2*K*z) ≤ (L+2*K)*z^q := by
  by_cases hz1 : z ≤ 1
  · have hp : z ≤ z^q := Real.self_le_rpow_of_le_one hz.le hz1 hq1
    calc
      min L (2*K*z) ≤ 2*K*z := min_le_right _ _
      _ ≤ 2*K*z^q := by gcongr
      _ ≤ (L+2*K)*z^q := by gcongr; linarith
  · have hp : 1 ≤ z^q := Real.one_le_rpow (le_of_not_ge hz1) hq
    calc
      min L (2*K*z) ≤ L := min_le_left _ _
      _ ≤ (L+2*K)*z^q := by nlinarith

/-- The arbitrary parameter law retains the inverse source-distance factor. -/
theorem parameter_fiber_fractional_le
    (ν : Measure ℝ) [IsFiniteMeasure ν] (K : ℝ) (hK : 0 ≤ K)
    (hgrowth : ∀ c r : ℝ, 0 < r → ν (Metric.ball c r) ≤
      ENNReal.ofReal K * ENNReal.ofReal r)
    (u v r q : ℝ) (hv : v ≠ 0) (hr : 0 < r)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ν {t : ℝ | |u+t*v| ≤ r} ≤
      ENNReal.ofReal (((ν univ).toReal+2*K)*r^q) *
        (ENNReal.ofReal |v|)^(-q) := by
  have hav : 0 < |v| := abs_pos.mpr hv
  have hsmall : ν {t : ℝ | |u+t*v| ≤ r} ≤ ENNReal.ofReal (ν univ).toReal := by
    rw [ENNReal.ofReal_toReal (measure_ne_top ν univ)]
    exact measure_mono (subset_univ _)
  calc
    _ ≤ min (ENNReal.ofReal (ν univ).toReal)
        (ENNReal.ofReal (2*K*(r/|v|))) :=
      le_min hsmall (parameter_fiber_linear_le ν K hK hgrowth u v r hv hr)
    _ = ENNReal.ofReal (min (ν univ).toReal (2*K*(r/|v|))) := by
      rw [ENNReal.ofReal_min]
    _ ≤ ENNReal.ofReal (((ν univ).toReal+2*K)*(r/|v|)^q) :=
      ENNReal.ofReal_le_ofReal
        (parameter_min_linear_le_fractional _ K (r/|v|) q (by positivity) hK
          (div_pos hr hav) hq hq1)
    _ = _ := by
      rw [Real.div_rpow hr.le hav.le, div_eq_mul_inv, ← Real.rpow_neg hav.le]
      rw [ENNReal.ofReal_rpow_of_pos hav, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

theorem parameter_averaged_collision_le_source_energy
    (ν μ : Measure ℝ) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (K : ℝ) (hK : 0 ≤ K)
    (hgrowth : ∀ c r : ℝ, 0 < r → ν (Metric.ball c r) ≤
      ENNReal.ofReal K * ENNReal.ofReal r)
    (f : ℝ → ℝ) (hf : Measurable f) (r q : ℝ)
    (hr : 0 < r) (hq : 0 < q) (hq1 : q < 1)
    (hdiag : (μ.prod μ) {p : ℝ × ℝ | p.1=p.2} = 0) :
    (ν.prod (μ.prod μ)) {p : ℝ × (ℝ × ℝ) |
      |(f p.2.1-f p.2.2)+p.1*(p.2.1-p.2.2)| ≤ r} ≤
      ENNReal.ofReal (((ν univ).toReal+2*K)*r^q) *
        ∫⁻ p : ℝ × ℝ, (ENNReal.ofReal |p.1-p.2|)^(-q) ∂μ.prod μ := by
  have hm : MeasurableSet {p : ℝ × (ℝ × ℝ) |
      |(f p.2.1-f p.2.2)+p.1*(p.2.1-p.2.2)| ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  have hne : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, p.1 ≠ p.2 := by
    simpa only [ae_iff, not_not] using hdiag
  rw [Measure.prod_apply_symm hm]
  calc
    _ ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (((ν univ).toReal+2*K)*r^q) *
        (ENNReal.ofReal |p.1-p.2|)^(-q) ∂μ.prod μ := by
      apply lintegral_mono_ae
      filter_upwards [hne] with p hp
      exact parameter_fiber_fractional_le ν K hK hgrowth
        (f p.1-f p.2) (p.1-p.2) r q (sub_ne_zero.mpr hp) hr hq.le hq1.le
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Finite averaged scalar energy follows from source density and parameter growth alone. -/
theorem finite_parameter_average_scalar_projection_pair_energy
    (ν μ : Measure ℝ) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (K : ℝ) (hK : 0 ≤ K)
    (hgrowth : ∀ c r : ℝ, 0 < r → ν (Metric.ball c r) ≤
      ENNReal.ofReal K * ENNReal.ofReal r)
    (D : ℝ) (hD : 0 ≤ D) (hμ : μ ≤ ENNReal.ofReal D • volume)
    (f : ℝ → ℝ) (hf : Measurable f) (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (∫⁻ p : ℝ × (ℝ × ℝ),
      (ENNReal.ofReal |(f p.2.1-f p.2.2)+p.1*(p.2.1-p.2.2)|)^(-s)
        ∂ν.prod (μ.prod μ)) < ∞ := by
  let q : ℝ := (s+1)/2
  have hsq : s < q := by dsimp [q]; linarith
  have hq : 0 < q := hs.trans hsq
  have hq1 : q < 1 := by dsimp [q]; linarith
  let E : ℝ≥0∞ := ∫⁻ p : ℝ × ℝ,
    (ENNReal.ofReal |p.1-p.2|)^(-q) ∂μ.prod μ
  have hE : E < ∞ := finite_source_pair_energy μ D hD hμ q hq hq1
  apply finite_inverse_energy_of_sublevel_power (ν.prod (μ.prod μ))
    (fun p : ℝ × (ℝ × ℝ) => |(f p.2.1-f p.2.2)+p.1*(p.2.1-p.2.2)|)
    (by fun_prop) (fun _ => abs_nonneg _) (((ν univ).toReal+2*K)*E.toReal) q s
    (by positivity) hs hsq
  intro r hr _
  calc
    _ ≤ ENNReal.ofReal (((ν univ).toReal+2*K)*r^q) * E :=
      parameter_averaged_collision_le_source_energy ν μ K hK hgrowth f hf r q hr hq hq1
        (source_pair_diagonal_null μ D hD hμ)
    _ = ENNReal.ofReal ((((ν univ).toReal+2*K)*E.toReal)*r^q) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hE.ne]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

theorem ae_finite_parameter_scalar_projection_pair_energy
    (ν μ : Measure ℝ) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (K : ℝ) (hK : 0 ≤ K)
    (hgrowth : ∀ c r : ℝ, 0 < r → ν (Metric.ball c r) ≤
      ENNReal.ofReal K * ENNReal.ofReal r)
    (D : ℝ) (hD : 0 ≤ D) (hμ : μ ≤ ENNReal.ofReal D • volume)
    (f : ℝ → ℝ) (hf : Measurable f) (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∀ᵐ t ∂ν, (∫⁻ p : ℝ × ℝ,
      (ENNReal.ofReal |(f p.1-f p.2)+t*(p.1-p.2)|)^(-s) ∂μ.prod μ) < ∞ := by
  exact ae_finite_fiber_inverse_energy_of_finite_product_energy
    ν (μ.prod μ) _ (by fun_prop) s
    (finite_parameter_average_scalar_projection_pair_energy
      ν μ K hK hgrowth D hD hμ f hf s hs hs1)


/-- A co-Lipschitz change of actual time has a linearly bounded parameter law.
The law is the literal pushforward of restricted Lebesgue measure, without normalization. -/
theorem time_change_map_ball_le
    (ρ : ℝ → ℝ) (hρ : Measurable ρ) (l h c : ℝ) (hc : 0 < c)
    (hco : ∀ t ∈ Icc l h, ∀ u ∈ Icc l h, c*|t-u| ≤ |ρ t-ρ u|)
    (y r : ℝ) (_hr : 0 < r) :
    ((volume.restrict (Icc l h)).map ρ) (Metric.ball y r) ≤
      ENNReal.ofReal (4/c) * ENNReal.ofReal r := by
  rw [Measure.map_apply hρ Metric.isOpen_ball.measurableSet,
    Measure.restrict_apply' measurableSet_Icc]
  by_cases hne : (ρ ⁻¹' Metric.ball y r ∩ Icc l h).Nonempty
  · obtain ⟨u, hu, hui⟩ := hne
    have hsub : ρ ⁻¹' Metric.ball y r ∩ Icc l h ⊆ Metric.ball u (2*r/c) := by
      intro t ht
      rcases ht with ⟨ht, hti⟩
      rw [Metric.mem_ball, Real.dist_eq]
      apply (lt_div_iff₀ hc).2
      have ht' : |ρ t-y| < r := by simpa [Metric.mem_ball, Real.dist_eq] using ht
      have hu' : |ρ u-y| < r := by simpa [Metric.mem_ball, Real.dist_eq] using hu
      have htri : |ρ t-ρ u| ≤ |ρ t-y|+|ρ u-y| := by
        simpa [abs_sub_comm] using (abs_sub_le (ρ t) y (ρ u))
      calc
        |t-u| * c = c*|t-u| := mul_comm _ _
        _ ≤ |ρ t-ρ u| := hco t hti u hui
        _ ≤ |ρ t-y|+|ρ u-y| := htri
        _ < r+r := add_lt_add ht' hu'
        _ = 2*r := by ring
    calc
      _ ≤ volume (Metric.ball u (2*r/c)) := measure_mono hsub
      _ = ENNReal.ofReal (4/c) * ENNReal.ofReal r := by
        rw [Real.volume_ball, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
    exact zero_le

variable {Z : Type*} [MeasurableSpace Z]

/-- Every fixed source parameter has finite native potential integral for almost every
value of any finite linearly bounded parameter law. -/
theorem ae_finite_parameter_law_potential_integral
    (ν μ : Measure ℝ) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (K : ℝ) (hK : 0 ≤ K)
    (hgrowth : ∀ c r : ℝ, 0 < r → ν (Metric.ball c r) ≤
      ENNReal.ofReal K * ENNReal.ofReal r)
    (D : ℝ) (hD : 0 ≤ D) (hμ : μ ≤ ENNReal.ofReal D • volume)
    (f : Z × ℝ → ℝ) (hf : Measurable f) (s : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (z : Z) :
    ∀ᵐ t ∂ν, (∫⁻ a, parameterizedScalarPotential μ f s (t,(z,a)) ∂μ) < ∞ := by
  have hz : Measurable (fun a => f (z,a)) := by fun_prop
  filter_upwards [ae_finite_parameter_scalar_projection_pair_energy
    ν μ K hK hgrowth D hD hμ (fun a => f (z,a)) hz s hs hs1] with t ht
  rw [parameterizedScalarPotential_integral_eq_pair_energy μ f hf s t z]
  exact ht

/-- Joint native potential finiteness for any finite linearly bounded parameter law. -/
theorem ae_finite_parameter_law_potential
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (ζ : Measure Z) [IsFiniteMeasure ζ]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (K : ℝ) (hK : 0 ≤ K)
    (hgrowth : ∀ c r : ℝ, 0 < r → ν (Metric.ball c r) ≤
      ENNReal.ofReal K * ENNReal.ofReal r)
    (D : ℝ) (hD : 0 ≤ D) (hμ : μ ≤ ENNReal.ofReal D • volume)
    (f : Z × ℝ → ℝ) (hf : Measurable f) (s : ℝ)
    (hs : 0 < s) (hs1 : s < 1) :
    ∀ᵐ p ∂ν.prod (ζ.prod μ), parameterizedScalarPotential μ f s p < ∞ := by
  let Q : ℝ × Z → ℝ≥0∞ := fun p =>
    ∫⁻ a, parameterizedScalarPotential μ f s (p.1,(p.2,a)) ∂μ
  have hP := measurable_parameterizedScalarPotential μ f hf s
  have hQ : Measurable Q := by
    have hm : Measurable (fun p : (ℝ × Z) × ℝ =>
        parameterizedScalarPotential μ f s (p.1.1,(p.1.2,p.2))) :=
      hP.comp (by fun_prop)
    exact hm.lintegral_prod_right'
  have hzt : ∀ᵐ z ∂ζ, ∀ᵐ t ∂ν, Q (t,z) < ∞ :=
    ae_of_all _ (fun z => ae_finite_parameter_law_potential_integral
      ν μ K hK hgrowth D hD hμ f hf s hs hs1 z)
  have htz : ∀ᵐ t ∂ν, ∀ᵐ z ∂ζ, Q (t,z) < ∞ :=
    (Measure.ae_ae_comm (μ := ζ) (ν := ν)
      (p := fun z t => Q (t,z) < ∞)
      (measurableSet_lt (hQ.comp measurable_swap) measurable_const)).mp hzt
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hP measurable_const)).mpr
  filter_upwards [htz] with t ht
  have hPt : Measurable (fun p : Z × ℝ => parameterizedScalarPotential μ f s (t,p)) :=
    hP.comp (by fun_prop)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hPt measurable_const)).mpr
  filter_upwards [ht] with z hz
  apply ae_lt_top (hP.comp (show Measurable (fun a : ℝ => (t,(z,a))) by fun_prop))
  exact hz.ne

/-- Actual-time change of a parameterized Borel scalar family retains native
potential finiteness on the original time × parameter × source measure. -/
theorem ae_finite_time_changed_parameterizedScalarPotential
    (ζ : Measure Z) [IsFiniteMeasure ζ]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (D : ℝ) (hD : 0 ≤ D) (hμ : μ ≤ ENNReal.ofReal D • volume)
    (f : Z × ℝ → ℝ) (hf : Measurable f)
    (ρ : ℝ → ℝ) (hρ : Measurable ρ) (l h c : ℝ) (hc : 0 < c)
    (hco : ∀ t ∈ Icc l h, ∀ u ∈ Icc l h, c*|t-u| ≤ |ρ t-ρ u|)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∀ᵐ p ∂(volume.restrict (Icc l h)).prod (ζ.prod μ),
      parameterizedScalarPotential μ f s (ρ p.1,p.2) < ∞ := by
  let ν := (volume.restrict (Icc l h)).map ρ
  have hfin := ae_finite_parameter_law_potential ν ζ μ (4/c) (by positivity)
    (time_change_map_ball_le ρ hρ l h c hc hco)
    D hD hμ f hf s hs hs1
  have hP := measurable_parameterizedScalarPotential μ f hf s
  have hiter : ∀ᵐ t ∂ν, ∀ᵐ za ∂ζ.prod μ,
      parameterizedScalarPotential μ f s (t,za) < ∞ :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_lt hP measurable_const)).mp hfin
  have hpull : ∀ᵐ t ∂volume.restrict (Icc l h), ∀ᵐ za ∂ζ.prod μ,
      parameterizedScalarPotential μ f s (ρ t,za) < ∞ :=
    ae_of_ae_map hρ.aemeasurable hiter
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt
    (hP.comp (show Measurable (fun p : ℝ × (Z × ℝ) => (ρ p.1,p.2)) by fun_prop))
    measurable_const)).mpr
  exact hpull

/-- The unparameterized native potential is finite on the original time × source,
with no normalized time-change law and no assumed energy bound. -/
theorem ae_finite_time_changed_scalar_potential
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (D : ℝ) (hD : 0 ≤ D) (hμ : μ ≤ ENNReal.ofReal D • volume)
    (f : ℝ → ℝ) (hf : Measurable f)
    (ρ : ℝ → ℝ) (hρ : Measurable ρ) (l h c : ℝ) (hc : 0 < c)
    (hco : ∀ t ∈ Icc l h, ∀ u ∈ Icc l h, c*|t-u| ≤ |ρ t-ρ u|)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∀ᵐ p ∂(volume.restrict (Icc l h)).prod μ,
      (∫⁻ a', edist (f p.2+ρ p.1*p.2) (f a'+ρ p.1*a')^(-s) ∂μ) < ∞ := by
  let ν := (volume.restrict (Icc l h)).map ρ
  have hfin := ae_finite_parameter_scalar_projection_pair_energy
    ν μ (4/c) (by positivity) (time_change_map_ball_le ρ hρ l h c hc hco)
    D hD hμ f hf s hs hs1
  have hpull : ∀ᵐ t ∂volume.restrict (Icc l h),
      (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal |(f p.1-f p.2)+ρ t*(p.1-p.2)|)^(-s)
        ∂μ.prod μ) < ∞ := ae_of_ae_map hρ.aemeasurable hfin
  have hP : Measurable (fun p : ℝ × ℝ =>
      ∫⁻ a', edist (f p.2+ρ p.1*p.2) (f a'+ρ p.1*a')^(-s) ∂μ) := by
    have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      edist (f p.1.2+ρ p.1.1*p.1.2) (f p.2+ρ p.1.1*p.2)^(-s)) := by fun_prop
    exact hm.lintegral_prod_right'
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hP measurable_const)).mpr
  filter_upwards [hpull] with t ht
  apply ae_lt_top (hP.comp (show Measurable (fun a : ℝ => (t,a)) by fun_prop))
  have he : (∫⁻ a, (∫⁻ a', edist (f a+ρ t*a) (f a'+ρ t*a')^(-s) ∂μ) ∂μ) =
      ∫⁻ p : ℝ × ℝ,
        (ENNReal.ofReal |(f p.1-f p.2)+ρ t*(p.1-p.2)|)^(-s) ∂μ.prod μ := by
    rw [lintegral_prod _ (by fun_prop)]
    apply lintegral_congr
    intro a
    apply lintegral_congr
    intro a'
    have he : (f a+ρ t*a)-(f a'+ρ t*a') = (f a-f a')+ρ t*(a-a') := by ring
    rw [edist_dist, Real.dist_eq, he]
  change (∫⁻ a, (∫⁻ a', edist (f a+ρ t*a) (f a'+ρ t*a')^(-s) ∂μ) ∂μ) ≠ ∞
  exact (he ▸ ht).ne

end StickyKakeya4.ScalarProjection
