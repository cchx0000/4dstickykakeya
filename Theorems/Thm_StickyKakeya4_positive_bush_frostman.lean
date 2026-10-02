import Theorems.Thm_StickyKakeya4_original_residual_criterion
import Theorems.Thm_StickyKakeya4_actual_slope_source_bounds
import Mathlib.Topology.MetricSpace.Sequences

/-!
# A positive physical bush is a genuine Frostman exit

An exact physical bush means that a positive actual slope source passes through
one common spacetime point. On a time interval separated from that point, its
transverse displacement is exactly a nonzero scalar multiple of the slope
displacement. Bounded Lebesgue density supplies cubic collision sublevels;
the proved spacetime-energy and supported-Frostman bridges give dimension four
on the original physical front. The shrinking-bush extension requires one
fixed positive lower mass for every individual bush; it does not assert the
full family/vector-Frostman statement of manuscript Theorem 8.11.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4.PositiveBush

/-- Every nondegenerate interval contains a nondegenerate subinterval a
uniform positive distance from any specified bush time. -/
theorem exists_separated_subinterval (u v s₀ : ℝ) (huv : u < v) :
    ∃ l h d : ℝ, l < h ∧ 0 < d ∧ Icc l h ⊆ Icc u v ∧
      ∀ s ∈ Icc l h, d ≤ |s - s₀| := by
  by_cases hc : s₀ ≤ (u + v) / 2
  · refine ⟨(u + 3 * v) / 4, v, (v - u) / 4, by linarith, by linarith, ?_, ?_⟩
    · intro s hs; exact ⟨by linarith [hs.1], hs.2⟩
    · intro s hs
      exact (show (v - u) / 4 ≤ s - s₀ by linarith [hs.1]).trans (le_abs_self _)
  · refine ⟨u, (3 * u + v) / 4, (v - u) / 4, by linarith, by linarith, ?_, ?_⟩
    · intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩
    · intro s hs
      have hc' : (u + v) / 2 < s₀ := lt_of_not_ge hc
      exact (show (v - u) / 4 ≤ -(s - s₀) by linarith [hs.2]).trans (neg_le_abs _)

/-- Two lines through the same physical bush point have an exact scalar
slope-displacement formula at every other time. -/
theorem exact_bush_displacement (b : E3 → E3) (s₀ s : ℝ) (c a a' : E3)
    (ha : b a + s₀ • a = c) (ha' : b a' + s₀ • a' = c) :
    (b a - b a') + s • (a - a') = (s - s₀) • (a - a') := by
  have hba : b a = c - s₀ • a := eq_sub_of_add_eq ha
  have hba' : b a' = c - s₀ • a' := eq_sub_of_add_eq ha'
  rw [hba, hba']
  module

/-- The actual exact-bush source has cubic same-time collision sublevels
away from the bush time, including the original ordered endpoint pairs. -/
theorem exact_bush_collision_mass_le_cubic
    (σ : Measure E3) [SFinite σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (s₀ s d r : ℝ) (c : E3)
    (hd : 0 < d) (hsep : d ≤ |s - s₀|)
    (hbush : ∀ᵐ a ∂σ, b a + s₀ • a = c) :
    (σ.prod σ) {p : E3 × E3 | ‖(b p.1 - b p.2) + s • (p.1 - p.2)‖ ≤ r} ≤
      (ENNReal.ofReal (Real.pi * 4 / 3) * σ univ) * ENNReal.ofReal (r / d) ^ 3 := by
  have hm : MeasurableSet {a : E3 | b a + s₀ • a = c} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hpair : ∀ᵐ p ∂σ.prod σ,
      b p.1 + s₀ • p.1 = c ∧ b p.2 + s₀ • p.2 = c := by
    apply (Measure.ae_prod_iff_ae_ae ((hm.preimage measurable_fst).inter
      (hm.preimage measurable_snd))).2
    exact hbush.mono (fun a ha => hbush.mono (fun a' ha' => ⟨ha, ha'⟩))
  calc
    _ ≤ (σ.prod σ) {p : E3 × E3 | ‖p.1 - p.2‖ ≤ r / d} := by
      apply measure_mono_ae
      filter_upwards [hpair] with p hp
      intro hcollision
      change ‖(b p.1 - b p.2) + s • (p.1 - p.2)‖ ≤ r at hcollision
      rw [exact_bush_displacement b s₀ s c p.1 p.2 hp.1 hp.2,
        norm_smul, Real.norm_eq_abs] at hcollision
      change ‖p.1 - p.2‖ ≤ r / d
      apply (le_div_iff₀ hd).2
      calc
        ‖p.1 - p.2‖ * d ≤ |s - s₀| * ‖p.1 - p.2‖ := by nlinarith [norm_nonneg (p.1 - p.2)]
        _ ≤ r := hcollision
    _ ≤ _ := by
      simpa using slope_pair_near_mass_le_cubic σ 1 (by simpa using hσ) (r / d)

/-- The positive time separation makes the averaged cubic constant finite,
uniformly over all positive collision radii. -/
theorem exact_bush_averaged_collision_power
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (s₀ u v d : ℝ) (c : E3)
    (hd : 0 < d) (hsep : ∀ s ∈ Icc u v, d ≤ |s - s₀|)
    (hbush : ∀ᵐ a ∂σ, b a + s₀ • a = c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r < 1 →
      (∫⁻ s in Icc u v, (σ.prod σ)
        {p : E3 × E3 | ‖(b p.1 - b p.2) + s • (p.1 - p.2)‖ ≤ r}) ≤
          ENNReal.ofReal (C * r ^ (3 : ℝ)) := by
  let K : ℝ≥0∞ := ENNReal.ofReal (v - u) *
    (ENNReal.ofReal (Real.pi * 4 / 3) * σ univ) * (ENNReal.ofReal d)⁻¹ ^ 3
  have hd0 : ENNReal.ofReal d ≠ 0 := by simp [hd.not_ge]
  have hK : K ≠ ⊤ := by dsimp [K]; finiteness
  refine ⟨K.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro r hr _
  calc
    _ ≤ ∫⁻ _s in Icc u v,
        (ENNReal.ofReal (Real.pi * 4 / 3) * σ univ) * ENNReal.ofReal (r / d) ^ 3 := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact exact_bush_collision_mass_le_cubic σ hσ b hb s₀ s d r c hd (hsep s hs) hbush
    _ = K * ENNReal.ofReal r ^ 3 := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
        ENNReal.ofReal_div_of_pos hd]
      dsimp [K]
      simp only [div_eq_mul_inv, mul_pow]
      ring
    _ = ENNReal.ofReal (K.toReal * r ^ (3 : ℝ)) := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hK, ← ENNReal.ofReal_rpow_of_pos hr]
      rw [ENNReal.rpow_ofNat]

/-- A genuinely positive exact bush produces Frostman probabilities on the
original physical front. No residual estimate or routing certificate is assumed. -/
theorem front_frostman_of_positive_exact_bush
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ) (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v s₀ : ℝ) (huv : u < v) (c : E3)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hbush : ∀ᵐ a ∂σ, b a + s₀ • a = c) :
    HasFrontFrostmanMeasures ambient := by
  obtain ⟨l, h, d, hlh, hd, hsub, hsep⟩ := exists_separated_subinterval u v s₀ huv
  obtain ⟨C, hC, hpower⟩ := exact_bush_averaged_collision_power σ hσ b hb s₀ l h d c hd hsep hbush
  have hsupported : ∀ᵐ a ∂σ, ∀ s ∈ Icc l h,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient :=
    hsupport.mono (fun a ha s hs => ha s (hsub hs))
  apply EnergyDimension.hasFrontFrostmanMeasures_of_supported_finite_energies
  intro ε hε hε4
  refine ⟨OriginalResidualCriterion.sourceFrontMeasure σ b l h, inferInstance,
    OriginalResidualCriterion.sourceFrontMeasure_ne_zero σ hσpos b hb l h hlh,
    OriginalResidualCriterion.sourceFrontMeasure_supported σ b hb l h _
      (StickyKakeya4.IsCompact.unitFront hcompact).measurableSet hsupported, ?_⟩
  exact finite_spacetime_front_energy_of_averaged_sublevel_power σ b hb
    l h 1 C 3 (4 - ε) (by norm_num) hslopes hC (by norm_num)
      (by linarith) (by linarith) hpower

/-- The full dimension conclusion for a positive exact physical bush. -/
theorem front_dimH_eq_four_of_positive_exact_bush
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ) (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v s₀ : ℝ) (huv : u < v) (c : E3)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hbush : ∀ᵐ a ∂σ, b a + s₀ • a = c) :
    dimH (unitFront ambient) = 4 := by
  apply le_antisymm
  · calc
      dimH (unitFront ambient) ≤ dimH (univ : Set E4) := dimH_mono (subset_univ _)
      _ = 4 := by simp [E4, Real.dimH_univ_eq_finrank]
  · exact dimH_ge_four_of_front_frostman_measures ambient
      (front_frostman_of_positive_exact_bush ambient hcompact σ hσpos hσ b hb hslopes
        u v s₀ huv c hsupport hbush)

/-- Positive mass of the exact-bush set suffices; the other slopes are simply
restricted away, without renormalizing the source-density bound. -/
theorem front_frostman_of_positive_exact_bush_piece
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v s₀ : ℝ) (huv : u < v) (c : E3)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hbush : 0 < σ {a | b a + s₀ • a = c}) :
    HasFrontFrostmanMeasures ambient := by
  let G : Set E3 := {a | b a + s₀ • a = c}
  have hG : MeasurableSet G := measurableSet_eq_fun (by fun_prop) measurable_const
  apply front_frostman_of_positive_exact_bush ambient hcompact (σ.restrict G)
    (by simpa only [Measure.restrict_apply_univ] using hbush)
    (Measure.restrict_le_self.trans hσ) b hb (ae_restrict_of_ae hslopes)
    u v s₀ huv c (ae_restrict_of_ae hsupport)
  exact ae_restrict_mem hG

/-- The positive-piece exact-bush exit has full front dimension. -/
theorem front_dimH_eq_four_of_positive_exact_bush_piece
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v s₀ : ℝ) (huv : u < v) (c : E3)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hbush : 0 < σ {a | b a + s₀ • a = c}) :
    dimH (unitFront ambient) = 4 := by
  apply le_antisymm
  · calc
      dimH (unitFront ambient) ≤ dimH (univ : Set E4) := dimH_mono (subset_univ _)
      _ = 4 := by simp [E4, Real.dimH_univ_eq_finrank]
  · exact dimH_ge_four_of_front_frostman_measures ambient
      (front_frostman_of_positive_exact_bush_piece ambient hcompact σ hσ b hb hslopes
        u v s₀ huv c hsupport hbush)

/-- Uniformly positive mass of individual approximate bushes survives a
convergent sequence of centers and times as an exact bush in the original
source. This is continuity from above for one fixed finite measure, not a
weak-limit support assertion. -/
theorem exact_bush_mass_ge_of_convergent_approximate_bushes
    (σ : Measure E3) [IsFiniteMeasure σ]
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (s : ℕ → ℝ) (c : ℕ → E3) (R : ℕ → ℝ) (s₀ : ℝ) (c₀ : E3)
    (hs : Tendsto s atTop (𝓝 s₀)) (hc : Tendsto c atTop (𝓝 c₀))
    (hR : Tendsto R atTop (𝓝 0)) (p : ℝ≥0∞)
    (hmass : ∀ n, p ≤ σ {a | ‖b a + s n • a - c n‖ ≤ R n}) :
    p ≤ σ {a | b a + s₀ • a = c₀} := by
  let E : ℝ → Set E3 := fun r => {a | ‖b a + s₀ • a - c₀‖ ≤ r}
  have hE (r : ℝ) : MeasurableSet (E r) := measurableSet_le (by fun_prop) measurable_const
  have herror : Tendsto (fun n => R n + |s₀ - s n| + ‖c n - c₀‖) atTop (𝓝 0) := by
    convert (hR.add ((tendsto_const_nhds.sub hs).abs)).add
      ((hc.sub tendsto_const_nhds).norm) using 1 <;> simp
  have hbound : ∀ r : ℝ, 0 < r → p ≤ σ (E r) := by
    intro r hr
    obtain ⟨n, hn⟩ := ((tendsto_order.mp herror).2 r hr).exists
    apply (hmass n).trans
    apply measure_mono_ae
    filter_upwards [hslopes] with a ha
    intro hnear
    change ‖b a + s₀ • a - c₀‖ ≤ r
    change ‖b a + s n • a - c n‖ ≤ R n at hnear
    have halg : b a + s₀ • a - c₀ =
        (b a + s n • a - c n) + (s₀ - s n) • a + (c n - c₀) := by module
    calc
      ‖b a + s₀ • a - c₀‖ ≤ ‖b a + s n • a - c n‖ +
          ‖(s₀ - s n) • a‖ + ‖c n - c₀‖ := by
        rw [halg]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ R n + |s₀ - s n| + ‖c n - c₀‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        gcongr
        exact mul_le_of_le_one_right (abs_nonneg _) ha
      _ ≤ r := hn.le
  have hinter : (⋂ r > (0 : ℝ), E r) = {a | b a + s₀ • a = c₀} := by
    ext a
    simp only [mem_iInter, E, mem_ofPred_eq]
    constructor
    · intro ha
      by_contra hne
      have hn : 0 < ‖b a + s₀ • a - c₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have hh := ha (‖b a + s₀ • a - c₀‖ / 2) (by positivity)
      linarith
    · intro ha r hr
      simp only [ha, sub_self, norm_zero]
      exact hr.le
  have hlim := tendsto_measure_biInter_gt (μ := σ) (a := (0 : ℝ))
    (s := E) (fun r _ => (hE r).nullMeasurableSet)
    (fun i j _ hij a ha => ha.trans hij)
    ⟨1, by norm_num, measure_ne_top σ (E 1)⟩
  rw [hinter] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hbound r hr

/-- Positive individual bushes have uniformly bounded centers when the
original slopes, intercepts, times and radii are bounded. -/
theorem approximate_bush_center_bound
    (σ : Measure E3) (b : E3 → E3)
    (B S s R : ℝ) (c : E3)
    (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1) (hb : ∀ᵐ a ∂σ, ‖b a‖ ≤ B)
    (hs : |s| ≤ S) (hmass : 0 < σ {a | ‖b a + s • a - c‖ ≤ R}) :
    ‖c‖ ≤ B + S + R := by
  obtain ⟨a, ha, hsa, hba⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmass.ne'
    (ae_restrict_of_ae (hslopes.and hb))
  change ‖b a + s • a - c‖ ≤ R at ha
  have heq : c = (b a + s • a) - (b a + s • a - c) := by module
  calc
    ‖c‖ ≤ ‖b a‖ + ‖s • a‖ + ‖b a + s • a - c‖ := by
      conv_lhs => rw [heq]
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ B + S + R := by
      rw [norm_smul, Real.norm_eq_abs]
      have hm : |s| * ‖a‖ ≤ S := (mul_le_of_le_one_right (abs_nonneg _) hsa).trans hs
      linarith

/-- Fixed positive mass of each shrinking physical bush yields a positive
exact bush after compactness. A positive total mass spread over individually
vanishing bushes does not satisfy the explicit uniform lower bound here. -/
theorem exists_positive_exact_bush_of_shrinking_bushes
    (σ : Measure E3) [IsFiniteMeasure σ]
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (B S : ℝ) (hbound : ∀ᵐ a ∂σ, ‖b a‖ ≤ B)
    (s : ℕ → ℝ) (c : ℕ → E3) (R : ℕ → ℝ)
    (hs : ∀ n, |s n| ≤ S) (hR : Tendsto R atTop (𝓝 0))
    (p : ℝ≥0∞) (hp : 0 < p)
    (hmass : ∀ n, p ≤ σ {a | ‖b a + s n • a - c n‖ ≤ R n}) :
    ∃ s₀ : ℝ, ∃ c₀ : E3, p ≤ σ {a | b a + s₀ • a = c₀} := by
  obtain ⟨M, hM⟩ := hR.bddAbove_range
  have hcenters (n : ℕ) : ‖c n‖ ≤ B + S + M := by
    have hn := approximate_bush_center_bound σ b B S (s n) (R n) (c n)
      hslopes hbound (hs n) (hp.trans_le (hmass n))
    exact hn.trans (by linarith [hM (mem_range_self n)])
  have hcompact := (isCompact_closedBall (0 : ℝ) S).prod
    (isCompact_closedBall (0 : E3) (B + S + M))
  obtain ⟨z, hz, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (x := fun n => (s n, c n)) (fun n => by
      constructor
      · simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hs n
      · simpa only [Metric.mem_closedBall, dist_zero_right] using hcenters n)
  refine ⟨z.1, z.2, ?_⟩
  apply exact_bush_mass_ge_of_convergent_approximate_bushes σ b hb hslopes
    (s ∘ φ) (c ∘ φ) (R ∘ φ) z.1 z.2
    (continuous_fst.tendsto z |>.comp hlim)
    (continuous_snd.tendsto z |>.comp hlim)
    (hR.comp hφ.tendsto_atTop) p
  exact fun n => hmass (φ n)

/-- A uniformly nonvanishing sequence of individual shrinking bushes is a
proved Frostman exit on the same compact physical front. -/
theorem front_frostman_of_shrinking_positive_bushes_of_bounded_intercept
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v : ℝ) (huv : u < v)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (B S : ℝ) (hbound : ∀ᵐ a ∂σ, ‖b a‖ ≤ B)
    (s : ℕ → ℝ) (c : ℕ → E3) (R : ℕ → ℝ)
    (hs : ∀ n, |s n| ≤ S) (hR : Tendsto R atTop (𝓝 0))
    (p : ℝ≥0∞) (hp : 0 < p)
    (hmass : ∀ n, p ≤ σ {a | ‖b a + s n • a - c n‖ ≤ R n}) :
    HasFrontFrostmanMeasures ambient := by
  obtain ⟨s₀, c₀, hmass₀⟩ := exists_positive_exact_bush_of_shrinking_bushes
    σ b hb hslopes B S hbound s c R hs hR p hp hmass
  exact front_frostman_of_positive_exact_bush_piece ambient hcompact σ hσ b hb hslopes
    u v s₀ huv c₀ hsupport (hp.trans_le hmass₀)

/-- Compact physical support supplies the intercept bound, so only bounded
times and one fixed positive lower bound for each individual shrinking bush
are needed for this actual-source Frostman exit. -/
theorem front_frostman_of_shrinking_positive_bushes
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v : ℝ) (huv : u < v)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (S : ℝ) (s : ℕ → ℝ) (c : ℕ → E3) (R : ℕ → ℝ)
    (hs : ∀ n, |s n| ≤ S) (hR : Tendsto R atTop (𝓝 0))
    (p : ℝ≥0∞) (hp : 0 < p)
    (hmass : ∀ n, p ≤ σ {a | ‖b a + s n • a - c n‖ ≤ R n}) :
    HasFrontFrostmanMeasures ambient := by
  have hatu : ∀ᵐ a ∂σ,
      ActualSlopeSource.heightPoint (b a + u • a) u ∈ unitFront ambient :=
    hsupport.mono (fun a ha => ha u ⟨le_rfl, huv.le⟩)
  obtain ⟨B, hB0, hbound⟩ := ActualSlopeSource.intercept_bound_of_compact_front_support
    ambient hcompact σ b u hslopes hatu
  exact front_frostman_of_shrinking_positive_bushes_of_bounded_intercept
    ambient hcompact σ hσ b hb hslopes u v huv hsupport B S hbound s c R hs hR p hp hmass

/-- Uniformly nonvanishing individual shrinking bushes force the original
compact physical front to have Hausdorff dimension four. -/
theorem front_dimH_eq_four_of_shrinking_positive_bushes
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v : ℝ) (huv : u < v)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (S : ℝ) (s : ℕ → ℝ) (c : ℕ → E3) (R : ℕ → ℝ)
    (hs : ∀ n, |s n| ≤ S) (hR : Tendsto R atTop (𝓝 0))
    (p : ℝ≥0∞) (hp : 0 < p)
    (hmass : ∀ n, p ≤ σ {a | ‖b a + s n • a - c n‖ ≤ R n}) :
    dimH (unitFront ambient) = 4 := by
  apply le_antisymm
  · calc
      dimH (unitFront ambient) ≤ dimH (univ : Set E4) := dimH_mono (subset_univ _)
      _ = 4 := by simp [E4, Real.dimH_univ_eq_finrank]
  · exact dimH_ge_four_of_front_frostman_measures ambient
      (front_frostman_of_shrinking_positive_bushes ambient hcompact σ hσ b hb hslopes
        u v huv hsupport S s c R hs hR p hp hmass)

end StickyKakeya4.PositiveBush
