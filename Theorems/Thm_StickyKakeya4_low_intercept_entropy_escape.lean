import Theorems.Thm_StickyKakeya4_vector_bush_frostman
import Theorems.Thm_StickyKakeya4_dimension_witness_extraction

/-!
# Escape from a low-entropy centered-intercept image

This is an auxiliary geometric theorem with a substantive extra hypothesis:
the centered intercept image of one fixed, full-source set has arbitrarily
small covering exponents. It does not claim this hypothesis follows from
packing dimension three, stickiness, or the source manuscript.

Finite covers of that image, bounded Lebesgue direction density, and a fixed
height gap give a cubic source-fibre estimate. The physical fourth coordinate
then contributes the remaining factor `2r`. The measure being estimated is
the actual source/time pushforward supported on the original compact front.
-/

open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

namespace StickyKakeya4.LowInterceptEntropyEscape

open OriginalResidualCriterion VectorBushFrostman

/-- The literal intercept image at the one fixed reference height. -/
def centeredInterceptImage (b : E3 → E3) (s₀ : ℝ) (A : Set E3) : Set E3 :=
  (fun a => b a + s₀ • a) '' A

/-- A genuine small-radius covering-number hypothesis on one fixed set.
The finite coefficient and positive cutoff may depend on the exponent. -/
def HasLowInterceptEntropy (b : E3 → E3) (s₀ : ℝ) (A : Set E3) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (C : ℝ≥0∞) (r₀ : ℝ), C ≠ ∞ ∧ 0 < r₀ ∧
    ∀ r : ℝ, 0 < r → r ≤ r₀ →
      coveringNumber (centeredInterceptImage b s₀ A) r ≤
        C * ENNReal.ofReal r ^ (-ε)

/-- A finite intercept cover forces every contributing slope into one of
its actual vector caps, all synchronized to the same physical point/time. -/
theorem fiber_mass_le_finite_cover
    (σ : Measure E3) (hσ : σ ≤ volume) (b : E3 → E3) (A : Set E3)
    (hA : ∀ᵐ a ∂σ, a ∈ A) (centers : Finset E3)
    (s₀ s t r g : ℝ) (y : E3) (hr : 0 < r) (hg : 0 < g)
    (hgap : g ≤ |s - s₀|)
    (hcover : coversAtRadius (centeredInterceptImage b s₀ A) r centers) :
    σ {a | slopeSpacetimePoint b (s, a) ∈ Metric.ball (spacetimeLift y t) r} ≤
      (centers.card : ℝ≥0∞) * ENNReal.ofReal (Real.pi * 4 / 3) *
        ENNReal.ofReal ((2 / g) * r) ^ (3 : ℕ) := by
  classical
  let caps : E3 → Set E3 := fun c =>
    Metric.closedBall (vectorCenter c y s₀ s) ((2 / g) * r)
  have hsub : ∀ᵐ a ∂σ,
      a ∈ {a | slopeSpacetimePoint b (s, a) ∈ Metric.ball (spacetimeLift y t) r} →
        a ∈ ⋃ c ∈ centers, caps c := by
    filter_upwards [hA] with a ha hball
    obtain ⟨c, hc⟩ := mem_iUnion.mp (hcover ⟨a, ha, rfl⟩)
    obtain ⟨hcfin, hac⟩ := mem_iUnion.mp hc
    have hbush : ‖b a + s₀ • a - c‖ ≤ r :=
      (show dist (b a + s₀ • a) c < r from hac).le
    have hdist : ‖spacetimeLift (b a + s • a) s - spacetimeLift y t‖ ≤ r :=
      (show dist (slopeSpacetimePoint b (s, a)) (spacetimeLift y t) < r from hball).le
    have hh := (spacetimeLift_collision_coordinates
      (b a + s • a) y s t r hr.le hdist).1
    have hcap := source_mem_vector_cap a (b a) c y s₀ s r r g hbush hh hg hgap
    have heq : (r + r) / g = (2 / g) * r := by ring
    rw [heq] at hcap
    exact mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨hcfin, hcap⟩⟩
  calc
    _ ≤ σ (⋃ c ∈ centers, caps c) := measure_mono_ae hsub
    _ ≤ ∑ c ∈ centers, σ (caps c) := measure_biUnion_finset_le _ _
    _ ≤ ∑ c ∈ centers, ENNReal.ofReal (Real.pi * 4 / 3) *
        ENNReal.ofReal ((2 / g) * r) ^ (3 : ℕ) := by
      apply Finset.sum_le_sum
      intro c hc
      exact (hσ (caps c)).trans_eq (by
        dsimp [caps]
        rw [EuclideanSpace.volume_closedBall_fin_three]
        ring)
    _ = _ := by simp [mul_assoc]

/-- Time integration supplies exactly the extra physical factor `2r`.
There is no assumed ball bound or paid geometric certificate here. -/
theorem physical_ball_mass_le_finite_cover
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (A : Set E3)
    (hA : ∀ᵐ a ∂σ, a ∈ A) (centers : Finset E3)
    (s₀ u v r g : ℝ) (y : E3) (t : ℝ) (hr : 0 < r) (hg : 0 < g)
    (hgap : ∀ s ∈ Icc u v, g ≤ |s - s₀|)
    (hcover : coversAtRadius (centeredInterceptImage b s₀ A) r centers) :
    sourceFrontMeasure σ b u v (Metric.ball (spacetimeLift y t) r) ≤
      ENNReal.ofReal (2 * r) * ((centers.card : ℝ≥0∞) *
        ENNReal.ofReal (Real.pi * 4 / 3) * ENNReal.ofReal ((2 / g) * r) ^ (3 : ℕ)) := by
  let B := (centers.card : ℝ≥0∞) * ENNReal.ofReal (Real.pi * 4 / 3) *
    ENNReal.ofReal ((2 / g) * r) ^ (3 : ℕ)
  have hF := measurable_slopeSpacetimePoint b hb
  have hrow (s : ℝ) (hs : s ∈ Icc u v) :
      σ {a | slopeSpacetimePoint b (s, a) ∈ Metric.ball (spacetimeLift y t) r} ≤
        (Icc (t - r) (t + r)).indicator (fun _ => B) s := by
    by_cases htime : s ∈ Icc (t - r) (t + r)
    · rw [Set.indicator_of_mem htime]
      exact fiber_mass_le_finite_cover σ hσ b A hA centers
        s₀ s t r g y hr hg (hgap s hs) hcover
    · rw [Set.indicator_of_notMem htime]
      have he : {a | slopeSpacetimePoint b (s, a) ∈ Metric.ball (spacetimeLift y t) r} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro a ha
        have hh : ‖spacetimeLift (b a + s • a) s - spacetimeLift y t‖ ≤ r :=
          (show dist (slopeSpacetimePoint b (s, a)) (spacetimeLift y t) < r from ha).le
        have ht := (spacetimeLift_collision_coordinates (b a + s • a) y s t r hr.le hh).2
        obtain ⟨hlo, hhi⟩ := abs_le.mp ht
        exact htime ⟨by linarith, by linarith⟩
      rw [he, measure_empty]
  change (((volume.restrict (Icc u v)).prod σ).map (slopeSpacetimePoint b)) _ ≤ _
  rw [Measure.map_apply hF Metric.isOpen_ball.measurableSet,
    Measure.prod_apply (Metric.isOpen_ball.measurableSet.preimage hF)]
  change (∫⁻ s in Icc u v, σ
    {a | slopeSpacetimePoint b (s, a) ∈ Metric.ball (spacetimeLift y t) r}) ≤ _
  calc
    _ ≤ ∫⁻ s in Icc u v, (Icc (t - r) (t + r)).indicator (fun _ => B) s := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact hrow s hs
    _ ≤ ∫⁻ s, (Icc (t - r) (t + r)).indicator (fun _ => B) s :=
      setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (2 * r) * B := by
      rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
      rw [show t + r - (t - r) = 2 * r by ring]
      exact mul_comm _ _

/-- The explicit geometric coefficient is `2 vol(B³(0,1)) (2/g)^3`. -/
def geometricConstant (g : ℝ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal (Real.pi * 4 / 3) * ENNReal.ofReal (2 / g) ^ (3 : ℕ)

theorem geometricConstant_ne_top (g : ℝ) : geometricConstant g ≠ ∞ := by
  unfold geometricConstant
  finiteness

/-- Cover cardinality times the fourth power, before using any entropy bound. -/
theorem physical_ball_mass_le_card_mul_fourth_power
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (A : Set E3)
    (hA : ∀ᵐ a ∂σ, a ∈ A) (centers : Finset E3)
    (s₀ u v r g : ℝ) (x : E4) (hr : 0 < r) (hg : 0 < g)
    (hgap : ∀ s ∈ Icc u v, g ≤ |s - s₀|)
    (hcover : coversAtRadius (centeredInterceptImage b s₀ A) r centers) :
    sourceFrontMeasure σ b u v (Metric.ball x r) ≤
      geometricConstant g * (centers.card : ℝ≥0∞) * ENNReal.ofReal r ^ (4 : ℝ) := by
  rw [← spacetimeLift_horizontalProjection x]
  apply (physical_ball_mass_le_finite_cover σ hσ b hb A hA centers
    s₀ u v r g (horizontalProjection x) (x (3 : Fin 4)) hr hg hgap hcover).trans_eq
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (div_nonneg (by norm_num) hg.le),
    ENNReal.rpow_ofNat]
  norm_num only [ENNReal.ofReal_ofNat]
  unfold geometricConstant
  ring

/-- A genuine covering-number estimate gives the desired sub-four physical
ball bound at every radius where the entropy estimate holds. The `+1` is the
explicit harmless loss when extracting a finite cover from its infimum. -/
theorem physical_ball_mass_le_of_coveringNumber
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (A : Set E3)
    (hA : ∀ᵐ a ∂σ, a ∈ A) (s₀ u v r g ε : ℝ) (x : E4)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (hr : 0 < r) (hr1 : r ≤ 1)
    (hg : 0 < g) (hε : 0 < ε)
    (hgap : ∀ s ∈ Icc u v, g ≤ |s - s₀|)
    (hentropy : coveringNumber (centeredInterceptImage b s₀ A) r ≤
      C * ENNReal.ofReal r ^ (-ε)) :
    sourceFrontMeasure σ b u v (Metric.ball x r) ≤
      (geometricConstant g * (C + 1)) * ENNReal.ofReal r ^ (4 - ε) := by
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrtop : ENNReal.ofReal r ^ (-ε) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hr0 ENNReal.ofReal_ne_top
  obtain ⟨centers, hcover, hcard⟩ := coveringNumber_le_extract_finset_cover
    (centeredInterceptImage b s₀ A) r (ENNReal.mul_ne_top hC hrtop) hentropy
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r ^ (-ε) :=
    ENNReal.one_le_rpow_of_pos_of_le_one_of_neg (ENNReal.ofReal_pos.mpr hr)
      (by simpa using ENNReal.ofReal_le_ofReal hr1) (neg_neg_of_pos hε)
  have hcard' : (centers.card : ℝ≥0∞) ≤ (C + 1) * ENNReal.ofReal r ^ (-ε) := by
    calc
      _ ≤ C * ENNReal.ofReal r ^ (-ε) + 1 := hcard.le
      _ ≤ C * ENNReal.ofReal r ^ (-ε) + ENNReal.ofReal r ^ (-ε) := add_le_add le_rfl hone
      _ = _ := by ring
  calc
    _ ≤ geometricConstant g * (centers.card : ℝ≥0∞) * ENNReal.ofReal r ^ (4 : ℝ) :=
      physical_ball_mass_le_card_mul_fourth_power σ hσ b hb A hA centers
        s₀ u v r g x hr hg hgap hcover
    _ ≤ geometricConstant g * ((C + 1) * ENNReal.ofReal r ^ (-ε)) *
        ENNReal.ofReal r ^ (4 : ℝ) := by gcongr
    _ = (geometricConstant g * (C + 1)) * ENNReal.ofReal r ^ (4 - ε) := by
      rw [show (4 - ε : ℝ) = -ε + 4 by ring,
        ENNReal.rpow_add (-ε) 4 hr0 ENNReal.ofReal_ne_top]
      ring

/-- The actual finite measure has global sub-four Frostman growth. The
small-radius threshold is retained in the large-radius coefficient, where
only total finite mass is used. -/
theorem sourceFrontMeasure_global_ball_bound
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (A : Set E3)
    (hA : ∀ᵐ a ∂σ, a ∈ A) (s₀ u v g ε : ℝ)
    (hg : 0 < g) (hε : 0 < ε) (hε4 : ε < 4)
    (hgap : ∀ s ∈ Icc u v, g ≤ |s - s₀|)
    (hentropy : HasLowInterceptEntropy b s₀ A) :
    ∃ D : ℝ≥0∞, D ≠ ∞ ∧ ∀ (x : E4) (r : ℝ), 0 < r →
      sourceFrontMeasure σ b u v (Metric.ball x r) ≤ D * ENNReal.ofReal r ^ (4 - ε) := by
  obtain ⟨C, r₀, hC, hr₀, hcover⟩ := hentropy ε hε
  let δ : ℝ := min r₀ 1
  have hδ : 0 < δ := lt_min hr₀ (by norm_num)
  have hδ0 : ENNReal.ofReal δ ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
  have hp : ENNReal.ofReal δ ^ (-(4 - ε)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hδ0 ENNReal.ofReal_ne_top
  let Dsmall : ℝ≥0∞ := geometricConstant g * (C + 1)
  let Dlarge : ℝ≥0∞ := sourceFrontMeasure σ b u v univ * ENNReal.ofReal δ ^ (-(4 - ε))
  have hDsmall : Dsmall ≠ ∞ := by
    dsimp [Dsmall]
    exact ENNReal.mul_ne_top (geometricConstant_ne_top g) (by finiteness)
  have hDlarge : Dlarge ≠ ∞ := by dsimp [Dlarge]; finiteness
  refine ⟨Dsmall + Dlarge, ENNReal.add_ne_top.mpr ⟨hDsmall, hDlarge⟩, ?_⟩
  intro x r hr
  by_cases hsmall : r ≤ δ
  · have hbound := physical_ball_mass_le_of_coveringNumber σ hσ b hb A hA
      s₀ u v r g ε x C hC hr (hsmall.trans (min_le_right _ _)) hg hε hgap
      (hcover r hr (hsmall.trans (min_le_left _ _)))
    apply hbound.trans
    change Dsmall * ENNReal.ofReal r ^ (4 - ε) ≤ _
    gcongr
    exact le_add_right le_rfl
  · have hδr : δ ≤ r := le_of_lt (lt_of_not_ge hsmall)
    have hpow : ENNReal.ofReal δ ^ (4 - ε) ≤ ENNReal.ofReal r ^ (4 - ε) :=
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hδr) (by linarith)
    have hcancel : ENNReal.ofReal δ ^ (-(4 - ε)) * ENNReal.ofReal δ ^ (4 - ε) = 1 := by
      rw [← ENNReal.rpow_add (-(4 - ε)) (4 - ε) hδ0 ENNReal.ofReal_ne_top]
      simp
    calc
      _ ≤ sourceFrontMeasure σ b u v univ := measure_mono (subset_univ _)
      _ = Dlarge * ENNReal.ofReal δ ^ (4 - ε) := by
        dsimp [Dlarge]
        rw [mul_assoc, hcancel, mul_one]
      _ ≤ Dlarge * ENNReal.ofReal r ^ (4 - ε) := mul_le_mul_right hpow _
      _ ≤ (Dsmall + Dlarge) * ENNReal.ofReal r ^ (4 - ε) := by
        gcongr
        exact le_add_left le_rfl

/-- Harmless scalar normalization of the actual pushforward; no restriction
or auxiliary replacement measure is made. -/
def frontProbability (σ : Measure E3) (b : E3 → E3) (u v : ℝ) : Measure E4 :=
  (sourceFrontMeasure σ b u v univ)⁻¹ • sourceFrontMeasure σ b u v

theorem sourceFrontMeasure_mass_ne_zero
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ)
    (b : E3 → E3) (hb : Measurable b) (u v : ℝ) (huv : u < v) :
    sourceFrontMeasure σ b u v univ ≠ 0 := by
  rw [sourceFrontMeasure_univ σ b hb]
  exact mul_ne_zero (ENNReal.ofReal_pos.mpr (sub_pos.mpr huv)).ne' hσpos.ne'

theorem frontProbability_isProbability
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ)
    (b : E3 → E3) (hb : Measurable b) (u v : ℝ) (huv : u < v) :
    IsProbabilityMeasure (frontProbability σ b u v) := by
  constructor
  rw [frontProbability, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (sourceFrontMeasure_mass_ne_zero σ hσpos b hb u v huv) (measure_ne_top _ _)

/-- Every sub-four exponent is a genuine global Frostman bound for the
same normalized actual source measure. -/
theorem frontProbability_global_ball_bound
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ) (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (A : Set E3)
    (hA : ∀ᵐ a ∂σ, a ∈ A) (s₀ u v g ε : ℝ) (huv : u < v)
    (hg : 0 < g) (hε : 0 < ε) (hε4 : ε < 4)
    (hgap : ∀ s ∈ Icc u v, g ≤ |s - s₀|)
    (hentropy : HasLowInterceptEntropy b s₀ A) :
    ∃ D : ℝ≥0∞, D ≠ ∞ ∧ ∀ (x : E4) (r : ℝ), 0 < r →
      frontProbability σ b u v (Metric.ball x r) ≤ D * ENNReal.ofReal r ^ (4 - ε) := by
  obtain ⟨D, hD, hbound⟩ := sourceFrontMeasure_global_ball_bound σ hσ b hb A hA
    s₀ u v g ε hg hε hε4 hgap hentropy
  have hm := sourceFrontMeasure_mass_ne_zero σ hσpos b hb u v huv
  refine ⟨(sourceFrontMeasure σ b u v univ)⁻¹ * D, ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hm) hD
  · intro x r hr
    rw [frontProbability, Measure.smul_apply, smul_eq_mul, mul_assoc]
    exact mul_le_mul_right (hbound x r hr) _

/-- Actual support is preserved by scalar normalization. -/
theorem frontProbability_supported
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3) (hb : Measurable b)
    (u v : ℝ) (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient) :
    frontProbability σ b u v (unitFront ambient)ᶜ = 0 := by
  rw [frontProbability, Measure.smul_apply, smul_eq_mul,
    sourceFrontMeasure_supported σ b hb u v (unitFront ambient)
      (StickyKakeya4.IsCompact.unitFront hcompact).measurableSet hsupport, mul_zero]

/-- Source-faithful low-intercept-entropy escape: covering numbers produce
supported Frostman probabilities on the literal original front. The fixed
full-source set is explicit, and the entropy premise is not derived here. -/
theorem front_frostman_of_low_intercept_entropy
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ) (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (A : Set E3) (_hAmeas : MeasurableSet A)
    (hA : ∀ᵐ a ∂σ, a ∈ A) (s₀ u v g : ℝ) (huv : u < v) (hg : 0 < g)
    (hgap : ∀ s ∈ Icc u v, g ≤ |s - s₀|)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hentropy : HasLowInterceptEntropy b s₀ A) :
    HasFrontFrostmanMeasures ambient := by
  intro ε hε hε4
  obtain ⟨D, hD, hball⟩ := frontProbability_global_ball_bound σ hσpos hσ b hb A hA
    s₀ u v g ε huv hg hε hε4 hgap hentropy
  exact ⟨frontProbability σ b u v, frontProbability_isProbability σ hσpos b hb u v huv,
    frontProbability_supported ambient hcompact σ b hb u v hsupport,
    D, hD, fun x r hr _ => hball x r hr⟩

/-- The original front has Hausdorff dimension four under the explicitly
additional low-centered-intercept-entropy premise at one separated height. -/
theorem front_dimH_eq_four_of_low_intercept_entropy
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ) (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (A : Set E3) (hAmeas : MeasurableSet A)
    (hA : ∀ᵐ a ∂σ, a ∈ A) (s₀ u v g : ℝ) (huv : u < v) (hg : 0 < g)
    (hgap : ∀ s ∈ Icc u v, g ≤ |s - s₀|)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hentropy : HasLowInterceptEntropy b s₀ A) :
    dimH (unitFront ambient) = 4 := by
  apply le_antisymm
  · calc
      dimH (unitFront ambient) ≤ dimH (Set.univ : Set E4) := dimH_mono (subset_univ _)
      _ = 4 := by simp [E4, Real.dimH_univ_eq_finrank]
  · exact dimH_ge_four_of_front_frostman_measures ambient
      (front_frostman_of_low_intercept_entropy ambient hcompact σ hσpos hσ b hb A hAmeas hA
        s₀ u v g huv hg hgap hsupport hentropy)

end StickyKakeya4.LowInterceptEntropyEscape
